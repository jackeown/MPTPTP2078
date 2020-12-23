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
% DateTime   : Thu Dec  3 12:49:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 180 expanded)
%              Number of leaves         :   23 (  58 expanded)
%              Depth                    :   13
%              Number of atoms          :  230 ( 529 expanded)
%              Number of equality atoms :   68 ( 178 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f56,f66,f70,f89,f102,f104,f112,f126,f129,f189,f191])).

fof(f191,plain,
    ( ~ spl2_5
    | spl2_13 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl2_5
    | spl2_13 ),
    inference(resolution,[],[f188,f88])).

fof(f88,plain,
    ( ! [X0] : r1_xboole_0(k1_xboole_0,X0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl2_5
  <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f188,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl2_13
  <=> r1_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f189,plain,
    ( spl2_2
    | ~ spl2_13
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f184,f123,f186,f52])).

fof(f52,plain,
    ( spl2_2
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f123,plain,
    ( spl2_9
  <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f184,plain,
    ( ~ r1_xboole_0(k1_xboole_0,sK0)
    | r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_9 ),
    inference(superposition,[],[f167,f125])).

fof(f125,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f123])).

fof(f167,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0)
      | r1_xboole_0(k1_relat_1(sK1),X0) ) ),
    inference(superposition,[],[f46,f149])).

fof(f149,plain,(
    ! [X8] : k1_relat_1(k7_relat_1(sK1,X8)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X8)) ),
    inference(resolution,[],[f45,f28])).

fof(f28,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k9_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k9_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).

fof(f24,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k9_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k9_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k9_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k9_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k9_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k9_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k9_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k9_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k9_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(definition_unfolding,[],[f41,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f44,f37])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k3_xboole_0(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_xboole_0(k3_xboole_0(X0,X1),X1)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

fof(f129,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f128])).

fof(f128,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f127,f28])).

fof(f127,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_8 ),
    inference(resolution,[],[f121,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

fof(f121,plain,
    ( ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f119])).

% (5679)Refutation not found, incomplete strategy% (5679)------------------------------
% (5679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (5679)Termination reason: Refutation not found, incomplete strategy

% (5679)Memory used [KB]: 10618
% (5679)Time elapsed: 0.078 s
% (5679)------------------------------
% (5679)------------------------------
fof(f119,plain,
    ( spl2_8
  <=> v1_relat_1(k7_relat_1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f126,plain,
    ( ~ spl2_8
    | spl2_9
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f116,f48,f123,f119])).

fof(f48,plain,
    ( spl2_1
  <=> k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f116,plain,
    ( k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f115])).

fof(f115,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))
    | ~ v1_relat_1(k7_relat_1(sK1,sK0))
    | ~ spl2_1 ),
    inference(superposition,[],[f81,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f81,plain,(
    ! [X0] :
      ( k1_xboole_0 != k9_relat_1(sK1,X0)
      | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0))
      | ~ v1_relat_1(k7_relat_1(sK1,X0)) ) ),
    inference(superposition,[],[f35,f78])).

fof(f78,plain,(
    ! [X7] : k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7) ),
    inference(resolution,[],[f40,f28])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 != k2_relat_1(X0)
      | k1_xboole_0 = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

fof(f112,plain,
    ( spl2_1
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | spl2_1
    | ~ spl2_7 ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl2_1
    | ~ spl2_7 ),
    inference(superposition,[],[f49,f107])).

fof(f107,plain,
    ( k1_xboole_0 = k9_relat_1(sK1,sK0)
    | ~ spl2_7 ),
    inference(forward_demodulation,[],[f105,f32])).

fof(f32,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f105,plain,
    ( k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0)
    | ~ spl2_7 ),
    inference(superposition,[],[f78,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl2_7
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f49,plain,
    ( k1_xboole_0 != k9_relat_1(sK1,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f48])).

fof(f104,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f103])).

fof(f103,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f97,f28])).

fof(f97,plain,
    ( ~ v1_relat_1(sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl2_6
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f102,plain,
    ( ~ spl2_6
    | spl2_7
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f90,f52,f99,f95])).

fof(f90,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f43,f54])).

fof(f54,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f52])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 = k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( ( k1_xboole_0 = k7_relat_1(X1,X0)
          | ~ r1_xboole_0(k1_relat_1(X1),X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f89,plain,
    ( ~ spl2_4
    | spl2_5 ),
    inference(avatar_split_clause,[],[f85,f87,f63])).

fof(f63,plain,
    ( spl2_4
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f85,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(trivial_inequality_removal,[],[f84])).

fof(f84,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_xboole_0(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f83,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

fof(f83,plain,(
    ! [X0] :
      ( r1_xboole_0(k1_xboole_0,X0)
      | k1_xboole_0 != k7_relat_1(k1_xboole_0,X0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[],[f42,f31])).

fof(f31,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_relat_1(X1),X0)
      | k1_xboole_0 != k7_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f70,plain,(
    ~ spl2_3 ),
    inference(avatar_contradiction_clause,[],[f67])).

fof(f67,plain,
    ( $false
    | ~ spl2_3 ),
    inference(resolution,[],[f61,f28])).

fof(f61,plain,
    ( ! [X0] : ~ v1_relat_1(X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_3
  <=> ! [X0] : ~ v1_relat_1(X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f66,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f58,f63,f60])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f38,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k4_xboole_0(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_xboole_0(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).

fof(f56,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f30,f52,f48])).

fof(f30,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f55,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f29,f52,f48])).

fof(f29,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k9_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:53:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (5674)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (5673)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (5671)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (5670)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (5676)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (5682)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (5681)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (5679)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (5672)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (5684)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (5678)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (5680)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (5670)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f192,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f55,f56,f66,f70,f89,f102,f104,f112,f126,f129,f189,f191])).
% 0.21/0.50  fof(f191,plain,(
% 0.21/0.50    ~spl2_5 | spl2_13),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f190])).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    $false | (~spl2_5 | spl2_13)),
% 0.21/0.50    inference(resolution,[],[f188,f88])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) ) | ~spl2_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f87])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl2_5 <=> ! [X0] : r1_xboole_0(k1_xboole_0,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_xboole_0,sK0) | spl2_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f186])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    spl2_13 <=> r1_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    spl2_2 | ~spl2_13 | ~spl2_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f184,f123,f186,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl2_2 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl2_9 <=> k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    ~r1_xboole_0(k1_xboole_0,sK0) | r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_9),
% 0.21/0.50    inference(superposition,[],[f167,f125])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f123])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ( ! [X0] : (~r1_xboole_0(k1_relat_1(k7_relat_1(sK1,X0)),X0) | r1_xboole_0(k1_relat_1(sK1),X0)) )),
% 0.21/0.50    inference(superposition,[],[f46,f149])).
% 0.21/0.50  fof(f149,plain,(
% 0.21/0.50    ( ! [X8] : (k1_relat_1(k7_relat_1(sK1,X8)) = k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),X8))) )),
% 0.21/0.50    inference(resolution,[],[f45,f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    v1_relat_1(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k9_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k9_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ? [X0,X1] : ((k1_xboole_0 = k9_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.50    inference(negated_conjecture,[],[f12])).
% 0.21/0.50  fof(f12,conjecture,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k9_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_relat_1(X1) | k1_relat_1(k7_relat_1(X1,X0)) = k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )),
% 0.21/0.50    inference(definition_unfolding,[],[f41,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0,X1] : (k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X1) => k1_relat_1(k7_relat_1(X1,X0)) = k3_xboole_0(k1_relat_1(X1),X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(definition_unfolding,[],[f44,f37])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0,X1] : (~r1_xboole_0(k3_xboole_0(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : ~(r1_xboole_0(k3_xboole_0(X0,X1),X1) & ~r1_xboole_0(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    spl2_8),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f128])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    $false | spl2_8),
% 0.21/0.50    inference(resolution,[],[f127,f28])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    ~v1_relat_1(sK1) | spl2_8),
% 0.21/0.50    inference(resolution,[],[f121,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ~v1_relat_1(k7_relat_1(sK1,sK0)) | spl2_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.51  % (5679)Refutation not found, incomplete strategy% (5679)------------------------------
% 0.21/0.51  % (5679)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5679)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5679)Memory used [KB]: 10618
% 0.21/0.51  % (5679)Time elapsed: 0.078 s
% 0.21/0.51  % (5679)------------------------------
% 0.21/0.51  % (5679)------------------------------
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    spl2_8 <=> v1_relat_1(k7_relat_1(sK1,sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    ~spl2_8 | spl2_9 | ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f116,f48,f123,f119])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    spl2_1 <=> k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_1),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f115])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,sK0)) | ~v1_relat_1(k7_relat_1(sK1,sK0)) | ~spl2_1),
% 0.21/0.51    inference(superposition,[],[f81,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f48])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k9_relat_1(sK1,X0) | k1_xboole_0 = k1_relat_1(k7_relat_1(sK1,X0)) | ~v1_relat_1(k7_relat_1(sK1,X0))) )),
% 0.21/0.51    inference(superposition,[],[f35,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X7] : (k2_relat_1(k7_relat_1(sK1,X7)) = k9_relat_1(sK1,X7)) )),
% 0.21/0.51    inference(resolution,[],[f40,f28])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(nnf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    spl2_1 | ~spl2_7),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    $false | (spl2_1 | ~spl2_7)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | (spl2_1 | ~spl2_7)),
% 0.21/0.51    inference(superposition,[],[f49,f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    k1_xboole_0 = k9_relat_1(sK1,sK0) | ~spl2_7),
% 0.21/0.51    inference(forward_demodulation,[],[f105,f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.51  fof(f105,plain,(
% 0.21/0.51    k2_relat_1(k1_xboole_0) = k9_relat_1(sK1,sK0) | ~spl2_7),
% 0.21/0.51    inference(superposition,[],[f78,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl2_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f99])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    spl2_7 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    k1_xboole_0 != k9_relat_1(sK1,sK0) | spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f48])).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    spl2_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f103])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    $false | spl2_6),
% 0.21/0.51    inference(resolution,[],[f97,f28])).
% 0.21/0.51  fof(f97,plain,(
% 0.21/0.51    ~v1_relat_1(sK1) | spl2_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    spl2_6 <=> v1_relat_1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ~spl2_6 | spl2_7 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f90,f52,f99,f95])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~v1_relat_1(sK1) | ~spl2_2),
% 0.21/0.51    inference(resolution,[],[f43,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f52])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1] : (((k1_xboole_0 = k7_relat_1(X1,X0) | ~r1_xboole_0(k1_relat_1(X1),X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ~spl2_4 | spl2_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f85,f87,f63])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    spl2_4 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f83,f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0) | k1_xboole_0 != k7_relat_1(k1_xboole_0,X0) | ~v1_relat_1(k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f42,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ~spl2_3),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f67])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    $false | ~spl2_3),
% 0.21/0.51    inference(resolution,[],[f61,f28])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(X0)) ) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    spl2_3 <=> ! [X0] : ~v1_relat_1(X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    spl2_3 | spl2_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f58,f63,f60])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(superposition,[],[f38,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ( ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(k4_xboole_0(X0,X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k4_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_relat_1)).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    ~spl2_1 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f30,f52,f48])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k9_relat_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl2_1 | spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f52,f48])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k9_relat_1(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5670)------------------------------
% 0.21/0.51  % (5670)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5670)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5670)Memory used [KB]: 6140
% 0.21/0.51  % (5670)Time elapsed: 0.066 s
% 0.21/0.51  % (5670)------------------------------
% 0.21/0.51  % (5670)------------------------------
% 0.21/0.52  % (5667)Success in time 0.145 s
%------------------------------------------------------------------------------
