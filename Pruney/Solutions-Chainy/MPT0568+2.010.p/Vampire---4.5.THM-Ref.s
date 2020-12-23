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
% DateTime   : Thu Dec  3 12:50:11 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 140 expanded)
%              Number of leaves         :   31 (  67 expanded)
%              Depth                    :    6
%              Number of atoms          :  247 ( 341 expanded)
%              Number of equality atoms :   40 (  56 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f168,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f59,f63,f67,f71,f79,f87,f91,f95,f101,f107,f113,f120,f134,f144,f149,f154,f165])).

fof(f165,plain,
    ( spl3_1
    | ~ spl3_24 ),
    inference(avatar_contradiction_clause,[],[f164])).

fof(f164,plain,
    ( $false
    | spl3_1
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f162])).

fof(f162,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl3_1
    | ~ spl3_24 ),
    inference(superposition,[],[f43,f153])).

fof(f153,plain,
    ( ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_24
  <=> ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f43,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl3_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f154,plain,
    ( spl3_24
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f150,f147,f142,f152])).

fof(f142,plain,
    ( spl3_22
  <=> ! [X2] : k10_relat_1(k1_xboole_0,X2) = k3_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f147,plain,
    ( spl3_23
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f150,plain,
    ( ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f143,f148])).

fof(f148,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f147])).

fof(f143,plain,
    ( ! [X2] : k10_relat_1(k1_xboole_0,X2) = k3_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f149,plain,
    ( spl3_23
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f145,f118,f61,f147])).

fof(f61,plain,
    ( spl3_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f118,plain,
    ( spl3_17
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f145,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_17 ),
    inference(resolution,[],[f119,f62])).

fof(f62,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f119,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k3_xboole_0(X0,X1) )
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f118])).

fof(f144,plain,
    ( spl3_22
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f136,f132,f89,f142])).

fof(f89,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f132,plain,
    ( spl3_20
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f136,plain,
    ( ! [X2] : k10_relat_1(k1_xboole_0,X2) = k3_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)
    | ~ spl3_12
    | ~ spl3_20 ),
    inference(resolution,[],[f90,f133])).

fof(f133,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f132])).

fof(f90,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f134,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f130,f98,f85,f56,f132])).

fof(f56,plain,
    ( spl3_4
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f85,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f98,plain,
    ( spl3_14
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f130,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f129,f100])).

fof(f100,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f98])).

fof(f129,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(superposition,[],[f86,f58])).

fof(f58,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f86,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f120,plain,
    ( spl3_17
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f114,f111,f105,f118])).

fof(f105,plain,
    ( spl3_15
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f111,plain,
    ( spl3_16
  <=> ! [X1,X0] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f114,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | k1_xboole_0 = k3_xboole_0(X0,X1) )
    | ~ spl3_15
    | ~ spl3_16 ),
    inference(resolution,[],[f112,f106])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f105])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f111])).

fof(f113,plain,
    ( spl3_16
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f109,f77,f69,f111])).

fof(f69,plain,
    ( spl3_7
  <=> ! [X0] :
        ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f77,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | v1_xboole_0(k3_xboole_0(X0,X1)) )
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(resolution,[],[f78,f70])).

fof(f70,plain,
    ( ! [X0] :
        ( r2_hidden(sK1(X0),X0)
        | v1_xboole_0(X0) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f107,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f103,f93,f46,f105])).

fof(f46,plain,
    ( spl3_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f93,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f103,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v1_xboole_0(X0) )
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(resolution,[],[f94,f48])).

fof(f48,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f94,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | X0 = X1
        | ~ v1_xboole_0(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f93])).

fof(f101,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f96,f65,f46,f98])).

fof(f65,plain,
    ( spl3_6
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f96,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl3_2
    | ~ spl3_6 ),
    inference(resolution,[],[f66,f48])).

fof(f66,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f65])).

fof(f95,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f39,f93])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

fof(f91,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f38,f89])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f87,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f37,f85])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

fof(f79,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f25])).

fof(f25,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f71,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK1(X0),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f67,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f32,f65])).

fof(f32,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f63,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f29,f56])).

fof(f29,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f49,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f28,f46])).

fof(f28,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f44,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f27,f41])).

fof(f27,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).

fof(f19,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:48:11 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (6810)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.21/0.42  % (6810)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f168,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f44,f49,f59,f63,f67,f71,f79,f87,f91,f95,f101,f107,f113,f120,f134,f144,f149,f154,f165])).
% 0.21/0.42  fof(f165,plain,(
% 0.21/0.42    spl3_1 | ~spl3_24),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f164])).
% 0.21/0.42  fof(f164,plain,(
% 0.21/0.42    $false | (spl3_1 | ~spl3_24)),
% 0.21/0.42    inference(trivial_inequality_removal,[],[f162])).
% 0.21/0.42  fof(f162,plain,(
% 0.21/0.42    k1_xboole_0 != k1_xboole_0 | (spl3_1 | ~spl3_24)),
% 0.21/0.42    inference(superposition,[],[f43,f153])).
% 0.21/0.42  fof(f153,plain,(
% 0.21/0.42    ( ! [X2] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)) ) | ~spl3_24),
% 0.21/0.42    inference(avatar_component_clause,[],[f152])).
% 0.21/0.42  fof(f152,plain,(
% 0.21/0.42    spl3_24 <=> ! [X2] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl3_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f41])).
% 0.21/0.42  fof(f41,plain,(
% 0.21/0.42    spl3_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.42  fof(f154,plain,(
% 0.21/0.42    spl3_24 | ~spl3_22 | ~spl3_23),
% 0.21/0.42    inference(avatar_split_clause,[],[f150,f147,f142,f152])).
% 0.21/0.42  fof(f142,plain,(
% 0.21/0.42    spl3_22 <=> ! [X2] : k10_relat_1(k1_xboole_0,X2) = k3_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.42  fof(f147,plain,(
% 0.21/0.42    spl3_23 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.42  fof(f150,plain,(
% 0.21/0.42    ( ! [X2] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X2)) ) | (~spl3_22 | ~spl3_23)),
% 0.21/0.42    inference(backward_demodulation,[],[f143,f148])).
% 0.21/0.42  fof(f148,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl3_23),
% 0.21/0.42    inference(avatar_component_clause,[],[f147])).
% 0.21/0.42  fof(f143,plain,(
% 0.21/0.42    ( ! [X2] : (k10_relat_1(k1_xboole_0,X2) = k3_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)) ) | ~spl3_22),
% 0.21/0.42    inference(avatar_component_clause,[],[f142])).
% 0.21/0.42  fof(f149,plain,(
% 0.21/0.42    spl3_23 | ~spl3_5 | ~spl3_17),
% 0.21/0.42    inference(avatar_split_clause,[],[f145,f118,f61,f147])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    spl3_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.42  fof(f118,plain,(
% 0.21/0.42    spl3_17 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.42  fof(f145,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | (~spl3_5 | ~spl3_17)),
% 0.21/0.42    inference(resolution,[],[f119,f62])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f61])).
% 0.21/0.42  fof(f119,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1)) ) | ~spl3_17),
% 0.21/0.42    inference(avatar_component_clause,[],[f118])).
% 0.21/0.42  fof(f144,plain,(
% 0.21/0.42    spl3_22 | ~spl3_12 | ~spl3_20),
% 0.21/0.42    inference(avatar_split_clause,[],[f136,f132,f89,f142])).
% 0.21/0.42  fof(f89,plain,(
% 0.21/0.42    spl3_12 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.42  fof(f132,plain,(
% 0.21/0.42    spl3_20 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.42  fof(f136,plain,(
% 0.21/0.42    ( ! [X2] : (k10_relat_1(k1_xboole_0,X2) = k3_xboole_0(k10_relat_1(k1_xboole_0,X2),k1_xboole_0)) ) | (~spl3_12 | ~spl3_20)),
% 0.21/0.42    inference(resolution,[],[f90,f133])).
% 0.21/0.42  fof(f133,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl3_20),
% 0.21/0.42    inference(avatar_component_clause,[],[f132])).
% 0.21/0.42  fof(f90,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl3_12),
% 0.21/0.42    inference(avatar_component_clause,[],[f89])).
% 0.21/0.42  fof(f134,plain,(
% 0.21/0.42    spl3_20 | ~spl3_4 | ~spl3_11 | ~spl3_14),
% 0.21/0.42    inference(avatar_split_clause,[],[f130,f98,f85,f56,f132])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl3_4 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    spl3_11 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.42  fof(f98,plain,(
% 0.21/0.42    spl3_14 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.42  fof(f130,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl3_4 | ~spl3_11 | ~spl3_14)),
% 0.21/0.42    inference(subsumption_resolution,[],[f129,f100])).
% 0.21/0.42  fof(f100,plain,(
% 0.21/0.42    v1_relat_1(k1_xboole_0) | ~spl3_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f98])).
% 0.21/0.42  fof(f129,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl3_4 | ~spl3_11)),
% 0.21/0.42    inference(superposition,[],[f86,f58])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_4),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl3_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f85])).
% 0.21/0.42  fof(f120,plain,(
% 0.21/0.42    spl3_17 | ~spl3_15 | ~spl3_16),
% 0.21/0.42    inference(avatar_split_clause,[],[f114,f111,f105,f118])).
% 0.21/0.42  fof(f105,plain,(
% 0.21/0.42    spl3_15 <=> ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.42  fof(f111,plain,(
% 0.21/0.42    spl3_16 <=> ! [X1,X0] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.42  fof(f114,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1)) ) | (~spl3_15 | ~spl3_16)),
% 0.21/0.42    inference(resolution,[],[f112,f106])).
% 0.21/0.42  fof(f106,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_15),
% 0.21/0.42    inference(avatar_component_clause,[],[f105])).
% 0.21/0.42  fof(f112,plain,(
% 0.21/0.42    ( ! [X0,X1] : (v1_xboole_0(k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_16),
% 0.21/0.42    inference(avatar_component_clause,[],[f111])).
% 0.21/0.42  fof(f113,plain,(
% 0.21/0.42    spl3_16 | ~spl3_7 | ~spl3_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f109,f77,f69,f111])).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl3_7 <=> ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    spl3_9 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.42  fof(f109,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | v1_xboole_0(k3_xboole_0(X0,X1))) ) | (~spl3_7 | ~spl3_9)),
% 0.21/0.42    inference(resolution,[],[f78,f70])).
% 0.21/0.42  fof(f70,plain,(
% 0.21/0.42    ( ! [X0] : (r2_hidden(sK1(X0),X0) | v1_xboole_0(X0)) ) | ~spl3_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f69])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f77])).
% 0.21/0.42  fof(f107,plain,(
% 0.21/0.42    spl3_15 | ~spl3_2 | ~spl3_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f103,f93,f46,f105])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl3_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.42  fof(f93,plain,(
% 0.21/0.42    spl3_13 <=> ! [X1,X0] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) ) | (~spl3_2 | ~spl3_13)),
% 0.21/0.42    inference(resolution,[],[f94,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0) | ~spl3_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f94,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) ) | ~spl3_13),
% 0.21/0.42    inference(avatar_component_clause,[],[f93])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    spl3_14 | ~spl3_2 | ~spl3_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f96,f65,f46,f98])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    spl3_6 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.42  fof(f96,plain,(
% 0.21/0.42    v1_relat_1(k1_xboole_0) | (~spl3_2 | ~spl3_6)),
% 0.21/0.42    inference(resolution,[],[f66,f48])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) ) | ~spl3_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f65])).
% 0.21/0.42  fof(f95,plain,(
% 0.21/0.42    spl3_13),
% 0.21/0.42    inference(avatar_split_clause,[],[f39,f93])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f18])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).
% 0.21/0.42  fof(f91,plain,(
% 0.21/0.42    spl3_12),
% 0.21/0.42    inference(avatar_split_clause,[],[f38,f89])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f17])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.42  fof(f87,plain,(
% 0.21/0.42    spl3_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f37,f85])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f16])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.42  fof(f79,plain,(
% 0.21/0.42    spl3_9),
% 0.21/0.42    inference(avatar_split_clause,[],[f36,f77])).
% 0.21/0.42  fof(f36,plain,(
% 0.21/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f26])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(ennf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    inference(rectify,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.42  fof(f71,plain,(
% 0.21/0.42    spl3_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f34,f69])).
% 0.21/0.42  fof(f34,plain,(
% 0.21/0.42    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f24])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f22,f23])).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(rectify,[],[f21])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.21/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.42  fof(f67,plain,(
% 0.21/0.42    spl3_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f32,f65])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl3_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f31,f61])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.42  fof(f59,plain,(
% 0.21/0.42    spl3_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f29,f56])).
% 0.21/0.42  fof(f29,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,axiom,(
% 0.21/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl3_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f28,f46])).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    v1_xboole_0(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    ~spl3_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f27,f41])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f20])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f13,f19])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,negated_conjecture,(
% 0.21/0.42    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f10])).
% 0.21/0.42  fof(f10,conjecture,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (6810)------------------------------
% 0.21/0.42  % (6810)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (6810)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (6810)Memory used [KB]: 6140
% 0.21/0.42  % (6810)Time elapsed: 0.006 s
% 0.21/0.42  % (6810)------------------------------
% 0.21/0.42  % (6810)------------------------------
% 0.21/0.42  % (6800)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.21/0.42  % (6799)Success in time 0.066 s
%------------------------------------------------------------------------------
