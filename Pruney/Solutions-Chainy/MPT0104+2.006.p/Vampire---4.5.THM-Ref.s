%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 148 expanded)
%              Number of leaves         :   26 (  66 expanded)
%              Depth                    :    9
%              Number of atoms          :  204 ( 334 expanded)
%              Number of equality atoms :   41 (  69 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f343,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f42,f46,f50,f55,f60,f64,f72,f80,f110,f142,f174,f209,f227,f309,f313,f339])).

fof(f339,plain,
    ( spl3_6
    | ~ spl3_27
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(avatar_contradiction_clause,[],[f338])).

fof(f338,plain,
    ( $false
    | spl3_6
    | ~ spl3_27
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(subsumption_resolution,[],[f337,f59])).

fof(f59,plain,
    ( ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_6
  <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f337,plain,
    ( r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2)
    | ~ spl3_27
    | ~ spl3_33
    | ~ spl3_34 ),
    inference(forward_demodulation,[],[f329,f308])).

fof(f308,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl3_33
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f329,plain,
    ( r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)
    | ~ spl3_27
    | ~ spl3_34 ),
    inference(superposition,[],[f312,f208])).

fof(f208,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl3_27
  <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f312,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK2,X0))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f311])).

fof(f311,plain,
    ( spl3_34
  <=> ! [X0] : r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK2,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f313,plain,
    ( spl3_34
    | ~ spl3_1
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f228,f225,f34,f311])).

fof(f34,plain,
    ( spl3_1
  <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f225,plain,
    ( spl3_29
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f228,plain,
    ( ! [X0] : r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK2,X0))
    | ~ spl3_1
    | ~ spl3_29 ),
    inference(resolution,[],[f226,f36])).

fof(f36,plain,
    ( r1_tarski(k4_xboole_0(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f226,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f225])).

fof(f309,plain,(
    spl3_33 ),
    inference(avatar_split_clause,[],[f31,f307])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f25,f24])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f227,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f29,f225])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

fof(f209,plain,
    ( spl3_27
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f188,f172,f139,f108,f78,f206])).

fof(f78,plain,
    ( spl3_10
  <=> ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f108,plain,
    ( spl3_15
  <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f139,plain,
    ( spl3_20
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f172,plain,
    ( spl3_23
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f188,plain,
    ( sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f182,f186])).

fof(f186,plain,
    ( ! [X1] : k2_xboole_0(X1,k1_xboole_0) = X1
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f180,f79])).

fof(f79,plain,
    ( ! [X2] : k2_xboole_0(X2,X2) = X2
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f180,plain,
    ( ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)
    | ~ spl3_15
    | ~ spl3_23 ),
    inference(superposition,[],[f173,f109])).

fof(f109,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f108])).

fof(f173,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f172])).

fof(f182,plain,
    ( k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))
    | ~ spl3_20
    | ~ spl3_23 ),
    inference(superposition,[],[f173,f141])).

fof(f141,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f139])).

fof(f174,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f23,f172])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f142,plain,
    ( spl3_20
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f103,f70,f39,f139])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f103,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(resolution,[],[f71,f41])).

fof(f41,plain,
    ( r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f110,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f105,f70,f53,f108])).

fof(f53,plain,
    ( spl3_5
  <=> ! [X0] : r1_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f105,plain,
    ( ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(resolution,[],[f71,f54])).

fof(f54,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f53])).

fof(f80,plain,
    ( spl3_10
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f76,f62,f53,f78])).

fof(f62,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k2_xboole_0(X0,X1) = X1
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( ! [X2] : k2_xboole_0(X2,X2) = X2
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(resolution,[],[f63,f54])).

fof(f63,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k2_xboole_0(X0,X1) = X1 )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f62])).

fof(f72,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f28,f70])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f64,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f60,plain,(
    ~ spl3_6 ),
    inference(avatar_split_clause,[],[f32,f57])).

fof(f32,plain,(
    ~ r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2) ),
    inference(backward_demodulation,[],[f30,f31])).

fof(f30,plain,(
    ~ r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) ),
    inference(definition_unfolding,[],[f20,f24])).

fof(f20,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
    & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
        & r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(k5_xboole_0(sK0,sK1),sK2)
      & r1_tarski(k4_xboole_0(sK1,sK0),sK2)
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X1),X2)
      & r1_tarski(k4_xboole_0(X1,X0),X2)
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
          & r1_tarski(k4_xboole_0(X0,X1),X2) )
       => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).

fof(f55,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f51,f48,f44,f53])).

fof(f44,plain,
    ( spl3_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f48,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f51,plain,
    ( ! [X0] : r1_tarski(X0,X0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f49,f45])).

fof(f45,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f49,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f50,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f22,f48])).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f46,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f42,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f19,f39])).

fof(f19,plain,(
    r1_tarski(k4_xboole_0(sK1,sK0),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f34])).

fof(f18,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:02:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (4816)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.45  % (4824)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (4816)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f343,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f37,f42,f46,f50,f55,f60,f64,f72,f80,f110,f142,f174,f209,f227,f309,f313,f339])).
% 0.22/0.47  fof(f339,plain,(
% 0.22/0.47    spl3_6 | ~spl3_27 | ~spl3_33 | ~spl3_34),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f338])).
% 0.22/0.47  fof(f338,plain,(
% 0.22/0.47    $false | (spl3_6 | ~spl3_27 | ~spl3_33 | ~spl3_34)),
% 0.22/0.47    inference(subsumption_resolution,[],[f337,f59])).
% 0.22/0.47  fof(f59,plain,(
% 0.22/0.47    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2) | spl3_6),
% 0.22/0.47    inference(avatar_component_clause,[],[f57])).
% 0.22/0.47  fof(f57,plain,(
% 0.22/0.47    spl3_6 <=> r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.47  fof(f337,plain,(
% 0.22/0.47    r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2) | (~spl3_27 | ~spl3_33 | ~spl3_34)),
% 0.22/0.47    inference(forward_demodulation,[],[f329,f308])).
% 0.22/0.47  fof(f308,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl3_33),
% 0.22/0.47    inference(avatar_component_clause,[],[f307])).
% 0.22/0.47  fof(f307,plain,(
% 0.22/0.47    spl3_33 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.22/0.47  fof(f329,plain,(
% 0.22/0.47    r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2) | (~spl3_27 | ~spl3_34)),
% 0.22/0.47    inference(superposition,[],[f312,f208])).
% 0.22/0.47  fof(f208,plain,(
% 0.22/0.47    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) | ~spl3_27),
% 0.22/0.47    inference(avatar_component_clause,[],[f206])).
% 0.22/0.47  fof(f206,plain,(
% 0.22/0.47    spl3_27 <=> sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.22/0.47  fof(f312,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK2,X0))) ) | ~spl3_34),
% 0.22/0.47    inference(avatar_component_clause,[],[f311])).
% 0.22/0.47  fof(f311,plain,(
% 0.22/0.47    spl3_34 <=> ! [X0] : r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK2,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.22/0.47  fof(f313,plain,(
% 0.22/0.47    spl3_34 | ~spl3_1 | ~spl3_29),
% 0.22/0.47    inference(avatar_split_clause,[],[f228,f225,f34,f311])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl3_1 <=> r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.47  fof(f225,plain,(
% 0.22/0.47    spl3_29 <=> ! [X1,X0,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.22/0.47  fof(f228,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),X0),k2_xboole_0(sK2,X0))) ) | (~spl3_1 | ~spl3_29)),
% 0.22/0.47    inference(resolution,[],[f226,f36])).
% 0.22/0.47  fof(f36,plain,(
% 0.22/0.47    r1_tarski(k4_xboole_0(sK0,sK1),sK2) | ~spl3_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f34])).
% 0.22/0.47  fof(f226,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2))) ) | ~spl3_29),
% 0.22/0.47    inference(avatar_component_clause,[],[f225])).
% 0.22/0.47  fof(f309,plain,(
% 0.22/0.47    spl3_33),
% 0.22/0.47    inference(avatar_split_clause,[],[f31,f307])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(definition_unfolding,[],[f25,f24])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.22/0.47  fof(f227,plain,(
% 0.22/0.47    spl3_29),
% 0.22/0.47    inference(avatar_split_clause,[],[f29,f225])).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,axiom,(
% 0.22/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X2)))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).
% 0.22/0.47  fof(f209,plain,(
% 0.22/0.47    spl3_27 | ~spl3_10 | ~spl3_15 | ~spl3_20 | ~spl3_23),
% 0.22/0.47    inference(avatar_split_clause,[],[f188,f172,f139,f108,f78,f206])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    spl3_10 <=> ! [X2] : k2_xboole_0(X2,X2) = X2),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    spl3_15 <=> ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.47  fof(f139,plain,(
% 0.22/0.47    spl3_20 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.22/0.47  fof(f172,plain,(
% 0.22/0.47    spl3_23 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.22/0.47  fof(f188,plain,(
% 0.22/0.47    sK2 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) | (~spl3_10 | ~spl3_15 | ~spl3_20 | ~spl3_23)),
% 0.22/0.47    inference(forward_demodulation,[],[f182,f186])).
% 0.22/0.47  fof(f186,plain,(
% 0.22/0.47    ( ! [X1] : (k2_xboole_0(X1,k1_xboole_0) = X1) ) | (~spl3_10 | ~spl3_15 | ~spl3_23)),
% 0.22/0.47    inference(forward_demodulation,[],[f180,f79])).
% 0.22/0.47  fof(f79,plain,(
% 0.22/0.47    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) ) | ~spl3_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f78])).
% 0.22/0.47  fof(f180,plain,(
% 0.22/0.47    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) ) | (~spl3_15 | ~spl3_23)),
% 0.22/0.47    inference(superposition,[],[f173,f109])).
% 0.22/0.47  fof(f109,plain,(
% 0.22/0.47    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | ~spl3_15),
% 0.22/0.47    inference(avatar_component_clause,[],[f108])).
% 0.22/0.47  fof(f173,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_23),
% 0.22/0.47    inference(avatar_component_clause,[],[f172])).
% 0.22/0.47  fof(f182,plain,(
% 0.22/0.47    k2_xboole_0(sK2,k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK1,sK0)) | (~spl3_20 | ~spl3_23)),
% 0.22/0.47    inference(superposition,[],[f173,f141])).
% 0.22/0.47  fof(f141,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) | ~spl3_20),
% 0.22/0.47    inference(avatar_component_clause,[],[f139])).
% 0.22/0.47  fof(f174,plain,(
% 0.22/0.47    spl3_23),
% 0.22/0.47    inference(avatar_split_clause,[],[f23,f172])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.47  fof(f142,plain,(
% 0.22/0.47    spl3_20 | ~spl3_2 | ~spl3_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f103,f70,f39,f139])).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    spl3_2 <=> r1_tarski(k4_xboole_0(sK1,sK0),sK2)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    spl3_9 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.47  fof(f103,plain,(
% 0.22/0.47    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK1,sK0),sK2) | (~spl3_2 | ~spl3_9)),
% 0.22/0.47    inference(resolution,[],[f71,f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    r1_tarski(k4_xboole_0(sK1,sK0),sK2) | ~spl3_2),
% 0.22/0.47    inference(avatar_component_clause,[],[f39])).
% 0.22/0.47  fof(f71,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) ) | ~spl3_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f70])).
% 0.22/0.47  fof(f110,plain,(
% 0.22/0.47    spl3_15 | ~spl3_5 | ~spl3_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f105,f70,f53,f108])).
% 0.22/0.47  fof(f53,plain,(
% 0.22/0.47    spl3_5 <=> ! [X0] : r1_tarski(X0,X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) ) | (~spl3_5 | ~spl3_9)),
% 0.22/0.47    inference(resolution,[],[f71,f54])).
% 0.22/0.47  fof(f54,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(X0,X0)) ) | ~spl3_5),
% 0.22/0.47    inference(avatar_component_clause,[],[f53])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl3_10 | ~spl3_5 | ~spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f76,f62,f53,f78])).
% 0.22/0.47  fof(f62,plain,(
% 0.22/0.47    spl3_7 <=> ! [X1,X0] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.47  fof(f76,plain,(
% 0.22/0.47    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) ) | (~spl3_5 | ~spl3_7)),
% 0.22/0.47    inference(resolution,[],[f63,f54])).
% 0.22/0.47  fof(f63,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) ) | ~spl3_7),
% 0.22/0.47    inference(avatar_component_clause,[],[f62])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    spl3_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f28,f70])).
% 0.22/0.47  fof(f28,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.47    inference(nnf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.47  fof(f64,plain,(
% 0.22/0.47    spl3_7),
% 0.22/0.47    inference(avatar_split_clause,[],[f26,f62])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.47  fof(f60,plain,(
% 0.22/0.47    ~spl3_6),
% 0.22/0.47    inference(avatar_split_clause,[],[f32,f57])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    ~r1_tarski(k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK2)),
% 0.22/0.47    inference(backward_demodulation,[],[f30,f31])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ~r1_tarski(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),sK2)),
% 0.22/0.47    inference(definition_unfolding,[],[f20,f24])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.22/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(k5_xboole_0(sK0,sK1),sK2) & r1_tarski(k4_xboole_0(sK1,sK0),sK2) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 0.22/0.47    introduced(choice_axiom,[])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.47    inference(flattening,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X1),X2) & (r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 0.22/0.47    inference(ennf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,negated_conjecture,(
% 0.22/0.47    ~! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 0.22/0.47    inference(negated_conjecture,[],[f9])).
% 0.22/0.47  fof(f9,conjecture,(
% 0.22/0.47    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_xboole_1)).
% 0.22/0.47  fof(f55,plain,(
% 0.22/0.47    spl3_5 | ~spl3_3 | ~spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f51,f48,f44,f53])).
% 0.22/0.47  fof(f44,plain,(
% 0.22/0.47    spl3_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.47  fof(f48,plain,(
% 0.22/0.47    spl3_4 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.47  fof(f51,plain,(
% 0.22/0.47    ( ! [X0] : (r1_tarski(X0,X0)) ) | (~spl3_3 | ~spl3_4)),
% 0.22/0.47    inference(superposition,[],[f49,f45])).
% 0.22/0.47  fof(f45,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.22/0.47    inference(avatar_component_clause,[],[f44])).
% 0.22/0.47  fof(f49,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_4),
% 0.22/0.47    inference(avatar_component_clause,[],[f48])).
% 0.22/0.47  fof(f50,plain,(
% 0.22/0.47    spl3_4),
% 0.22/0.47    inference(avatar_split_clause,[],[f22,f48])).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.22/0.47  fof(f46,plain,(
% 0.22/0.47    spl3_3),
% 0.22/0.47    inference(avatar_split_clause,[],[f21,f44])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.47    inference(cnf_transformation,[],[f7])).
% 0.22/0.47  fof(f7,axiom,(
% 0.22/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    spl3_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f19,f39])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    r1_tarski(k4_xboole_0(sK1,sK0),sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl3_1),
% 0.22/0.47    inference(avatar_split_clause,[],[f18,f34])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.22/0.47    inference(cnf_transformation,[],[f16])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (4816)------------------------------
% 0.22/0.47  % (4816)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (4816)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (4816)Memory used [KB]: 6268
% 0.22/0.47  % (4816)Time elapsed: 0.049 s
% 0.22/0.47  % (4816)------------------------------
% 0.22/0.47  % (4816)------------------------------
% 0.22/0.47  % (4807)Success in time 0.106 s
%------------------------------------------------------------------------------
