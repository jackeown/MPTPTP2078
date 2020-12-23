%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:36 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 145 expanded)
%              Number of leaves         :   27 (  70 expanded)
%              Depth                    :    7
%              Number of atoms          :  222 ( 352 expanded)
%              Number of equality atoms :   46 (  74 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f756,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f42,f46,f50,f54,f58,f62,f66,f74,f92,f114,f126,f157,f171,f198,f278,f533,f722,f744])).

fof(f744,plain,
    ( ~ spl3_6
    | spl3_12
    | ~ spl3_23
    | ~ spl3_42
    | ~ spl3_56 ),
    inference(avatar_contradiction_clause,[],[f743])).

fof(f743,plain,
    ( $false
    | ~ spl3_6
    | spl3_12
    | ~ spl3_23
    | ~ spl3_42
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f91,f742])).

fof(f742,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_6
    | ~ spl3_23
    | ~ spl3_42
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f741,f532])).

fof(f532,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f530])).

fof(f530,plain,
    ( spl3_42
  <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f741,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_6
    | ~ spl3_23
    | ~ spl3_56 ),
    inference(forward_demodulation,[],[f724,f53])).

fof(f53,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl3_6
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f724,plain,
    ( k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0)
    | ~ spl3_23
    | ~ spl3_56 ),
    inference(superposition,[],[f721,f197])).

fof(f197,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f196])).

fof(f196,plain,
    ( spl3_23
  <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f721,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f720])).

fof(f720,plain,
    ( spl3_56
  <=> ! [X0] : k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f91,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_12
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f722,plain,
    ( spl3_56
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f159,f154,f112,f720])).

fof(f112,plain,
    ( spl3_13
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f154,plain,
    ( spl3_18
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f159,plain,
    ( ! [X0] : k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))
    | ~ spl3_13
    | ~ spl3_18 ),
    inference(superposition,[],[f113,f156])).

fof(f156,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f154])).

fof(f113,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f112])).

fof(f533,plain,
    ( spl3_42
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f282,f276,f168,f530])).

fof(f168,plain,
    ( spl3_20
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f276,plain,
    ( spl3_30
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f282,plain,
    ( k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)
    | ~ spl3_20
    | ~ spl3_30 ),
    inference(superposition,[],[f277,f170])).

fof(f170,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f168])).

fof(f277,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f276])).

fof(f278,plain,
    ( spl3_30
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f76,f56,f48,f276])).

fof(f48,plain,
    ( spl3_5
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f56,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f76,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_5
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f49,f57])).

fof(f57,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f49,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f48])).

fof(f198,plain,
    ( spl3_23
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f83,f64,f48,f196])).

fof(f64,plain,
    ( spl3_9
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f83,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f49,f65])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f64])).

fof(f171,plain,
    ( spl3_20
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f82,f64,f30,f168])).

fof(f30,plain,
    ( spl3_1
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f82,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f32,f65])).

fof(f32,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f157,plain,
    ( spl3_18
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f75,f56,f30,f154])).

fof(f75,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f32,f57])).

fof(f126,plain,
    ( spl3_3
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f98,f72,f44,f30,f39])).

fof(f39,plain,
    ( spl3_3
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f44,plain,
    ( spl3_4
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f98,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f32,f45,f73])).

fof(f73,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f72])).

fof(f45,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f114,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f27,f112])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f92,plain,
    ( ~ spl3_12
    | spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f81,f60,f35,f89])).

fof(f35,plain,
    ( spl3_2
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f60,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f81,plain,
    ( k1_xboole_0 != k4_xboole_0(sK0,sK1)
    | spl3_2
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f37,f61])).

fof(f61,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) != k1_xboole_0
        | r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f37,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f74,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f28,f72])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f66,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f26,f64])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f62,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f25,f60])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f58,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f24,f56])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f54,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f22,f52])).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f50,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f21,f48])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f46,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f20,f44])).

fof(f20,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f42,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f19,f39,f35])).

fof(f19,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f33,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f30])).

fof(f18,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:09:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (15147)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.46  % (15151)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.46  % (15141)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (15142)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (15143)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (15137)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (15149)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.48  % (15150)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (15138)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (15148)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (15139)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (15140)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (15144)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (15142)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f756,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f33,f42,f46,f50,f54,f58,f62,f66,f74,f92,f114,f126,f157,f171,f198,f278,f533,f722,f744])).
% 0.21/0.50  fof(f744,plain,(
% 0.21/0.50    ~spl3_6 | spl3_12 | ~spl3_23 | ~spl3_42 | ~spl3_56),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f743])).
% 0.21/0.50  fof(f743,plain,(
% 0.21/0.50    $false | (~spl3_6 | spl3_12 | ~spl3_23 | ~spl3_42 | ~spl3_56)),
% 0.21/0.50    inference(subsumption_resolution,[],[f91,f742])).
% 0.21/0.50  fof(f742,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_6 | ~spl3_23 | ~spl3_42 | ~spl3_56)),
% 0.21/0.50    inference(forward_demodulation,[],[f741,f532])).
% 0.21/0.50  fof(f532,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | ~spl3_42),
% 0.21/0.50    inference(avatar_component_clause,[],[f530])).
% 0.21/0.50  fof(f530,plain,(
% 0.21/0.50    spl3_42 <=> k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.50  fof(f741,plain,(
% 0.21/0.50    k4_xboole_0(sK0,sK1) = k3_xboole_0(k1_xboole_0,sK0) | (~spl3_6 | ~spl3_23 | ~spl3_56)),
% 0.21/0.50    inference(forward_demodulation,[],[f724,f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    spl3_6 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f724,plain,(
% 0.21/0.50    k4_xboole_0(sK0,sK1) = k3_xboole_0(sK0,k1_xboole_0) | (~spl3_23 | ~spl3_56)),
% 0.21/0.50    inference(superposition,[],[f721,f197])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f196])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    spl3_23 <=> ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f721,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) ) | ~spl3_56),
% 0.21/0.50    inference(avatar_component_clause,[],[f720])).
% 0.21/0.50  fof(f720,plain,(
% 0.21/0.50    spl3_56 <=> ! [X0] : k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK1) | spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl3_12 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f722,plain,(
% 0.21/0.50    spl3_56 | ~spl3_13 | ~spl3_18),
% 0.21/0.50    inference(avatar_split_clause,[],[f159,f154,f112,f720])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    spl3_13 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    spl3_18 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f159,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(sK0,X0) = k3_xboole_0(sK0,k4_xboole_0(k4_xboole_0(sK1,sK2),X0))) ) | (~spl3_13 | ~spl3_18)),
% 0.21/0.50    inference(superposition,[],[f113,f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f154])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) ) | ~spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f112])).
% 0.21/0.50  fof(f533,plain,(
% 0.21/0.50    spl3_42 | ~spl3_20 | ~spl3_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f282,f276,f168,f530])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    spl3_20 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    spl3_30 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    k1_xboole_0 = k3_xboole_0(k1_xboole_0,sK0) | (~spl3_20 | ~spl3_30)),
% 0.21/0.50    inference(superposition,[],[f277,f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f168])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) ) | ~spl3_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f276])).
% 0.21/0.50  fof(f278,plain,(
% 0.21/0.50    spl3_30 | ~spl3_5 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f76,f56,f48,f276])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl3_5 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    spl3_7 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_5 | ~spl3_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f49,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f56])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f48])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    spl3_23 | ~spl3_5 | ~spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f83,f64,f48,f196])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    spl3_9 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) ) | (~spl3_5 | ~spl3_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f49,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f64])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    spl3_20 | ~spl3_1 | ~spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f82,f64,f30,f168])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    spl3_1 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_9)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f32,f65])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f30])).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    spl3_18 | ~spl3_1 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f75,f56,f30,f154])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | (~spl3_1 | ~spl3_7)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f32,f57])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    spl3_3 | ~spl3_1 | ~spl3_4 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f98,f72,f44,f30,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    spl3_3 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    spl3_4 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    spl3_11 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    r1_xboole_0(sK0,sK2) | (~spl3_1 | ~spl3_4 | ~spl3_11)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f32,f45,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) ) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f72])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f44])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    spl3_13),
% 0.21/0.50    inference(avatar_split_clause,[],[f27,f112])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    ~spl3_12 | spl3_2 | ~spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f81,f60,f35,f89])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    spl3_2 <=> r1_tarski(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    spl3_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    k1_xboole_0 != k4_xboole_0(sK0,sK1) | (spl3_2 | ~spl3_8)),
% 0.21/0.50    inference(unit_resulting_resolution,[],[f37,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.21/0.50    inference(avatar_component_clause,[],[f60])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ~r1_tarski(sK0,sK1) | spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f35])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f28,f72])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f13])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f26,f64])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.50    inference(nnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f25,f60])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f24,f56])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f22,f52])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f21,f48])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f20,f44])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ~spl3_2 | ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f19,f39,f35])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f15])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f11,plain,(
% 0.21/0.50    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f18,f30])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.50    inference(cnf_transformation,[],[f16])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (15142)------------------------------
% 0.21/0.50  % (15142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (15142)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (15142)Memory used [KB]: 6652
% 0.21/0.50  % (15142)Time elapsed: 0.071 s
% 0.21/0.50  % (15142)------------------------------
% 0.21/0.50  % (15142)------------------------------
% 0.21/0.50  % (15136)Success in time 0.142 s
%------------------------------------------------------------------------------
