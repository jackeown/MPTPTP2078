%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:50 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 116 expanded)
%              Number of leaves         :   23 (  54 expanded)
%              Depth                    :    6
%              Number of atoms          :  162 ( 241 expanded)
%              Number of equality atoms :   51 (  81 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f282,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f35,f39,f43,f51,f59,f63,f69,f75,f97,f175,f197,f233,f265,f279])).

fof(f279,plain,
    ( spl3_2
    | ~ spl3_6
    | ~ spl3_27 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | spl3_2
    | ~ spl3_6
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f34,f277])).

fof(f277,plain,
    ( ! [X0] : r1_tarski(k4_xboole_0(sK0,X0),sK1)
    | ~ spl3_6
    | ~ spl3_27 ),
    inference(trivial_inequality_removal,[],[f269])).

fof(f269,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k1_xboole_0
        | r1_tarski(k4_xboole_0(sK0,X0),sK1) )
    | ~ spl3_6
    | ~ spl3_27 ),
    inference(superposition,[],[f58,f264])).

fof(f264,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X3),sK1)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f263])).

fof(f263,plain,
    ( spl3_27
  <=> ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 != k4_xboole_0(X0,X1)
        | r1_tarski(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl3_6
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f34,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl3_2
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f265,plain,
    ( spl3_27
    | ~ spl3_8
    | ~ spl3_20
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f254,f231,f173,f66,f263])).

fof(f66,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f173,plain,
    ( spl3_20
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f231,plain,
    ( spl3_24
  <=> ! [X0] : k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k4_xboole_0(X0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f254,plain,
    ( ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X3),sK1)
    | ~ spl3_8
    | ~ spl3_20
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f243,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f66])).

fof(f243,plain,
    ( ! [X3] : k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,X3),sK1)
    | ~ spl3_20
    | ~ spl3_24 ),
    inference(superposition,[],[f232,f174])).

fof(f174,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f173])).

fof(f232,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k4_xboole_0(X0,sK1)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f233,plain,
    ( spl3_24
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f222,f195,f66,f49,f231])).

fof(f49,plain,
    ( spl3_5
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f195,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f222,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k4_xboole_0(X0,sK1)
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f206,f50])).

fof(f50,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f206,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK1))
    | ~ spl3_8
    | ~ spl3_23 ),
    inference(superposition,[],[f196,f68])).

fof(f196,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f195])).

fof(f197,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f23,f195])).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f175,plain,
    ( spl3_20
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f127,f95,f73,f173])).

fof(f73,plain,
    ( spl3_9
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f95,plain,
    ( spl3_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f127,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | ~ spl3_9
    | ~ spl3_12 ),
    inference(superposition,[],[f74,f96])).

fof(f96,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f95])).

fof(f74,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f73])).

fof(f97,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f25,f95])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f20,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f75,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f24,f73])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f18,f19])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f69,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f64,f61,f27,f66])).

fof(f27,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f61,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f64,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(resolution,[],[f62,f29])).

fof(f29,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f62,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k4_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f61])).

fof(f63,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f22,f61])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f59,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f21,f57])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f51,plain,
    ( spl3_5
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f44,f41,f37,f49])).

fof(f37,plain,
    ( spl3_3
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f41,plain,
    ( spl3_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f44,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(superposition,[],[f42,f38])).

fof(f38,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f42,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f43,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f39,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f16,f37])).

fof(f16,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f35,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f15,f32])).

fof(f15,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f30,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f27])).

fof(f14,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n002.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:19:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (18615)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (18615)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f282,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f30,f35,f39,f43,f51,f59,f63,f69,f75,f97,f175,f197,f233,f265,f279])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    spl3_2 | ~spl3_6 | ~spl3_27),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f278])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    $false | (spl3_2 | ~spl3_6 | ~spl3_27)),
% 0.21/0.48    inference(subsumption_resolution,[],[f34,f277])).
% 0.21/0.48  fof(f277,plain,(
% 0.21/0.48    ( ! [X0] : (r1_tarski(k4_xboole_0(sK0,X0),sK1)) ) | (~spl3_6 | ~spl3_27)),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f269])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,X0),sK1)) ) | (~spl3_6 | ~spl3_27)),
% 0.21/0.48    inference(superposition,[],[f58,f264])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X3),sK1)) ) | ~spl3_27),
% 0.21/0.48    inference(avatar_component_clause,[],[f263])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    spl3_27 <=> ! [X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X3),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) ) | ~spl3_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl3_6 <=> ! [X1,X0] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) | spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    spl3_2 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    spl3_27 | ~spl3_8 | ~spl3_20 | ~spl3_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f254,f231,f173,f66,f263])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl3_8 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    spl3_20 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.48  fof(f231,plain,(
% 0.21/0.48    spl3_24 <=> ! [X0] : k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k4_xboole_0(X0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.48  fof(f254,plain,(
% 0.21/0.48    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X3),sK1)) ) | (~spl3_8 | ~spl3_20 | ~spl3_24)),
% 0.21/0.48    inference(forward_demodulation,[],[f243,f68])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f66])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    ( ! [X3] : (k4_xboole_0(sK0,sK1) = k4_xboole_0(k4_xboole_0(sK0,X3),sK1)) ) | (~spl3_20 | ~spl3_24)),
% 0.21/0.48    inference(superposition,[],[f232,f174])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | ~spl3_20),
% 0.21/0.48    inference(avatar_component_clause,[],[f173])).
% 0.21/0.48  fof(f232,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k4_xboole_0(X0,sK1)) ) | ~spl3_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f231])).
% 0.21/0.48  fof(f233,plain,(
% 0.21/0.48    spl3_24 | ~spl3_5 | ~spl3_8 | ~spl3_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f222,f195,f66,f49,f231])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl3_5 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    spl3_23 <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.48  fof(f222,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k4_xboole_0(X0,sK1)) ) | (~spl3_5 | ~spl3_8 | ~spl3_23)),
% 0.21/0.48    inference(forward_demodulation,[],[f206,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl3_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK0,X0),sK1) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,sK1))) ) | (~spl3_8 | ~spl3_23)),
% 0.21/0.48    inference(superposition,[],[f196,f68])).
% 0.21/0.48  fof(f196,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) ) | ~spl3_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f195])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl3_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f23,f195])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 0.21/0.48  fof(f175,plain,(
% 0.21/0.48    spl3_20 | ~spl3_9 | ~spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f127,f95,f73,f173])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl3_9 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl3_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) ) | (~spl3_9 | ~spl3_12)),
% 0.21/0.48    inference(superposition,[],[f74,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) ) | ~spl3_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f73])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f95])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f20,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f24,f73])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f18,f19])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    spl3_8 | ~spl3_1 | ~spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f64,f61,f27,f66])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_7 <=> ! [X1,X0] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(sK0,sK1) | (~spl3_1 | ~spl3_7)),
% 0.21/0.48    inference(resolution,[],[f62,f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f27])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f61])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f22,f61])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f21,f57])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl3_5 | ~spl3_3 | ~spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f41,f37,f49])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    spl3_3 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    spl3_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl3_3 | ~spl3_4)),
% 0.21/0.48    inference(superposition,[],[f42,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f37])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f41])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f41])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f37])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f15,f32])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.48    inference(negated_conjecture,[],[f8])).
% 0.21/0.48  fof(f8,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f14,f27])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    r1_tarski(sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (18615)------------------------------
% 0.21/0.48  % (18615)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18615)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (18615)Memory used [KB]: 6268
% 0.21/0.48  % (18615)Time elapsed: 0.013 s
% 0.21/0.48  % (18615)------------------------------
% 0.21/0.48  % (18615)------------------------------
% 0.21/0.48  % (18607)Success in time 0.113 s
%------------------------------------------------------------------------------
