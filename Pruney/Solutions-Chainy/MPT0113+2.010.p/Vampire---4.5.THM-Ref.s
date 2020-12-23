%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:34 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 109 expanded)
%              Number of leaves         :   22 (  45 expanded)
%              Depth                    :    8
%              Number of atoms          :  139 ( 202 expanded)
%              Number of equality atoms :   36 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f631,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f56,f101,f121,f148,f306,f324,f619,f629])).

fof(f629,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | spl3_13 ),
    inference(unit_resulting_resolution,[],[f31,f618])).

fof(f618,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f616])).

fof(f616,plain,
    ( spl3_13
  <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f619,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f601,f321,f44,f616])).

fof(f44,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f321,plain,
    ( spl3_9
  <=> k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f601,plain,
    ( ~ r1_tarski(k4_xboole_0(sK1,sK2),sK1)
    | spl3_1
    | ~ spl3_9 ),
    inference(superposition,[],[f75,f323])).

fof(f323,plain,
    ( k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f321])).

fof(f75,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(X0,sK0),sK1)
    | spl3_1 ),
    inference(superposition,[],[f67,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f67,plain,
    ( ! [X0] : ~ r1_tarski(k2_xboole_0(sK0,X0),sK1)
    | spl3_1 ),
    inference(unit_resulting_resolution,[],[f46,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f46,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f324,plain,
    ( spl3_9
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f319,f303,f321])).

fof(f303,plain,
    ( spl3_8
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f319,plain,
    ( k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0)
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f314,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f314,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)
    | ~ spl3_8 ),
    inference(superposition,[],[f34,f305])).

fof(f305,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f303])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f306,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f301,f145,f303])).

fof(f145,plain,
    ( spl3_5
  <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f301,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f147,f131])).

fof(f131,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f129,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f129,plain,(
    ! [X1] : k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)) ),
    inference(superposition,[],[f39,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f40,f28])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f26,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f35,f33])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f147,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f145])).

fof(f148,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f140,f115,f145])).

fof(f115,plain,
    ( spl3_4
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f140,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0)
    | ~ spl3_4 ),
    inference(superposition,[],[f39,f117])).

fof(f117,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f121,plain,
    ( spl3_4
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f113,f53,f115])).

fof(f53,plain,
    ( spl3_3
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f113,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))
    | ~ spl3_3 ),
    inference(resolution,[],[f42,f55])).

fof(f55,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f36,f33])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f101,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f87,f53,f48])).

fof(f48,plain,
    ( spl3_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f87,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f55,f30,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f56,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f24,f53])).

fof(f24,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f51,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f25,f48,f44])).

fof(f25,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:02:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (21063)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (21058)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (21063)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f631,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f51,f56,f101,f121,f148,f306,f324,f619,f629])).
% 0.21/0.47  fof(f629,plain,(
% 0.21/0.47    spl3_13),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f623])).
% 0.21/0.47  fof(f623,plain,(
% 0.21/0.47    $false | spl3_13),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f31,f618])).
% 0.21/0.47  fof(f618,plain,(
% 0.21/0.47    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | spl3_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f616])).
% 0.21/0.47  fof(f616,plain,(
% 0.21/0.47    spl3_13 <=> r1_tarski(k4_xboole_0(sK1,sK2),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.47  fof(f619,plain,(
% 0.21/0.47    ~spl3_13 | spl3_1 | ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f601,f321,f44,f616])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.47  fof(f321,plain,(
% 0.21/0.47    spl3_9 <=> k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f601,plain,(
% 0.21/0.47    ~r1_tarski(k4_xboole_0(sK1,sK2),sK1) | (spl3_1 | ~spl3_9)),
% 0.21/0.47    inference(superposition,[],[f75,f323])).
% 0.21/0.47  fof(f323,plain,(
% 0.21/0.47    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f321])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(k2_xboole_0(X0,sK0),sK1)) ) | spl3_1),
% 0.21/0.47    inference(superposition,[],[f67,f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0] : (~r1_tarski(k2_xboole_0(sK0,X0),sK1)) ) | spl3_1),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f46,f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f44])).
% 0.21/0.47  fof(f324,plain,(
% 0.21/0.47    spl3_9 | ~spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f319,f303,f321])).
% 0.21/0.47  fof(f303,plain,(
% 0.21/0.47    spl3_8 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.47  fof(f319,plain,(
% 0.21/0.47    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) | ~spl3_8),
% 0.21/0.47    inference(forward_demodulation,[],[f314,f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.47  fof(f314,plain,(
% 0.21/0.47    k2_xboole_0(k4_xboole_0(sK1,sK2),sK0) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) | ~spl3_8),
% 0.21/0.47    inference(superposition,[],[f34,f305])).
% 0.21/0.47  fof(f305,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_8),
% 0.21/0.47    inference(avatar_component_clause,[],[f303])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.47  fof(f306,plain,(
% 0.21/0.47    spl3_8 | ~spl3_5),
% 0.21/0.47    inference(avatar_split_clause,[],[f301,f145,f303])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    spl3_5 <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f301,plain,(
% 0.21/0.47    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_5),
% 0.21/0.47    inference(forward_demodulation,[],[f147,f131])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,X1)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f129,f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    ( ! [X1] : (k1_xboole_0 = k5_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) )),
% 0.21/0.47    inference(superposition,[],[f39,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.47    inference(forward_demodulation,[],[f40,f28])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f26,f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.47    inference(definition_unfolding,[],[f35,f33])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f145])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    spl3_5 | ~spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f140,f115,f145])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    spl3_4 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k5_xboole_0(sK0,sK0) | ~spl3_4),
% 0.21/0.47    inference(superposition,[],[f39,f117])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f115])).
% 0.21/0.47  fof(f121,plain,(
% 0.21/0.47    spl3_4 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f113,f53,f115])).
% 0.21/0.47  fof(f53,plain,(
% 0.21/0.47    spl3_3 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f113,plain,(
% 0.21/0.47    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))) | ~spl3_3),
% 0.21/0.47    inference(resolution,[],[f42,f55])).
% 0.21/0.47  fof(f55,plain,(
% 0.21/0.47    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f53])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.47    inference(definition_unfolding,[],[f36,f33])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.47  fof(f101,plain,(
% 0.21/0.47    spl3_2 | ~spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f87,f53,f48])).
% 0.21/0.47  fof(f48,plain,(
% 0.21/0.47    spl3_2 <=> r1_xboole_0(sK0,sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    r1_xboole_0(sK0,sK2) | ~spl3_3),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f55,f30,f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f24,f53])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.21/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.21/0.47    introduced(choice_axiom,[])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.21/0.47    inference(ennf_transformation,[],[f15])).
% 0.21/0.47  fof(f15,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.47    inference(negated_conjecture,[],[f14])).
% 0.21/0.47  fof(f14,conjecture,(
% 0.21/0.47    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ~spl3_1 | ~spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f25,f48,f44])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f23])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (21063)------------------------------
% 0.21/0.47  % (21063)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21063)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (21063)Memory used [KB]: 6396
% 0.21/0.47  % (21063)Time elapsed: 0.019 s
% 0.21/0.47  % (21063)------------------------------
% 0.21/0.47  % (21063)------------------------------
% 0.21/0.47  % (21053)Success in time 0.112 s
%------------------------------------------------------------------------------
