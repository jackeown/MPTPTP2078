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
% DateTime   : Thu Dec  3 12:30:19 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   61 (  96 expanded)
%              Number of leaves         :   20 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :  130 ( 209 expanded)
%              Number of equality atoms :   27 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f225,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f47,f60,f70,f71,f82,f107,f125,f155,f221,f224])).

fof(f224,plain,
    ( sK1 != k2_xboole_0(sK0,sK1)
    | sK0 != k2_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f221,plain,
    ( spl3_16
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f209,f127,f218])).

fof(f218,plain,
    ( spl3_16
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f127,plain,
    ( spl3_11
  <=> sK0 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f209,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f129,f17])).

fof(f17,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f129,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f127])).

fof(f155,plain,
    ( sK0 != sK2
    | sK2 != k2_xboole_0(sK1,sK2)
    | sK0 = k2_xboole_0(sK1,sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f125,plain,
    ( spl3_10
    | spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f116,f104,f35,f122])).

fof(f122,plain,
    ( spl3_10
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f35,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f104,plain,
    ( spl3_9
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f116,plain,
    ( sK0 = sK2
    | spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f114,f37])).

fof(f37,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f114,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f106,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f106,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f107,plain,
    ( spl3_9
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f92,f57,f44,f104])).

fof(f44,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f57,plain,
    ( spl3_5
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f92,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f76,f59])).

fof(f59,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f76,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(sK1,X0))
    | ~ spl3_4 ),
    inference(superposition,[],[f48,f17])).

fof(f48,plain,
    ( ! [X0] : r1_tarski(sK0,k2_xboole_0(X0,sK1))
    | ~ spl3_4 ),
    inference(resolution,[],[f46,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f46,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f44])).

fof(f82,plain,
    ( spl3_8
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f50,f44,f79])).

fof(f79,plain,
    ( spl3_8
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f50,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f46,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f71,plain,
    ( sK1 != sK2
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f70,plain,
    ( spl3_6
    | spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f41,f30,f67,f63])).

fof(f63,plain,
    ( spl3_6
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f67,plain,
    ( spl3_7
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f41,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f32,f21])).

fof(f32,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f60,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f30,f57])).

fof(f42,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f32,f18])).

fof(f47,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f39,f25,f44])).

fof(f25,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f39,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f27,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f38,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.12/0.32  % Computer   : n010.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:58:44 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.19/0.41  % (7805)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.41  % (7797)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.42  % (7797)Refutation found. Thanks to Tanya!
% 0.19/0.42  % SZS status Theorem for theBenchmark
% 0.19/0.42  % SZS output start Proof for theBenchmark
% 0.19/0.42  fof(f225,plain,(
% 0.19/0.42    $false),
% 0.19/0.42    inference(avatar_sat_refutation,[],[f28,f33,f38,f47,f60,f70,f71,f82,f107,f125,f155,f221,f224])).
% 0.19/0.42  fof(f224,plain,(
% 0.19/0.42    sK1 != k2_xboole_0(sK0,sK1) | sK0 != k2_xboole_0(sK0,sK1) | r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK1,sK2)),
% 0.19/0.42    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.42  fof(f221,plain,(
% 0.19/0.42    spl3_16 | ~spl3_11),
% 0.19/0.42    inference(avatar_split_clause,[],[f209,f127,f218])).
% 0.19/0.42  fof(f218,plain,(
% 0.19/0.42    spl3_16 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.19/0.42  fof(f127,plain,(
% 0.19/0.42    spl3_11 <=> sK0 = k2_xboole_0(sK1,sK0)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.19/0.42  fof(f209,plain,(
% 0.19/0.42    sK0 = k2_xboole_0(sK0,sK1) | ~spl3_11),
% 0.19/0.42    inference(superposition,[],[f129,f17])).
% 0.19/0.42  fof(f17,plain,(
% 0.19/0.42    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f1])).
% 0.19/0.42  fof(f1,axiom,(
% 0.19/0.42    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.19/0.42  fof(f129,plain,(
% 0.19/0.42    sK0 = k2_xboole_0(sK1,sK0) | ~spl3_11),
% 0.19/0.42    inference(avatar_component_clause,[],[f127])).
% 0.19/0.42  fof(f155,plain,(
% 0.19/0.42    sK0 != sK2 | sK2 != k2_xboole_0(sK1,sK2) | sK0 = k2_xboole_0(sK1,sK0)),
% 0.19/0.42    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.42  fof(f125,plain,(
% 0.19/0.42    spl3_10 | spl3_3 | ~spl3_9),
% 0.19/0.42    inference(avatar_split_clause,[],[f116,f104,f35,f122])).
% 0.19/0.42  fof(f122,plain,(
% 0.19/0.42    spl3_10 <=> sK0 = sK2),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.19/0.42  fof(f35,plain,(
% 0.19/0.42    spl3_3 <=> r2_xboole_0(sK0,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.19/0.42  fof(f104,plain,(
% 0.19/0.42    spl3_9 <=> r1_tarski(sK0,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.19/0.42  fof(f116,plain,(
% 0.19/0.42    sK0 = sK2 | (spl3_3 | ~spl3_9)),
% 0.19/0.42    inference(subsumption_resolution,[],[f114,f37])).
% 0.19/0.42  fof(f37,plain,(
% 0.19/0.42    ~r2_xboole_0(sK0,sK2) | spl3_3),
% 0.19/0.42    inference(avatar_component_clause,[],[f35])).
% 0.19/0.42  fof(f114,plain,(
% 0.19/0.42    sK0 = sK2 | r2_xboole_0(sK0,sK2) | ~spl3_9),
% 0.19/0.42    inference(resolution,[],[f106,f21])).
% 0.19/0.42  fof(f21,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f2,axiom,(
% 0.19/0.42    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.19/0.42  fof(f106,plain,(
% 0.19/0.42    r1_tarski(sK0,sK2) | ~spl3_9),
% 0.19/0.42    inference(avatar_component_clause,[],[f104])).
% 0.19/0.42  fof(f107,plain,(
% 0.19/0.42    spl3_9 | ~spl3_4 | ~spl3_5),
% 0.19/0.42    inference(avatar_split_clause,[],[f92,f57,f44,f104])).
% 0.19/0.42  fof(f44,plain,(
% 0.19/0.42    spl3_4 <=> r1_tarski(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.19/0.42  fof(f57,plain,(
% 0.19/0.42    spl3_5 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.19/0.42  fof(f92,plain,(
% 0.19/0.42    r1_tarski(sK0,sK2) | (~spl3_4 | ~spl3_5)),
% 0.19/0.42    inference(superposition,[],[f76,f59])).
% 0.19/0.42  fof(f59,plain,(
% 0.19/0.42    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_5),
% 0.19/0.42    inference(avatar_component_clause,[],[f57])).
% 0.19/0.42  fof(f76,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(sK1,X0))) ) | ~spl3_4),
% 0.19/0.42    inference(superposition,[],[f48,f17])).
% 0.19/0.42  fof(f48,plain,(
% 0.19/0.42    ( ! [X0] : (r1_tarski(sK0,k2_xboole_0(X0,sK1))) ) | ~spl3_4),
% 0.19/0.42    inference(resolution,[],[f46,f22])).
% 0.19/0.42  fof(f22,plain,(
% 0.19/0.42    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(X0,k2_xboole_0(X2,X1))) )),
% 0.19/0.42    inference(cnf_transformation,[],[f12])).
% 0.19/0.42  fof(f12,plain,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f4])).
% 0.19/0.42  fof(f4,axiom,(
% 0.19/0.42    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.19/0.42  fof(f46,plain,(
% 0.19/0.42    r1_tarski(sK0,sK1) | ~spl3_4),
% 0.19/0.42    inference(avatar_component_clause,[],[f44])).
% 0.19/0.42  fof(f82,plain,(
% 0.19/0.42    spl3_8 | ~spl3_4),
% 0.19/0.42    inference(avatar_split_clause,[],[f50,f44,f79])).
% 0.19/0.42  fof(f79,plain,(
% 0.19/0.42    spl3_8 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.19/0.42  fof(f50,plain,(
% 0.19/0.42    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_4),
% 0.19/0.42    inference(resolution,[],[f46,f18])).
% 0.19/0.42  fof(f18,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.19/0.42    inference(cnf_transformation,[],[f11])).
% 0.19/0.42  fof(f11,plain,(
% 0.19/0.42    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.19/0.42    inference(ennf_transformation,[],[f5])).
% 0.19/0.42  fof(f5,axiom,(
% 0.19/0.42    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.19/0.42  fof(f71,plain,(
% 0.19/0.42    sK1 != sK2 | r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK0,sK1)),
% 0.19/0.42    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.42  fof(f70,plain,(
% 0.19/0.42    spl3_6 | spl3_7 | ~spl3_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f41,f30,f67,f63])).
% 0.19/0.42  fof(f63,plain,(
% 0.19/0.42    spl3_6 <=> r2_xboole_0(sK1,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.19/0.42  fof(f67,plain,(
% 0.19/0.42    spl3_7 <=> sK1 = sK2),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.19/0.42  fof(f30,plain,(
% 0.19/0.42    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.42  fof(f41,plain,(
% 0.19/0.42    sK1 = sK2 | r2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.19/0.42    inference(resolution,[],[f32,f21])).
% 0.19/0.42  fof(f32,plain,(
% 0.19/0.42    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.19/0.42    inference(avatar_component_clause,[],[f30])).
% 0.19/0.42  fof(f60,plain,(
% 0.19/0.42    spl3_5 | ~spl3_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f42,f30,f57])).
% 0.19/0.42  fof(f42,plain,(
% 0.19/0.42    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.19/0.42    inference(resolution,[],[f32,f18])).
% 0.19/0.42  fof(f47,plain,(
% 0.19/0.42    spl3_4 | ~spl3_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f39,f25,f44])).
% 0.19/0.42  fof(f25,plain,(
% 0.19/0.42    spl3_1 <=> r2_xboole_0(sK0,sK1)),
% 0.19/0.42    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.42  fof(f39,plain,(
% 0.19/0.42    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.19/0.42    inference(resolution,[],[f27,f19])).
% 0.19/0.42  fof(f19,plain,(
% 0.19/0.42    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.19/0.42    inference(cnf_transformation,[],[f2])).
% 0.19/0.42  fof(f27,plain,(
% 0.19/0.42    r2_xboole_0(sK0,sK1) | ~spl3_1),
% 0.19/0.42    inference(avatar_component_clause,[],[f25])).
% 0.19/0.42  fof(f38,plain,(
% 0.19/0.42    ~spl3_3),
% 0.19/0.42    inference(avatar_split_clause,[],[f15,f35])).
% 0.19/0.42  fof(f15,plain,(
% 0.19/0.42    ~r2_xboole_0(sK0,sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  fof(f10,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.19/0.42    inference(flattening,[],[f9])).
% 0.19/0.42  fof(f9,plain,(
% 0.19/0.42    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.19/0.42    inference(ennf_transformation,[],[f7])).
% 0.19/0.42  fof(f7,negated_conjecture,(
% 0.19/0.42    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.19/0.42    inference(negated_conjecture,[],[f6])).
% 0.19/0.42  fof(f6,conjecture,(
% 0.19/0.42    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.19/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.19/0.42  fof(f33,plain,(
% 0.19/0.42    spl3_2),
% 0.19/0.42    inference(avatar_split_clause,[],[f14,f30])).
% 0.19/0.42  fof(f14,plain,(
% 0.19/0.42    r1_tarski(sK1,sK2)),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  fof(f28,plain,(
% 0.19/0.42    spl3_1),
% 0.19/0.42    inference(avatar_split_clause,[],[f13,f25])).
% 0.19/0.42  fof(f13,plain,(
% 0.19/0.42    r2_xboole_0(sK0,sK1)),
% 0.19/0.42    inference(cnf_transformation,[],[f10])).
% 0.19/0.42  % SZS output end Proof for theBenchmark
% 0.19/0.42  % (7797)------------------------------
% 0.19/0.42  % (7797)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.42  % (7797)Termination reason: Refutation
% 0.19/0.42  
% 0.19/0.42  % (7797)Memory used [KB]: 10618
% 0.19/0.42  % (7797)Time elapsed: 0.048 s
% 0.19/0.42  % (7797)------------------------------
% 0.19/0.42  % (7797)------------------------------
% 0.19/0.42  % (7791)Success in time 0.085 s
%------------------------------------------------------------------------------
