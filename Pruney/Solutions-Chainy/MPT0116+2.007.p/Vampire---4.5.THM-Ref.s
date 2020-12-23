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
% DateTime   : Thu Dec  3 12:32:51 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   51 (  71 expanded)
%              Number of leaves         :   15 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :  108 ( 156 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f185,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f41,f45,f83,f99,f152,f184])).

fof(f184,plain,
    ( spl3_2
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl3_2
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f28,f180])).

fof(f180,plain,
    ( ! [X1] : r1_tarski(k4_xboole_0(sK0,X1),sK1)
    | ~ spl3_10
    | ~ spl3_16 ),
    inference(superposition,[],[f82,f151])).

fof(f151,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl3_16
  <=> sK0 = k3_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f82,plain,
    ( ! [X2,X0,X1] : r1_tarski(k4_xboole_0(k3_xboole_0(X0,X1),X2),X0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl3_10
  <=> ! [X1,X0,X2] : r1_tarski(k4_xboole_0(k3_xboole_0(X0,X1),X2),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f28,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl3_2
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f152,plain,
    ( spl3_16
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f100,f97,f21,f149])).

fof(f21,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f97,plain,
    ( spl3_12
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f100,plain,
    ( sK0 = k3_xboole_0(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f23,f98])).

fof(f98,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f23,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f99,plain,
    ( spl3_12
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f52,f39,f35,f97])).

fof(f35,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f39,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f52,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(superposition,[],[f40,f36])).

fof(f36,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f35])).

fof(f40,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f39])).

fof(f83,plain,
    ( spl3_10
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f57,f43,f31,f81])).

fof(f31,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f43,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( r1_tarski(X0,X1)
        | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f57,plain,
    ( ! [X2,X0,X1] : r1_tarski(k4_xboole_0(k3_xboole_0(X0,X1),X2),X0)
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f32,f44])).

fof(f44,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
        | r1_tarski(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f43])).

fof(f32,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f31])).

fof(f45,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f41,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f37,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f16,f35])).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f33,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f29,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k4_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f24,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f13,f21])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (15425)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.45  % (15425)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f185,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(avatar_sat_refutation,[],[f24,f29,f33,f37,f41,f45,f83,f99,f152,f184])).
% 0.20/0.45  fof(f184,plain,(
% 0.20/0.45    spl3_2 | ~spl3_10 | ~spl3_16),
% 0.20/0.45    inference(avatar_contradiction_clause,[],[f183])).
% 0.20/0.45  fof(f183,plain,(
% 0.20/0.45    $false | (spl3_2 | ~spl3_10 | ~spl3_16)),
% 0.20/0.45    inference(subsumption_resolution,[],[f28,f180])).
% 0.20/0.45  fof(f180,plain,(
% 0.20/0.45    ( ! [X1] : (r1_tarski(k4_xboole_0(sK0,X1),sK1)) ) | (~spl3_10 | ~spl3_16)),
% 0.20/0.45    inference(superposition,[],[f82,f151])).
% 0.20/0.45  fof(f151,plain,(
% 0.20/0.45    sK0 = k3_xboole_0(sK1,sK0) | ~spl3_16),
% 0.20/0.45    inference(avatar_component_clause,[],[f149])).
% 0.20/0.45  fof(f149,plain,(
% 0.20/0.45    spl3_16 <=> sK0 = k3_xboole_0(sK1,sK0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.45  fof(f82,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k3_xboole_0(X0,X1),X2),X0)) ) | ~spl3_10),
% 0.20/0.45    inference(avatar_component_clause,[],[f81])).
% 0.20/0.45  fof(f81,plain,(
% 0.20/0.45    spl3_10 <=> ! [X1,X0,X2] : r1_tarski(k4_xboole_0(k3_xboole_0(X0,X1),X2),X0)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.45  fof(f28,plain,(
% 0.20/0.45    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) | spl3_2),
% 0.20/0.45    inference(avatar_component_clause,[],[f26])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    spl3_2 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.45  fof(f152,plain,(
% 0.20/0.45    spl3_16 | ~spl3_1 | ~spl3_12),
% 0.20/0.45    inference(avatar_split_clause,[],[f100,f97,f21,f149])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.45  fof(f97,plain,(
% 0.20/0.45    spl3_12 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3))),
% 0.20/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.45  fof(f100,plain,(
% 0.20/0.45    sK0 = k3_xboole_0(sK1,sK0) | (~spl3_1 | ~spl3_12)),
% 0.20/0.45    inference(unit_resulting_resolution,[],[f23,f98])).
% 0.20/0.45  fof(f98,plain,(
% 0.20/0.45    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | ~spl3_12),
% 0.20/0.45    inference(avatar_component_clause,[],[f97])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.20/0.45    inference(avatar_component_clause,[],[f21])).
% 0.20/0.45  fof(f99,plain,(
% 0.20/0.45    spl3_12 | ~spl3_4 | ~spl3_5),
% 0.20/0.45    inference(avatar_split_clause,[],[f52,f39,f35,f97])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f39,plain,(
% 0.20/0.46    spl3_5 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | (~spl3_4 | ~spl3_5)),
% 0.20/0.46    inference(superposition,[],[f40,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f35])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f39])).
% 0.20/0.46  fof(f83,plain,(
% 0.20/0.46    spl3_10 | ~spl3_3 | ~spl3_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f57,f43,f31,f81])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    spl3_3 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    spl3_6 <=> ! [X1,X0,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(k3_xboole_0(X0,X1),X2),X0)) ) | (~spl3_3 | ~spl3_6)),
% 0.20/0.46    inference(unit_resulting_resolution,[],[f32,f44])).
% 0.20/0.46  fof(f44,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) ) | ~spl3_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f43])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f31])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    spl3_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f43])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 0.20/0.46  fof(f41,plain,(
% 0.20/0.46    spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f18,f39])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl3_4),
% 0.20/0.46    inference(avatar_split_clause,[],[f16,f35])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f15,f31])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ~spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f14,f26])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (~r1_tarski(k4_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_tarski(k4_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.20/0.46    inference(negated_conjecture,[],[f6])).
% 0.20/0.46  fof(f6,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 0.20/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_xboole_1)).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f13,f21])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    r1_tarski(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f12])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (15425)------------------------------
% 0.20/0.46  % (15425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (15425)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (15425)Memory used [KB]: 6140
% 0.20/0.46  % (15425)Time elapsed: 0.036 s
% 0.20/0.46  % (15425)------------------------------
% 0.20/0.46  % (15425)------------------------------
% 0.20/0.46  % (15419)Success in time 0.101 s
%------------------------------------------------------------------------------
