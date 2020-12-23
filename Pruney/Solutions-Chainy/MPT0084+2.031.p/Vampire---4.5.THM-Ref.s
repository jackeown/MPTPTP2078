%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:18 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 146 expanded)
%              Number of leaves         :   16 (  57 expanded)
%              Depth                    :    9
%              Number of atoms          :  141 ( 304 expanded)
%              Number of equality atoms :   18 (  58 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f487,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f53,f107,f115,f135,f439,f466,f486])).

fof(f486,plain,
    ( ~ spl4_14
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f485])).

fof(f485,plain,
    ( $false
    | ~ spl4_14
    | ~ spl4_26 ),
    inference(global_subsumption,[],[f25,f473])).

fof(f473,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl4_14
    | ~ spl4_26 ),
    inference(forward_demodulation,[],[f468,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f468,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))
    | ~ spl4_14
    | ~ spl4_26 ),
    inference(unit_resulting_resolution,[],[f134,f465])).

fof(f465,plain,
    ( ! [X2,X3] :
        ( ~ r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X2)))
        | ~ r2_hidden(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,X2))) )
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl4_26
  <=> ! [X3,X2] :
        ( ~ r2_hidden(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,X2)))
        | ~ r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f134,plain,
    ( r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_14
  <=> r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f25,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f18,f20])).

fof(f18,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f466,plain,
    ( spl4_26
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f444,f437,f464])).

fof(f437,plain,
    ( spl4_25
  <=> ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f444,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,X2)))
        | ~ r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) )
    | ~ spl4_25 ),
    inference(superposition,[],[f27,f438])).

fof(f438,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f437])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).

fof(f14,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f439,plain,
    ( spl4_25
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f370,f50,f437])).

fof(f50,plain,
    ( spl4_4
  <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f370,plain,
    ( ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))
    | ~ spl4_4 ),
    inference(superposition,[],[f30,f52])).

fof(f52,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f50])).

fof(f30,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) ),
    inference(definition_unfolding,[],[f24,f20,f20,f20,f20])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f135,plain,
    ( spl4_14
    | spl4_12 ),
    inference(avatar_split_clause,[],[f117,f112,f132])).

fof(f112,plain,
    ( spl4_12
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f117,plain,
    ( r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl4_12 ),
    inference(forward_demodulation,[],[f116,f26])).

fof(f116,plain,
    ( r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)))
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f114,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f21,f20])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f114,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f115,plain,
    ( ~ spl4_12
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f108,f104,f112])).

fof(f104,plain,
    ( spl4_11
  <=> r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f108,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f106,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) ),
    inference(superposition,[],[f27,f26])).

fof(f106,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f104])).

fof(f107,plain,
    ( spl4_11
    | spl4_1 ),
    inference(avatar_split_clause,[],[f84,f32,f104])).

fof(f32,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f84,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f34,f28])).

fof(f34,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f53,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f47,f37,f50])).

fof(f37,plain,
    ( spl4_2
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f47,plain,
    ( sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f39,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f39,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f40,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f35,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f16,f32])).

fof(f16,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.42  % (3978)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.43  % (3978)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f487,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f35,f40,f53,f107,f115,f135,f439,f466,f486])).
% 0.20/0.43  fof(f486,plain,(
% 0.20/0.43    ~spl4_14 | ~spl4_26),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f485])).
% 0.20/0.43  fof(f485,plain,(
% 0.20/0.43    $false | (~spl4_14 | ~spl4_26)),
% 0.20/0.43    inference(global_subsumption,[],[f25,f473])).
% 0.20/0.43  fof(f473,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | (~spl4_14 | ~spl4_26)),
% 0.20/0.43    inference(forward_demodulation,[],[f468,f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f19,f20,f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.43  fof(f19,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.43  fof(f468,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) | (~spl4_14 | ~spl4_26)),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f134,f465])).
% 0.20/0.43  fof(f465,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X2))) | ~r2_hidden(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,X2)))) ) | ~spl4_26),
% 0.20/0.43    inference(avatar_component_clause,[],[f464])).
% 0.20/0.43  fof(f464,plain,(
% 0.20/0.43    spl4_26 <=> ! [X3,X2] : (~r2_hidden(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,X2))) | ~r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X2))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.20/0.43  fof(f134,plain,(
% 0.20/0.43    r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl4_14),
% 0.20/0.43    inference(avatar_component_clause,[],[f132])).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    spl4_14 <=> r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.43    inference(definition_unfolding,[],[f18,f20])).
% 0.20/0.43  fof(f18,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,plain,(
% 0.20/0.43    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.20/0.43  fof(f12,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f9,plain,(
% 0.20/0.43    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,negated_conjecture,(
% 0.20/0.43    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.43    inference(negated_conjecture,[],[f6])).
% 0.20/0.43  fof(f6,conjecture,(
% 0.20/0.43    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.43  fof(f466,plain,(
% 0.20/0.43    spl4_26 | ~spl4_25),
% 0.20/0.43    inference(avatar_split_clause,[],[f444,f437,f464])).
% 0.20/0.43  fof(f437,plain,(
% 0.20/0.43    spl4_25 <=> ! [X0] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.20/0.43  fof(f444,plain,(
% 0.20/0.43    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(sK0,k4_xboole_0(sK0,X2))) | ~r1_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X2)))) ) | ~spl4_25),
% 0.20/0.43    inference(superposition,[],[f27,f438])).
% 0.20/0.43  fof(f438,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ) | ~spl4_25),
% 0.20/0.43    inference(avatar_component_clause,[],[f437])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f22,f20])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,plain,(
% 0.20/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f10,f14])).
% 0.20/0.43  fof(f14,plain,(
% 0.20/0.43    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f10,plain,(
% 0.20/0.43    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,plain,(
% 0.20/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.43    inference(rectify,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.20/0.43  fof(f439,plain,(
% 0.20/0.43    spl4_25 | ~spl4_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f370,f50,f437])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    spl4_4 <=> sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.43  fof(f370,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,k4_xboole_0(sK2,X0)))) = k4_xboole_0(sK0,k4_xboole_0(sK0,X0))) ) | ~spl4_4),
% 0.20/0.43    inference(superposition,[],[f30,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f50])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f24,f20,f20,f20,f20])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    spl4_14 | spl4_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f117,f112,f132])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    spl4_12 <=> r1_xboole_0(sK1,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.43  fof(f117,plain,(
% 0.20/0.43    r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl4_12),
% 0.20/0.43    inference(forward_demodulation,[],[f116,f26])).
% 0.20/0.43  fof(f116,plain,(
% 0.20/0.43    r2_hidden(sK3(sK1,sK0),k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))) | spl4_12),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f114,f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f21,f20])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f15])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    ~r1_xboole_0(sK1,sK0) | spl4_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f112])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    ~spl4_12 | ~spl4_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f108,f104,f112])).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    spl4_11 <=> r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    ~r1_xboole_0(sK1,sK0) | ~spl4_11),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f106,f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 0.20/0.43    inference(superposition,[],[f27,f26])).
% 0.20/0.43  fof(f106,plain,(
% 0.20/0.43    r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~spl4_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f104])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl4_11 | spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f84,f32,f104])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    r2_hidden(sK3(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl4_1),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f34,f28])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,sK1) | spl4_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f32])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    spl4_4 | ~spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f47,f37,f50])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    spl4_2 <=> r1_tarski(sK0,sK2)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) | ~spl4_2),
% 0.20/0.43    inference(unit_resulting_resolution,[],[f39,f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f23,f20])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,plain,(
% 0.20/0.43    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    r1_tarski(sK0,sK2) | ~spl4_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f37])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    spl4_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f17,f37])).
% 0.20/0.43  fof(f17,plain,(
% 0.20/0.43    r1_tarski(sK0,sK2)),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ~spl4_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f16,f32])).
% 0.20/0.43  fof(f16,plain,(
% 0.20/0.43    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.43    inference(cnf_transformation,[],[f13])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (3978)------------------------------
% 0.20/0.43  % (3978)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (3978)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (3978)Memory used [KB]: 11001
% 0.20/0.43  % (3978)Time elapsed: 0.015 s
% 0.20/0.43  % (3978)------------------------------
% 0.20/0.43  % (3978)------------------------------
% 0.20/0.43  % (3960)Success in time 0.079 s
%------------------------------------------------------------------------------
