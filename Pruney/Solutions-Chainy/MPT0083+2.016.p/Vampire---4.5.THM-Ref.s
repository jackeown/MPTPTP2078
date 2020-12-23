%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   59 (  98 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :  130 ( 212 expanded)
%              Number of equality atoms :    5 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f37,f43,f48,f53,f58,f64,f71,f74])).

fof(f74,plain,
    ( ~ spl3_4
    | ~ spl3_7
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f73])).

fof(f73,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_7
    | spl3_9 ),
    inference(subsumption_resolution,[],[f72,f42])).

fof(f42,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl3_4
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f72,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | ~ spl3_7
    | spl3_9 ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(X1,k4_xboole_0(X0,X2))
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl3_7
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,k4_xboole_0(X0,X2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f70,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl3_9
  <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f71,plain,
    ( ~ spl3_9
    | ~ spl3_6
    | spl3_8 ),
    inference(avatar_split_clause,[],[f65,f61,f51,f68])).

fof(f51,plain,
    ( spl3_6
  <=> ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X0,X2),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f61,plain,
    ( spl3_8
  <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f65,plain,
    ( ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | ~ spl3_6
    | spl3_8 ),
    inference(resolution,[],[f63,f52])).

fof(f52,plain,
    ( ! [X2,X0,X1] :
        ( r1_xboole_0(k4_xboole_0(X0,X2),X1)
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f63,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f61])).

fof(f64,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f24,f61])).

fof(f24,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f18,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f23,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(backward_demodulation,[],[f21,f22])).

fof(f21,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1))) ),
    inference(definition_unfolding,[],[f15,f18,f18])).

fof(f15,plain,(
    ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
    & r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
        & r1_xboole_0(X0,X1) )
   => ( ~ r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))
      & r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1))
      & r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_xboole_0(X0,X1)
       => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

fof(f58,plain,
    ( spl3_7
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f54,f51,f35,f56])).

fof(f35,plain,
    ( spl3_3
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f54,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,k4_xboole_0(X0,X2)) )
    | ~ spl3_3
    | ~ spl3_6 ),
    inference(resolution,[],[f52,f36])).

fof(f36,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f53,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f49,f46,f31,f51])).

fof(f31,plain,
    ( spl3_2
  <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( spl3_5
  <=> ! [X1,X0,X2] :
        ( r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X1,X2)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f49,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(k4_xboole_0(X0,X2),X1) )
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,
    ( ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f47,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | ~ r1_xboole_0(X1,X2)
        | r1_xboole_0(X0,X2) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f48,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f43,plain,
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f38,f35,f26,f40])).

fof(f26,plain,
    ( spl3_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f38,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(resolution,[],[f36,f28])).

fof(f28,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f37,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f19,f35])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:59 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.20/0.45  % (5513)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (5524)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (5510)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (5516)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.46  % (5516)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(avatar_sat_refutation,[],[f29,f33,f37,f43,f48,f53,f58,f64,f71,f74])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ~spl3_4 | ~spl3_7 | spl3_9),
% 0.20/0.46    inference(avatar_contradiction_clause,[],[f73])).
% 0.20/0.46  fof(f73,plain,(
% 0.20/0.46    $false | (~spl3_4 | ~spl3_7 | spl3_9)),
% 0.20/0.46    inference(subsumption_resolution,[],[f72,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    r1_xboole_0(sK1,sK0) | ~spl3_4),
% 0.20/0.46    inference(avatar_component_clause,[],[f40])).
% 0.20/0.46  fof(f40,plain,(
% 0.20/0.46    spl3_4 <=> r1_xboole_0(sK1,sK0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.46  fof(f72,plain,(
% 0.20/0.46    ~r1_xboole_0(sK1,sK0) | (~spl3_7 | spl3_9)),
% 0.20/0.46    inference(resolution,[],[f70,f57])).
% 0.20/0.46  fof(f57,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_xboole_0(X1,k4_xboole_0(X0,X2)) | ~r1_xboole_0(X0,X1)) ) | ~spl3_7),
% 0.20/0.46    inference(avatar_component_clause,[],[f56])).
% 0.20/0.46  fof(f56,plain,(
% 0.20/0.46    spl3_7 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,k4_xboole_0(X0,X2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.46  fof(f70,plain,(
% 0.20/0.46    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_9),
% 0.20/0.46    inference(avatar_component_clause,[],[f68])).
% 0.20/0.46  fof(f68,plain,(
% 0.20/0.46    spl3_9 <=> r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ~spl3_9 | ~spl3_6 | spl3_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f65,f61,f51,f68])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    spl3_6 <=> ! [X1,X0,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X0,X2),X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    spl3_8 <=> r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | (~spl3_6 | spl3_8)),
% 0.20/0.46    inference(resolution,[],[f63,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X2),X1) | ~r1_xboole_0(X0,X1)) ) | ~spl3_6),
% 0.20/0.46    inference(avatar_component_clause,[],[f51])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) | spl3_8),
% 0.20/0.46    inference(avatar_component_clause,[],[f61])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    ~spl3_8),
% 0.20/0.46    inference(avatar_split_clause,[],[f24,f61])).
% 0.20/0.46  fof(f24,plain,(
% 0.20/0.46    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.46    inference(forward_demodulation,[],[f23,f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.46    inference(definition_unfolding,[],[f17,f18,f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f4])).
% 0.20/0.46  fof(f4,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.46    inference(backward_demodulation,[],[f21,f22])).
% 0.20/0.46  fof(f21,plain,(
% 0.20/0.46    ~r1_xboole_0(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK2,k4_xboole_0(sK2,sK1)))),
% 0.20/0.46    inference(definition_unfolding,[],[f15,f18,f18])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  fof(f13,plain,(
% 0.20/0.46    ~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f12])).
% 0.20/0.46  fof(f12,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1)) => (~r1_xboole_0(k3_xboole_0(sK2,sK0),k3_xboole_0(sK2,sK1)) & r1_xboole_0(sK0,sK1))),
% 0.20/0.46    introduced(choice_axiom,[])).
% 0.20/0.46  fof(f8,plain,(
% 0.20/0.46    ? [X0,X1,X2] : (~r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)) & r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f7])).
% 0.20/0.46  fof(f7,negated_conjecture,(
% 0.20/0.46    ~! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.20/0.46    inference(negated_conjecture,[],[f6])).
% 0.20/0.46  fof(f6,conjecture,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X1) => r1_xboole_0(k3_xboole_0(X2,X0),k3_xboole_0(X2,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    spl3_7 | ~spl3_3 | ~spl3_6),
% 0.20/0.46    inference(avatar_split_clause,[],[f54,f51,f35,f56])).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    spl3_3 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,k4_xboole_0(X0,X2))) ) | (~spl3_3 | ~spl3_6)),
% 0.20/0.46    inference(resolution,[],[f52,f36])).
% 0.20/0.46  fof(f36,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_3),
% 0.20/0.46    inference(avatar_component_clause,[],[f35])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    spl3_6 | ~spl3_2 | ~spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f49,f46,f31,f51])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    spl3_2 <=> ! [X1,X0] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    spl3_5 <=> ! [X1,X0,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.46  fof(f49,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(k4_xboole_0(X0,X2),X1)) ) | (~spl3_2 | ~spl3_5)),
% 0.20/0.46    inference(resolution,[],[f47,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) ) | ~spl3_2),
% 0.20/0.46    inference(avatar_component_clause,[],[f31])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) ) | ~spl3_5),
% 0.20/0.46    inference(avatar_component_clause,[],[f46])).
% 0.20/0.46  fof(f48,plain,(
% 0.20/0.46    spl3_5),
% 0.20/0.46    inference(avatar_split_clause,[],[f20,f46])).
% 0.20/0.46  fof(f20,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f10])).
% 0.20/0.46  fof(f10,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.20/0.46  fof(f43,plain,(
% 0.20/0.46    spl3_4 | ~spl3_1 | ~spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f38,f35,f26,f40])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    spl3_1 <=> r1_xboole_0(sK0,sK1)),
% 0.20/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    r1_xboole_0(sK1,sK0) | (~spl3_1 | ~spl3_3)),
% 0.20/0.46    inference(resolution,[],[f36,f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK1) | ~spl3_1),
% 0.20/0.46    inference(avatar_component_clause,[],[f26])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    spl3_3),
% 0.20/0.46    inference(avatar_split_clause,[],[f19,f35])).
% 0.20/0.46  fof(f19,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f9])).
% 0.20/0.46  fof(f9,plain,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.20/0.46  fof(f33,plain,(
% 0.20/0.46    spl3_2),
% 0.20/0.46    inference(avatar_split_clause,[],[f16,f31])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    spl3_1),
% 0.20/0.46    inference(avatar_split_clause,[],[f14,f26])).
% 0.20/0.46  fof(f14,plain,(
% 0.20/0.46    r1_xboole_0(sK0,sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f13])).
% 0.20/0.46  % SZS output end Proof for theBenchmark
% 0.20/0.46  % (5516)------------------------------
% 0.20/0.46  % (5516)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.46  % (5516)Termination reason: Refutation
% 0.20/0.46  
% 0.20/0.46  % (5516)Memory used [KB]: 6140
% 0.20/0.46  % (5516)Time elapsed: 0.058 s
% 0.20/0.46  % (5516)------------------------------
% 0.20/0.46  % (5516)------------------------------
% 0.20/0.46  % (5508)Success in time 0.108 s
%------------------------------------------------------------------------------
