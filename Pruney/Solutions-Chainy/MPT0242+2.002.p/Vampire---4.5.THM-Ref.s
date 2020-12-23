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
% DateTime   : Thu Dec  3 12:37:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   24 (  36 expanded)
%              Number of leaves         :    4 (  13 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 (  73 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f17,f19,f22,f26])).

fof(f26,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f25])).

fof(f25,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f24,f15])).

fof(f15,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f14])).

fof(f14,plain,
    ( spl2_2
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f24,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_1 ),
    inference(resolution,[],[f8,f12])).

fof(f12,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f10])).

fof(f10,plain,
    ( spl2_1
  <=> r1_tarski(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f22,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f21])).

fof(f21,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f20,f11])).

fof(f11,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f10])).

fof(f20,plain,
    ( r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_2 ),
    inference(resolution,[],[f7,f16])).

fof(f16,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f14])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f19,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f18,f14,f10])).

fof(f18,plain,
    ( ~ r1_tarski(k1_tarski(sK0),sK1)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f6,f16])).

fof(f6,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f17,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f5,f14,f10])).

fof(f5,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (22046)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.46  % (22046)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (22059)lrs+1010_4:1_aac=none:add=off:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=on:gs=on:gsem=on:irw=on:nm=0:nwc=2.5:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f17,f19,f22,f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ~spl2_1 | spl2_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    $false | (~spl2_1 | spl2_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f24,f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK1) | spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f14])).
% 0.21/0.47  fof(f14,plain,(
% 0.21/0.47    spl2_2 <=> r2_hidden(sK0,sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | ~spl2_1),
% 0.21/0.47    inference(resolution,[],[f8,f12])).
% 0.21/0.47  fof(f12,plain,(
% 0.21/0.47    r1_tarski(k1_tarski(sK0),sK1) | ~spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f10])).
% 0.21/0.47  fof(f10,plain,(
% 0.21/0.47    spl2_1 <=> r1_tarski(k1_tarski(sK0),sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.47  fof(f8,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    spl2_1 | ~spl2_2),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    $false | (spl2_1 | ~spl2_2)),
% 0.21/0.47    inference(subsumption_resolution,[],[f20,f11])).
% 0.21/0.47  fof(f11,plain,(
% 0.21/0.47    ~r1_tarski(k1_tarski(sK0),sK1) | spl2_1),
% 0.21/0.47    inference(avatar_component_clause,[],[f10])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    r1_tarski(k1_tarski(sK0),sK1) | ~spl2_2),
% 0.21/0.47    inference(resolution,[],[f7,f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | ~spl2_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f14])).
% 0.21/0.47  fof(f7,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f1])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ~spl2_1 | ~spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f18,f14,f10])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ~r1_tarski(k1_tarski(sK0),sK1) | ~spl2_2),
% 0.21/0.47    inference(subsumption_resolution,[],[f6,f16])).
% 0.21/0.47  fof(f6,plain,(
% 0.21/0.47    ~r2_hidden(sK0,sK1) | ~r1_tarski(k1_tarski(sK0),sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,plain,(
% 0.21/0.47    ? [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,negated_conjecture,(
% 0.21/0.47    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.47    inference(negated_conjecture,[],[f2])).
% 0.21/0.47  fof(f2,conjecture,(
% 0.21/0.47    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    spl2_1 | spl2_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f5,f14,f10])).
% 0.21/0.47  fof(f5,plain,(
% 0.21/0.47    r2_hidden(sK0,sK1) | r1_tarski(k1_tarski(sK0),sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (22046)------------------------------
% 0.21/0.47  % (22046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (22046)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (22046)Memory used [KB]: 5373
% 0.21/0.47  % (22046)Time elapsed: 0.044 s
% 0.21/0.47  % (22046)------------------------------
% 0.21/0.47  % (22046)------------------------------
% 0.21/0.47  % (22038)Success in time 0.114 s
%------------------------------------------------------------------------------
