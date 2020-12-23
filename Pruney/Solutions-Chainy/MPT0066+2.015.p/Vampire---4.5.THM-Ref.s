%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :    9 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 111 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f56,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f21,f26,f31,f49,f50,f55])).

fof(f55,plain,
    ( ~ spl3_2
    | spl3_3
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f54])).

fof(f54,plain,
    ( $false
    | ~ spl3_2
    | spl3_3
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f53,f30])).

fof(f30,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f53,plain,
    ( r2_xboole_0(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_5 ),
    inference(resolution,[],[f51,f25])).

fof(f25,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl3_2
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( ! [X0] :
        ( ~ r2_xboole_0(sK1,X0)
        | r2_xboole_0(sK0,X0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f44,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X2)
      | r2_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).

fof(f44,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_5
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f50,plain,
    ( sK0 != sK1
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f49,plain,
    ( spl3_5
    | spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f32,f18,f46,f42])).

fof(f46,plain,
    ( spl3_6
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f18,plain,
    ( spl3_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f32,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f20,f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f20,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f18])).

fof(f31,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f11,f28])).

fof(f11,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).

fof(f26,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f10,f23])).

fof(f10,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f21,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f9,f18])).

fof(f9,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.43  % (10898)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.43  % (10898)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.44  % (10915)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f21,f26,f31,f49,f50,f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    ~spl3_2 | spl3_3 | ~spl3_5),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f54])).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    $false | (~spl3_2 | spl3_3 | ~spl3_5)),
% 0.21/0.44    inference(subsumption_resolution,[],[f53,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ~r2_xboole_0(sK0,sK2) | spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    spl3_3 <=> r2_xboole_0(sK0,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    r2_xboole_0(sK0,sK2) | (~spl3_2 | ~spl3_5)),
% 0.21/0.44    inference(resolution,[],[f51,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    r2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    spl3_2 <=> r2_xboole_0(sK1,sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_xboole_0(sK1,X0) | r2_xboole_0(sK0,X0)) ) | ~spl3_5),
% 0.21/0.44    inference(resolution,[],[f44,f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X2) | r2_xboole_0(X0,X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r2_xboole_0(X1,X2) | ~r2_xboole_0(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f7])).
% 0.21/0.44  fof(f7,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r2_xboole_0(X1,X2) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_xboole_1)).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    r2_xboole_0(sK0,sK1) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    spl3_5 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f50,plain,(
% 0.21/0.44    sK0 != sK1 | r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK1,sK2)),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl3_5 | spl3_6 | ~spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f32,f18,f46,f42])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    spl3_6 <=> sK0 = sK1),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    spl3_1 <=> r1_tarski(sK0,sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.44    inference(resolution,[],[f20,f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f18])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f11,f28])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f5])).
% 0.21/0.44  fof(f5,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.44    inference(negated_conjecture,[],[f3])).
% 0.21/0.44  fof(f3,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f10,f23])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    r2_xboole_0(sK1,sK2)),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f9,f18])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (10898)------------------------------
% 0.21/0.44  % (10898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (10898)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (10898)Memory used [KB]: 10618
% 0.21/0.44  % (10898)Time elapsed: 0.049 s
% 0.21/0.44  % (10898)------------------------------
% 0.21/0.44  % (10898)------------------------------
% 0.21/0.44  % (10891)Success in time 0.091 s
%------------------------------------------------------------------------------
