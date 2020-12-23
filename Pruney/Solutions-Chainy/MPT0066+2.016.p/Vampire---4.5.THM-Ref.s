%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:22 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   33 (  64 expanded)
%              Number of leaves         :    6 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 187 expanded)
%              Number of equality atoms :    9 (  15 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f44,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f43])).

fof(f43,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f42])).

fof(f42,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f41,f15])).

fof(f15,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

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

fof(f41,plain,
    ( r2_xboole_0(sK0,sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f38,f25])).

fof(f25,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f38,plain,(
    ! [X0] :
      ( ~ r2_xboole_0(X0,sK1)
      | r2_xboole_0(X0,sK2) ) ),
    inference(resolution,[],[f21,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r2_xboole_0(X0,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( r2_xboole_0(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f21,plain,(
    r1_tarski(sK1,sK2) ),
    inference(resolution,[],[f16,f14])).

fof(f14,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f34,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f33])).

fof(f33,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f32,f15])).

fof(f32,plain,
    ( r2_xboole_0(sK0,sK2)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f14,f28])).

fof(f28,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl3_2
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f29,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f22,f27,f24])).

fof(f22,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f18,f13])).

fof(f13,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:29:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.21/0.45  % (9728)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.45  % (9725)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.45  % (9744)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.46  % (9728)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f44,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f29,f34,f43])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f42])).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    $false | ~spl3_1),
% 0.21/0.46    inference(subsumption_resolution,[],[f41,f15])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f5])).
% 0.21/0.46  fof(f5,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f4])).
% 0.21/0.46  fof(f4,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.46    inference(negated_conjecture,[],[f3])).
% 0.21/0.46  fof(f3,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_xboole_1)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    r2_xboole_0(sK0,sK2) | ~spl3_1),
% 0.21/0.46    inference(resolution,[],[f38,f25])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    r2_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f24])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    spl3_1 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ( ! [X0] : (~r2_xboole_0(X0,sK1) | r2_xboole_0(X0,sK2)) )),
% 0.21/0.46    inference(resolution,[],[f21,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r2_xboole_0(X0,X2) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | ~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f7])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r2_xboole_0(X0,X2) | (~r1_tarski(X1,X2) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    r1_tarski(sK1,sK2)),
% 0.21/0.46    inference(resolution,[],[f16,f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    r2_xboole_0(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.46    inference(flattening,[],[f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.46  fof(f34,plain,(
% 0.21/0.46    ~spl3_2),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f33])).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    $false | ~spl3_2),
% 0.21/0.46    inference(subsumption_resolution,[],[f32,f15])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    r2_xboole_0(sK0,sK2) | ~spl3_2),
% 0.21/0.46    inference(backward_demodulation,[],[f14,f28])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    sK0 = sK1 | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    spl3_2 <=> sK0 = sK1),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    spl3_1 | spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f27,f24])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    sK0 = sK1 | r2_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(resolution,[],[f18,f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    r1_tarski(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (9728)------------------------------
% 0.21/0.46  % (9728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (9728)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (9728)Memory used [KB]: 10618
% 0.21/0.46  % (9728)Time elapsed: 0.052 s
% 0.21/0.46  % (9728)------------------------------
% 0.21/0.46  % (9728)------------------------------
% 0.21/0.46  % (9742)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (9722)Success in time 0.111 s
%------------------------------------------------------------------------------
