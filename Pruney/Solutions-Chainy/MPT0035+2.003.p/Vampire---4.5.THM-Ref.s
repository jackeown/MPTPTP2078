%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:44 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   25 (  38 expanded)
%              Number of leaves         :    5 (  12 expanded)
%              Depth                    :    8
%              Number of atoms          :   58 (  85 expanded)
%              Number of equality atoms :    8 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f64,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f48,f63])).

fof(f63,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f57])).

fof(f57,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(unit_resulting_resolution,[],[f7,f26,f31,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f31,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK0),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f29,plain,
    ( spl4_2
  <=> r2_hidden(sK2(sK0,sK1,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f26,plain,
    ( r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl4_1
  <=> r2_hidden(sK2(sK0,sK1,sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f7,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,plain,(
    ? [X0,X1] :
      ( k3_xboole_0(X0,X1) != X0
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(X0,X1)
       => k3_xboole_0(X0,X1) = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f48,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f39])).

fof(f39,plain,
    ( $false
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f8,f27,f27,f10])).

fof(f10,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f27,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f8,plain,(
    sK0 != k3_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f5])).

fof(f32,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f23,f29,f25])).

fof(f23,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK0),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0) ),
    inference(duplicate_literal_removal,[],[f22])).

fof(f22,plain,
    ( ~ r2_hidden(sK2(sK0,sK1,sK0),sK1)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0)
    | ~ r2_hidden(sK2(sK0,sK1,sK0),sK0) ),
    inference(equality_resolution,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( sK0 != X0
      | ~ r2_hidden(sK2(sK0,sK1,X0),sK1)
      | ~ r2_hidden(sK2(sK0,sK1,X0),X0)
      | ~ r2_hidden(sK2(sK0,sK1,X0),sK0) ) ),
    inference(superposition,[],[f8,f9])).

fof(f9,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X0,X1) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f2])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:53:22 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.21/0.54  % (30806)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.54  % (30782)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (30790)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (30779)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (30782)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f32,f48,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ~spl4_1 | spl4_2),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f57])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    $false | (~spl4_1 | spl4_2)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f7,f26,f31,f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,plain,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ~r2_hidden(sK2(sK0,sK1,sK0),sK1) | spl4_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    spl4_2 <=> r2_hidden(sK2(sK0,sK1,sK0),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    r2_hidden(sK2(sK0,sK1,sK0),sK0) | ~spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    spl4_1 <=> r2_hidden(sK2(sK0,sK1,sK0),sK0)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.55  fof(f7,plain,(
% 0.21/0.55    r1_tarski(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,plain,(
% 0.21/0.55    ? [X0,X1] : (k3_xboole_0(X0,X1) != X0 & r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    inference(negated_conjecture,[],[f3])).
% 0.21/0.55  fof(f3,conjecture,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    spl4_1),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    $false | spl4_1),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f8,f27,f27,f10])).
% 0.21/0.55  fof(f10,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X0) | k3_xboole_0(X0,X1) = X2) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ~r2_hidden(sK2(sK0,sK1,sK0),sK0) | spl4_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f25])).
% 0.21/0.55  fof(f8,plain,(
% 0.21/0.55    sK0 != k3_xboole_0(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ~spl4_1 | ~spl4_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f23,f29,f25])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ~r2_hidden(sK2(sK0,sK1,sK0),sK1) | ~r2_hidden(sK2(sK0,sK1,sK0),sK0)),
% 0.21/0.55    inference(duplicate_literal_removal,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ~r2_hidden(sK2(sK0,sK1,sK0),sK1) | ~r2_hidden(sK2(sK0,sK1,sK0),sK0) | ~r2_hidden(sK2(sK0,sK1,sK0),sK0)),
% 0.21/0.55    inference(equality_resolution,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ( ! [X0] : (sK0 != X0 | ~r2_hidden(sK2(sK0,sK1,X0),sK1) | ~r2_hidden(sK2(sK0,sK1,X0),X0) | ~r2_hidden(sK2(sK0,sK1,X0),sK0)) )),
% 0.21/0.55    inference(superposition,[],[f8,f9])).
% 0.21/0.55  fof(f9,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(X0,X1) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f2])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (30782)------------------------------
% 0.21/0.55  % (30782)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (30782)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (30782)Memory used [KB]: 6140
% 0.21/0.55  % (30782)Time elapsed: 0.138 s
% 0.21/0.55  % (30782)------------------------------
% 0.21/0.55  % (30782)------------------------------
% 0.21/0.55  % (30770)Success in time 0.191 s
%------------------------------------------------------------------------------
