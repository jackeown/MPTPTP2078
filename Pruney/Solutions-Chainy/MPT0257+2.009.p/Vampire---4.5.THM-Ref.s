%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   49 (  80 expanded)
%              Number of leaves         :   13 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 163 expanded)
%              Number of equality atoms :   44 (  72 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f153,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f116,f128,f151,f152])).

fof(f152,plain,
    ( sK0 != sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f151,plain,
    ( ~ spl4_1
    | ~ spl4_7
    | spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f145,f125,f57,f148,f52])).

fof(f52,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f148,plain,
    ( spl4_7
  <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f57,plain,
    ( spl4_2
  <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f125,plain,
    ( spl4_6
  <=> sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f145,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,sK1)
    | spl4_2
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f144])).

fof(f144,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,sK1)
    | spl4_2
    | ~ spl4_6 ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,
    ( ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ r2_hidden(sK0,sK1)
    | spl4_2
    | ~ spl4_6 ),
    inference(superposition,[],[f64,f127])).

fof(f127,plain,
    ( sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_enumset1(sK0,sK0,sK0,sK0))
        | k2_enumset1(sK0,sK0,sK0,sK0) != X0
        | ~ r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),X0)
        | ~ r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),sK1) )
    | spl4_2 ),
    inference(superposition,[],[f59,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | ~ r2_hidden(sK2(X0,X1,X2),X0) ) ),
    inference(definition_unfolding,[],[f16,f14])).

fof(f14,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1,X2),X0)
      | ~ r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f59,plain,
    ( k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f128,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f122,f113,f125])).

fof(f113,plain,
    ( spl4_5
  <=> r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f122,plain,
    ( sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_5 ),
    inference(duplicate_literal_removal,[],[f117])).

fof(f117,plain,
    ( sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_5 ),
    inference(resolution,[],[f115,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_enumset1(X0,X0,X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_enumset1(X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f25,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f13,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f13,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f115,plain,
    ( r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f116,plain,
    ( spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f100,f57,f113])).

fof(f100,plain,
    ( r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | spl4_2 ),
    inference(trivial_inequality_removal,[],[f95])).

fof(f95,plain,
    ( r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))
    | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0)
    | spl4_2 ),
    inference(factoring,[],[f66])).

fof(f66,plain,
    ( ! [X2] :
        ( r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X2),k2_enumset1(sK0,sK0,sK0,sK0))
        | r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X2),X2)
        | k2_enumset1(sK0,sK0,sK0,sK0) != X2 )
    | spl4_2 ),
    inference(superposition,[],[f59,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2
      | r2_hidden(sK2(X0,X1,X2),X2)
      | r2_hidden(sK2(X0,X1,X2),X1) ) ),
    inference(definition_unfolding,[],[f18,f14])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | r2_hidden(sK2(X0,X1,X2),X2)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f60,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f11,f29,f14,f29])).

fof(f29,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f12,f28])).

fof(f12,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f11,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0))
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).

fof(f55,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f10,f52])).

fof(f10,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:39:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.49  % (21588)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.50  % (21604)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.50  % (21580)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (21596)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.51  % (21581)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (21583)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.52  % (21598)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (21576)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (21597)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (21605)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (21590)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (21590)Refutation not found, incomplete strategy% (21590)------------------------------
% 0.20/0.52  % (21590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21590)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (21590)Memory used [KB]: 1663
% 0.20/0.52  % (21590)Time elapsed: 0.078 s
% 0.20/0.52  % (21590)------------------------------
% 0.20/0.52  % (21590)------------------------------
% 0.20/0.52  % (21587)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.52  % (21604)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f55,f60,f116,f128,f151,f152])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    sK0 != sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f151,plain,(
% 0.20/0.52    ~spl4_1 | ~spl4_7 | spl4_2 | ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f145,f125,f57,f148,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    spl4_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f148,plain,(
% 0.20/0.52    spl4_7 <=> r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl4_2 <=> k2_enumset1(sK0,sK0,sK0,sK0) = k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f125,plain,(
% 0.20/0.52    spl4_6 <=> sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,sK1) | (spl4_2 | ~spl4_6)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f144])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,sK1) | (spl4_2 | ~spl4_6)),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f138])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,k2_enumset1(sK0,sK0,sK0,sK0)) | ~r2_hidden(sK0,sK1) | (spl4_2 | ~spl4_6)),
% 0.20/0.52    inference(superposition,[],[f64,f127])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f125])).
% 0.20/0.52  fof(f64,plain,(
% 0.20/0.52    ( ! [X0] : (~r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) != X0 | ~r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),X0) | ~r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X0),sK1)) ) | spl4_2),
% 0.20/0.52    inference(superposition,[],[f59,f36])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | ~r2_hidden(sK2(X0,X1,X2),X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f16,f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK2(X0,X1,X2),X0) | ~r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.20/0.52  fof(f59,plain,(
% 0.20/0.52    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0))) | spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f57])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    spl4_6 | ~spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f122,f113,f125])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    spl4_5 <=> r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_5),
% 0.20/0.52    inference(duplicate_literal_removal,[],[f117])).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | sK0 = sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_5),
% 0.20/0.52    inference(resolution,[],[f115,f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_enumset1(X0,X0,X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.20/0.52    inference(equality_resolution,[],[f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_enumset1(X0,X0,X0,X1) != X2) )),
% 0.20/0.52    inference(definition_unfolding,[],[f25,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f13,f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | ~spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f113])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    spl4_5 | spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f100,f57,f113])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | spl4_2),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f95])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK0,sK0,sK0,sK0)),k2_enumset1(sK0,sK0,sK0,sK0)) | k2_enumset1(sK0,sK0,sK0,sK0) != k2_enumset1(sK0,sK0,sK0,sK0) | spl4_2),
% 0.20/0.52    inference(factoring,[],[f66])).
% 0.20/0.52  fof(f66,plain,(
% 0.20/0.52    ( ! [X2] : (r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X2),k2_enumset1(sK0,sK0,sK0,sK0)) | r2_hidden(sK2(sK1,k2_enumset1(sK0,sK0,sK0,sK0),X2),X2) | k2_enumset1(sK0,sK0,sK0,sK0) != X2) ) | spl4_2),
% 0.20/0.52    inference(superposition,[],[f59,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X2 | r2_hidden(sK2(X0,X1,X2),X2) | r2_hidden(sK2(X0,X1,X2),X1)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f18,f14])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | r2_hidden(sK2(X0,X1,X2),X2) | k3_xboole_0(X0,X1) = X2) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f30,f57])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    k2_enumset1(sK0,sK0,sK0,sK0) != k4_xboole_0(sK1,k4_xboole_0(sK1,k2_enumset1(sK0,sK0,sK0,sK0)))),
% 0.20/0.52    inference(definition_unfolding,[],[f11,f29,f14,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 0.20/0.52    inference(definition_unfolding,[],[f12,f28])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,plain,(
% 0.20/0.52    ? [X0,X1] : (k1_tarski(X0) != k3_xboole_0(X1,k1_tarski(X0)) & r2_hidden(X0,X1))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,negated_conjecture,(
% 0.20/0.52    ~! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.20/0.52    inference(negated_conjecture,[],[f7])).
% 0.20/0.52  fof(f7,conjecture,(
% 0.20/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_zfmisc_1)).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f10,f52])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    r2_hidden(sK0,sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f9])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (21604)------------------------------
% 0.20/0.52  % (21604)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (21604)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (21604)Memory used [KB]: 10746
% 0.20/0.52  % (21604)Time elapsed: 0.121 s
% 0.20/0.52  % (21604)------------------------------
% 0.20/0.52  % (21604)------------------------------
% 0.20/0.52  % (21589)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (21575)Success in time 0.17 s
%------------------------------------------------------------------------------
