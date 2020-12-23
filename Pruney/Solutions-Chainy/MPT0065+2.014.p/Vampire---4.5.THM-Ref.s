%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:19 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 102 expanded)
%              Number of leaves         :   19 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :  140 ( 229 expanded)
%              Number of equality atoms :   26 (  38 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f32,f36,f44,f51,f55,f62,f63,f69,f78,f117,f125,f126])).

fof(f126,plain,
    ( sK1 != k2_xboole_0(sK0,sK1)
    | sK0 != k2_xboole_0(sK0,sK1)
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK1,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f125,plain,
    ( spl3_17
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f118,f80,f123])).

fof(f123,plain,
    ( spl3_17
  <=> sK0 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f80,plain,
    ( spl3_11
  <=> sK0 = k2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f118,plain,
    ( sK0 = k2_xboole_0(sK0,sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f81,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f81,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f117,plain,
    ( spl3_11
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f85,f76,f49,f80])).

fof(f49,plain,
    ( spl3_5
  <=> sK2 = k2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f76,plain,
    ( spl3_10
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f85,plain,
    ( sK0 = k2_xboole_0(sK1,sK0)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f50,f77])).

fof(f77,plain,
    ( sK0 = sK2
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f50,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f49])).

fof(f78,plain,
    ( spl3_10
    | spl3_3
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f73,f67,f34,f76])).

fof(f34,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f67,plain,
    ( spl3_9
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f73,plain,
    ( sK0 = sK2
    | spl3_3
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f71,f35])).

fof(f35,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f34])).

fof(f71,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f68,f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f68,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f67])).

fof(f69,plain,
    ( spl3_9
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f65,f42,f30,f67])).

fof(f30,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f42,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f65,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f47,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f43,f17])).

fof(f17,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f43,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f42])).

fof(f63,plain,
    ( sK1 != sK2
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f62,plain,
    ( spl3_7
    | spl3_8
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f39,f30,f60,f57])).

fof(f57,plain,
    ( spl3_7
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f60,plain,
    ( spl3_8
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f39,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f31,f20])).

fof(f55,plain,
    ( spl3_6
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f45,f42,f53])).

fof(f53,plain,
    ( spl3_6
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f45,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f43,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f51,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f38,f30,f49])).

fof(f38,plain,
    ( sK2 = k2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f31,f21])).

fof(f44,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f37,f26,f42])).

fof(f26,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f37,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f27,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f27,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f36,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f32,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f30])).

fof(f15,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f28,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:58:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (24835)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.47  % (24825)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (24827)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.48  % (24832)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  % (24825)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f28,f32,f36,f44,f51,f55,f62,f63,f69,f78,f117,f125,f126])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    sK1 != k2_xboole_0(sK0,sK1) | sK0 != k2_xboole_0(sK0,sK1) | r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK1,sK2)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    spl3_17 | ~spl3_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f118,f80,f123])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    spl3_17 <=> sK0 = k2_xboole_0(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    spl3_11 <=> sK0 = k2_xboole_0(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    sK0 = k2_xboole_0(sK0,sK1) | ~spl3_11),
% 0.22/0.49    inference(superposition,[],[f81,f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    sK0 = k2_xboole_0(sK1,sK0) | ~spl3_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f80])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    spl3_11 | ~spl3_5 | ~spl3_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f85,f76,f49,f80])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl3_5 <=> sK2 = k2_xboole_0(sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl3_10 <=> sK0 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    sK0 = k2_xboole_0(sK1,sK0) | (~spl3_5 | ~spl3_10)),
% 0.22/0.49    inference(superposition,[],[f50,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    sK0 = sK2 | ~spl3_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    spl3_10 | spl3_3 | ~spl3_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f73,f67,f34,f76])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    spl3_3 <=> r2_xboole_0(sK0,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    spl3_9 <=> r1_tarski(sK0,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    sK0 = sK2 | (spl3_3 | ~spl3_9)),
% 0.22/0.49    inference(subsumption_resolution,[],[f71,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ~r2_xboole_0(sK0,sK2) | spl3_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f34])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    sK0 = sK2 | r2_xboole_0(sK0,sK2) | ~spl3_9),
% 0.22/0.49    inference(resolution,[],[f68,f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    r1_tarski(sK0,sK2) | ~spl3_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f67])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl3_9 | ~spl3_2 | ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f65,f42,f30,f67])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    spl3_4 <=> r1_tarski(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    r1_tarski(sK0,sK2) | (~spl3_2 | ~spl3_4)),
% 0.22/0.49    inference(resolution,[],[f47,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f30])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK0,X0)) ) | ~spl3_4),
% 0.22/0.49    inference(resolution,[],[f43,f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X2) | r1_tarski(X0,X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    r1_tarski(sK0,sK1) | ~spl3_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f42])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    sK1 != sK2 | r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK0,sK1)),
% 0.22/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl3_7 | spl3_8 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f39,f30,f60,f57])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    spl3_7 <=> r2_xboole_0(sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl3_8 <=> sK1 = sK2),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    sK1 = sK2 | r2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.49    inference(resolution,[],[f31,f20])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    spl3_6 | ~spl3_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f45,f42,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl3_6 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_4),
% 0.22/0.49    inference(resolution,[],[f43,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl3_5 | ~spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f38,f30,f49])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    sK2 = k2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.49    inference(resolution,[],[f31,f21])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    spl3_4 | ~spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f37,f26,f42])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    spl3_1 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.22/0.49    inference(resolution,[],[f27,f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    r2_xboole_0(sK0,sK1) | ~spl3_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f26])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ~spl3_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f34])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.22/0.49    inference(flattening,[],[f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.49    inference(negated_conjecture,[],[f6])).
% 0.22/0.49  fof(f6,conjecture,(
% 0.22/0.49    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    spl3_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f15,f30])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    r1_tarski(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    spl3_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f14,f26])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    r2_xboole_0(sK0,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (24825)------------------------------
% 0.22/0.49  % (24825)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (24825)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (24825)Memory used [KB]: 6140
% 0.22/0.49  % (24825)Time elapsed: 0.065 s
% 0.22/0.49  % (24825)------------------------------
% 0.22/0.49  % (24825)------------------------------
% 0.22/0.49  % (24824)Success in time 0.128 s
%------------------------------------------------------------------------------
