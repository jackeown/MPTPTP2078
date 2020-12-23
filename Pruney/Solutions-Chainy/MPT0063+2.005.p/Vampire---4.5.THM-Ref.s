%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  85 expanded)
%              Number of leaves         :   14 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :  124 ( 228 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f57,f65,f70,f80,f89,f90])).

fof(f90,plain,
    ( sK0 != sK2
    | r2_xboole_0(sK2,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f89,plain,
    ( spl3_9
    | spl3_1
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f88,f77,f25,f84])).

fof(f84,plain,
    ( spl3_9
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f25,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f77,plain,
    ( spl3_8
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f88,plain,
    ( sK0 = sK2
    | spl3_1
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f82,f27])).

fof(f27,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f25])).

fof(f82,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f79,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f79,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f80,plain,
    ( spl3_8
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f74,f67,f62,f77])).

fof(f62,plain,
    ( spl3_6
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f67,plain,
    ( spl3_7
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f74,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_6
    | ~ spl3_7 ),
    inference(unit_resulting_resolution,[],[f64,f69,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f69,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f67])).

fof(f64,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f70,plain,
    ( spl3_7
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f59,f30,f67])).

fof(f30,plain,
    ( spl3_2
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f32,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f32,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f65,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f60,f35,f62])).

fof(f35,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f60,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f37,f19])).

fof(f37,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f57,plain,
    ( ~ spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f43,f30,f51])).

fof(f51,plain,
    ( spl3_5
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f43,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl3_2 ),
    inference(resolution,[],[f18,f32])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f15,f35])).

fof(f15,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r2_xboole_0(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r2_xboole_0(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r2_xboole_0(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_xboole_0(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_xboole_0(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).

fof(f33,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    r2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f12])).

fof(f28,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f17,f25])).

fof(f17,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:24:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.44  % (31924)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.45  % (31940)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.45  % (31924)Refutation not found, incomplete strategy% (31924)------------------------------
% 0.21/0.45  % (31924)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (31924)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.45  
% 0.21/0.45  % (31924)Memory used [KB]: 6012
% 0.21/0.45  % (31924)Time elapsed: 0.056 s
% 0.21/0.45  % (31924)------------------------------
% 0.21/0.45  % (31924)------------------------------
% 0.21/0.46  % (31930)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.46  % (31940)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f91,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f28,f33,f38,f57,f65,f70,f80,f89,f90])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    sK0 != sK2 | r2_xboole_0(sK2,sK1) | ~r2_xboole_0(sK0,sK1)),
% 0.21/0.46    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl3_9 | spl3_1 | ~spl3_8),
% 0.21/0.46    inference(avatar_split_clause,[],[f88,f77,f25,f84])).
% 0.21/0.46  fof(f84,plain,(
% 0.21/0.46    spl3_9 <=> sK0 = sK2),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    spl3_1 <=> r2_xboole_0(sK0,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    spl3_8 <=> r1_tarski(sK0,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    sK0 = sK2 | (spl3_1 | ~spl3_8)),
% 0.21/0.46    inference(subsumption_resolution,[],[f82,f27])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ~r2_xboole_0(sK0,sK2) | spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f25])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    sK0 = sK2 | r2_xboole_0(sK0,sK2) | ~spl3_8),
% 0.21/0.46    inference(resolution,[],[f79,f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f14,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.46    inference(flattening,[],[f13])).
% 0.21/0.46  fof(f13,plain,(
% 0.21/0.46    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.21/0.46    inference(nnf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.46  fof(f79,plain,(
% 0.21/0.46    r1_tarski(sK0,sK2) | ~spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f77])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl3_8 | ~spl3_6 | ~spl3_7),
% 0.21/0.46    inference(avatar_split_clause,[],[f74,f67,f62,f77])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl3_6 <=> r1_tarski(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f67,plain,(
% 0.21/0.46    spl3_7 <=> r1_tarski(sK1,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.46  fof(f74,plain,(
% 0.21/0.46    r1_tarski(sK0,sK2) | (~spl3_6 | ~spl3_7)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f64,f69,f22])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f10])).
% 0.21/0.46  fof(f10,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f9])).
% 0.21/0.46  fof(f9,plain,(
% 0.21/0.46    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.46  fof(f69,plain,(
% 0.21/0.46    r1_tarski(sK1,sK2) | ~spl3_7),
% 0.21/0.46    inference(avatar_component_clause,[],[f67])).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    r1_tarski(sK0,sK1) | ~spl3_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f62])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    spl3_7 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f59,f30,f67])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    spl3_2 <=> r2_xboole_0(sK1,sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f32,f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f14])).
% 0.21/0.46  fof(f32,plain,(
% 0.21/0.46    r2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f30])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    spl3_6 | ~spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f60,f35,f62])).
% 0.21/0.46  fof(f35,plain,(
% 0.21/0.46    spl3_3 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    r1_tarski(sK0,sK1) | ~spl3_3),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f37,f19])).
% 0.21/0.46  fof(f37,plain,(
% 0.21/0.46    r2_xboole_0(sK0,sK1) | ~spl3_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f35])).
% 0.21/0.46  fof(f57,plain,(
% 0.21/0.46    ~spl3_5 | ~spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f43,f30,f51])).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl3_5 <=> r2_xboole_0(sK2,sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    ~r2_xboole_0(sK2,sK1) | ~spl3_2),
% 0.21/0.46    inference(resolution,[],[f18,f32])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f8])).
% 0.21/0.46  fof(f8,plain,(
% 0.21/0.46    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl3_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f15,f35])).
% 0.21/0.46  fof(f15,plain,(
% 0.21/0.46    r2_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,plain,(
% 0.21/0.46    ~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f7,f11])).
% 0.21/0.46  fof(f11,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r2_xboole_0(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f7,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1))),
% 0.21/0.46    inference(flattening,[],[f6])).
% 0.21/0.46  fof(f6,plain,(
% 0.21/0.46    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.21/0.46    inference(ennf_transformation,[],[f5])).
% 0.21/0.46  fof(f5,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.46    inference(negated_conjecture,[],[f4])).
% 0.21/0.46  fof(f4,conjecture,(
% 0.21/0.46    ! [X0,X1,X2] : ((r2_xboole_0(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_xboole_1)).
% 0.21/0.46  fof(f33,plain,(
% 0.21/0.46    spl3_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    r2_xboole_0(sK1,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  fof(f28,plain,(
% 0.21/0.46    ~spl3_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f17,f25])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.46    inference(cnf_transformation,[],[f12])).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (31940)------------------------------
% 0.21/0.46  % (31940)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (31940)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (31940)Memory used [KB]: 10618
% 0.21/0.46  % (31940)Time elapsed: 0.063 s
% 0.21/0.46  % (31940)------------------------------
% 0.21/0.46  % (31940)------------------------------
% 0.21/0.47  % (31923)Success in time 0.108 s
%------------------------------------------------------------------------------
