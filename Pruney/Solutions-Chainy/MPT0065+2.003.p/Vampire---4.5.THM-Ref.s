%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  84 expanded)
%              Number of leaves         :   17 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :  121 ( 188 expanded)
%              Number of equality atoms :   15 (  20 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f39,f48,f66,f75,f76,f83,f90,f98,f99])).

fof(f99,plain,
    ( sK0 != sK2
    | r2_xboole_0(sK2,sK1)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f98,plain,
    ( spl3_12
    | spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f93,f87,f36,f95])).

fof(f95,plain,
    ( spl3_12
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f36,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f87,plain,
    ( spl3_11
  <=> r1_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f93,plain,
    ( sK0 = sK2
    | spl3_3
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f91,f38])).

fof(f38,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f91,plain,
    ( sK0 = sK2
    | r2_xboole_0(sK0,sK2)
    | ~ spl3_11 ),
    inference(resolution,[],[f89,f22])).

fof(f22,plain,(
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

fof(f89,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f87])).

fof(f90,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f85,f63,f31,f87])).

fof(f31,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f63,plain,
    ( spl3_7
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f85,plain,
    ( r1_tarski(sK0,sK2)
    | ~ spl3_2
    | ~ spl3_7 ),
    inference(resolution,[],[f84,f33])).

fof(f33,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f84,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,X0)
        | r1_tarski(sK0,X0) )
    | ~ spl3_7 ),
    inference(superposition,[],[f23,f65])).

fof(f65,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f63])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f83,plain,
    ( ~ spl3_10
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f78,f68,f80])).

fof(f80,plain,
    ( spl3_10
  <=> r2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f68,plain,
    ( spl3_8
  <=> r2_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f78,plain,
    ( ~ r2_xboole_0(sK2,sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f70,f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
     => ~ r2_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).

fof(f70,plain,
    ( r2_xboole_0(sK1,sK2)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f68])).

fof(f76,plain,
    ( sK1 != sK2
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f75,plain,
    ( spl3_8
    | spl3_9
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f42,f31,f72,f68])).

fof(f72,plain,
    ( spl3_9
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f42,plain,
    ( sK1 = sK2
    | r2_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f33,f22])).

% (27707)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f66,plain,
    ( spl3_7
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f55,f45,f63])).

fof(f45,plain,
    ( spl3_4
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

% (27697)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f55,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_4 ),
    inference(resolution,[],[f47,f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f47,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f45])).

fof(f48,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f40,f26,f45])).

fof(f26,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f40,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl3_1 ),
    inference(resolution,[],[f28,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

% (27701)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f28,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f39,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f16,f36])).

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

fof(f34,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f15,f31])).

fof(f15,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f10])).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f14,f26])).

fof(f14,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:16:49 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.48  % (27710)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.49  % (27700)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (27695)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (27699)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (27695)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f100,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f29,f34,f39,f48,f66,f75,f76,f83,f90,f98,f99])).
% 0.21/0.49  fof(f99,plain,(
% 0.21/0.49    sK0 != sK2 | r2_xboole_0(sK2,sK1) | ~r2_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f98,plain,(
% 0.21/0.49    spl3_12 | spl3_3 | ~spl3_11),
% 0.21/0.49    inference(avatar_split_clause,[],[f93,f87,f36,f95])).
% 0.21/0.49  fof(f95,plain,(
% 0.21/0.49    spl3_12 <=> sK0 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    spl3_3 <=> r2_xboole_0(sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    spl3_11 <=> r1_tarski(sK0,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    sK0 = sK2 | (spl3_3 | ~spl3_11)),
% 0.21/0.49    inference(subsumption_resolution,[],[f91,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ~r2_xboole_0(sK0,sK2) | spl3_3),
% 0.21/0.49    inference(avatar_component_clause,[],[f36])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    sK0 = sK2 | r2_xboole_0(sK0,sK2) | ~spl3_11),
% 0.21/0.49    inference(resolution,[],[f89,f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    r1_tarski(sK0,sK2) | ~spl3_11),
% 0.21/0.49    inference(avatar_component_clause,[],[f87])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    spl3_11 | ~spl3_2 | ~spl3_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f85,f63,f31,f87])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    spl3_7 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.49  fof(f85,plain,(
% 0.21/0.49    r1_tarski(sK0,sK2) | (~spl3_2 | ~spl3_7)),
% 0.21/0.49    inference(resolution,[],[f84,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.21/0.49    inference(avatar_component_clause,[],[f31])).
% 0.21/0.49  fof(f84,plain,(
% 0.21/0.49    ( ! [X0] : (~r1_tarski(sK1,X0) | r1_tarski(sK0,X0)) ) | ~spl3_7),
% 0.21/0.49    inference(superposition,[],[f23,f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f63])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    ~spl3_10 | ~spl3_8),
% 0.21/0.49    inference(avatar_split_clause,[],[f78,f68,f80])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    spl3_10 <=> r2_xboole_0(sK2,sK1)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    spl3_8 <=> r2_xboole_0(sK1,sK2)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~r2_xboole_0(sK2,sK1) | ~spl3_8),
% 0.21/0.49    inference(resolution,[],[f70,f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r2_xboole_0(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) => ~r2_xboole_0(X1,X0))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_xboole_0)).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    r2_xboole_0(sK1,sK2) | ~spl3_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f68])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    sK1 != sK2 | r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK0,sK1)),
% 0.21/0.49    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    spl3_8 | spl3_9 | ~spl3_2),
% 0.21/0.49    inference(avatar_split_clause,[],[f42,f31,f72,f68])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    spl3_9 <=> sK1 = sK2),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    sK1 = sK2 | r2_xboole_0(sK1,sK2) | ~spl3_2),
% 0.21/0.49    inference(resolution,[],[f33,f22])).
% 0.21/0.49  % (27707)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    spl3_7 | ~spl3_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f55,f45,f63])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    spl3_4 <=> r1_tarski(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  % (27697)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_4),
% 0.21/0.50    inference(resolution,[],[f47,f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.50    inference(cnf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,plain,(
% 0.21/0.50    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f45])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    spl3_4 | ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f40,f26,f45])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    spl3_1 <=> r2_xboole_0(sK0,sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    r1_tarski(sK0,sK1) | ~spl3_1),
% 0.21/0.50    inference(resolution,[],[f28,f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  % (27701)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    r2_xboole_0(sK0,sK1) | ~spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f26])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ~spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f16,f36])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ~r2_xboole_0(sK0,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.21/0.50    inference(flattening,[],[f9])).
% 0.21/0.50  fof(f9,plain,(
% 0.21/0.50    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.50    inference(negated_conjecture,[],[f6])).
% 0.21/0.50  fof(f6,conjecture,(
% 0.21/0.50    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f15,f31])).
% 0.21/0.50  fof(f15,plain,(
% 0.21/0.50    r1_tarski(sK1,sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f14,f26])).
% 0.21/0.50  fof(f14,plain,(
% 0.21/0.50    r2_xboole_0(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f10])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (27695)------------------------------
% 0.21/0.50  % (27695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27695)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (27695)Memory used [KB]: 10618
% 0.21/0.50  % (27695)Time elapsed: 0.052 s
% 0.21/0.50  % (27695)------------------------------
% 0.21/0.50  % (27695)------------------------------
% 0.21/0.50  % (27702)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (27702)Refutation not found, incomplete strategy% (27702)------------------------------
% 0.21/0.50  % (27702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (27702)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (27702)Memory used [KB]: 6012
% 0.21/0.50  % (27702)Time elapsed: 0.073 s
% 0.21/0.50  % (27702)------------------------------
% 0.21/0.50  % (27702)------------------------------
% 0.21/0.50  % (27711)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.50  % (27691)Success in time 0.135 s
%------------------------------------------------------------------------------
