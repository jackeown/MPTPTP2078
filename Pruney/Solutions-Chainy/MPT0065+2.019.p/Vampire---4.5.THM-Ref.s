%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:20 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   60 (  88 expanded)
%              Number of leaves         :   18 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :  138 ( 221 expanded)
%              Number of equality atoms :   35 (  44 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f178,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f57,f67,f72,f103,f159,f161,f169])).

fof(f169,plain,
    ( ~ spl3_2
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f164,f154,f70,f39])).

fof(f39,plain,
    ( spl3_2
  <=> r1_tarski(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,
    ( spl3_7
  <=> sK1 = k2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f154,plain,
    ( spl3_14
  <=> ! [X11] : ~ r1_tarski(k2_xboole_0(sK0,X11),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f164,plain,
    ( ~ r1_tarski(sK1,sK2)
    | ~ spl3_7
    | ~ spl3_14 ),
    inference(superposition,[],[f155,f71])).

fof(f71,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f70])).

fof(f155,plain,
    ( ! [X11] : ~ r1_tarski(k2_xboole_0(sK0,X11),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f154])).

fof(f161,plain,
    ( sK0 != sK2
    | sK1 != k2_xboole_0(sK0,sK1)
    | sK2 != k2_xboole_0(sK2,sK1)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f159,plain,
    ( spl3_14
    | spl3_15
    | spl3_1 ),
    inference(avatar_split_clause,[],[f149,f35,f157,f154])).

fof(f157,plain,
    ( spl3_15
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f35,plain,
    ( spl3_1
  <=> r2_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f149,plain,
    ( ! [X11] :
        ( sK0 = sK2
        | ~ r1_tarski(k2_xboole_0(sK0,X11),sK2) )
    | spl3_1 ),
    inference(resolution,[],[f93,f36])).

fof(f36,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(resolution,[],[f29,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r2_xboole_0(X0,X1)
        | X0 = X1
        | ~ r1_tarski(X0,X1) )
      & ( ( X0 != X1
          & r1_tarski(X0,X1) )
        | ~ r2_xboole_0(X0,X1) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f103,plain,
    ( sK1 != sK2
    | r2_xboole_0(sK0,sK2)
    | ~ r2_xboole_0(sK0,sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f72,plain,
    ( spl3_7
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f68,f43,f70])).

fof(f43,plain,
    ( spl3_3
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f68,plain,
    ( sK1 = k2_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f47,f44])).

fof(f44,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(resolution,[],[f26,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f67,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f63,f55,f65])).

fof(f65,plain,
    ( spl3_6
  <=> sK2 = k2_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f55,plain,
    ( spl3_5
  <=> k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f63,plain,
    ( sK2 = k2_xboole_0(sK2,sK1)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f62,f23])).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f62,plain,
    ( k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_5 ),
    inference(superposition,[],[f25,f56])).

fof(f56,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f57,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f52,f39,f55])).

fof(f52,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f31,f40])).

fof(f40,plain,
    ( r1_tarski(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    r2_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r2_xboole_0(sK0,sK2)
    & r1_tarski(sK1,sK2)
    & r2_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_xboole_0(X0,X2)
        & r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
   => ( ~ r2_xboole_0(sK0,sK2)
      & r1_tarski(sK1,sK2)
      & r2_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_xboole_0(X0,X2)
      & r1_tarski(X1,X2)
      & r2_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X1,X2)
          & r2_xboole_0(X0,X1) )
       => r2_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r2_xboole_0(X0,X1) )
     => r2_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f21,f39])).

fof(f21,plain,(
    r1_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f37,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f22,f35])).

fof(f22,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 12:25:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.51  % (17127)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.51  % (17123)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (17131)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.51  % (17135)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.51  % (17131)Refutation not found, incomplete strategy% (17131)------------------------------
% 0.22/0.51  % (17131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (17131)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (17131)Memory used [KB]: 1663
% 0.22/0.51  % (17131)Time elapsed: 0.004 s
% 0.22/0.51  % (17131)------------------------------
% 0.22/0.51  % (17131)------------------------------
% 0.22/0.51  % (17123)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (17122)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (17132)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f37,f41,f45,f57,f67,f72,f103,f159,f161,f169])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    ~spl3_2 | ~spl3_7 | ~spl3_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f164,f154,f70,f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    spl3_2 <=> r1_tarski(sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.52  fof(f70,plain,(
% 0.22/0.52    spl3_7 <=> sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.52  fof(f154,plain,(
% 0.22/0.52    spl3_14 <=> ! [X11] : ~r1_tarski(k2_xboole_0(sK0,X11),sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ~r1_tarski(sK1,sK2) | (~spl3_7 | ~spl3_14)),
% 0.22/0.52    inference(superposition,[],[f155,f71])).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_7),
% 0.22/0.52    inference(avatar_component_clause,[],[f70])).
% 0.22/0.52  fof(f155,plain,(
% 0.22/0.52    ( ! [X11] : (~r1_tarski(k2_xboole_0(sK0,X11),sK2)) ) | ~spl3_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f154])).
% 0.22/0.52  fof(f161,plain,(
% 0.22/0.52    sK0 != sK2 | sK1 != k2_xboole_0(sK0,sK1) | sK2 != k2_xboole_0(sK2,sK1) | sK1 = sK2),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f159,plain,(
% 0.22/0.52    spl3_14 | spl3_15 | spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f149,f35,f157,f154])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    spl3_15 <=> sK0 = sK2),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    spl3_1 <=> r2_xboole_0(sK0,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.52  fof(f149,plain,(
% 0.22/0.52    ( ! [X11] : (sK0 = sK2 | ~r1_tarski(k2_xboole_0(sK0,X11),sK2)) ) | spl3_1),
% 0.22/0.52    inference(resolution,[],[f93,f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ~r2_xboole_0(sK0,sK2) | spl3_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f35])).
% 0.22/0.52  fof(f93,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 0.22/0.52    inference(resolution,[],[f29,f32])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1)) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.52    inference(flattening,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0,X1] : ((r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1))) & ((X0 != X1 & r1_tarski(X0,X1)) | ~r2_xboole_0(X0,X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    sK1 != sK2 | r2_xboole_0(sK0,sK2) | ~r2_xboole_0(sK0,sK1)),
% 0.22/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.22/0.52  fof(f72,plain,(
% 0.22/0.52    spl3_7 | ~spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f68,f43,f70])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    spl3_3 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    sK1 = k2_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.52    inference(resolution,[],[f47,f44])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    r2_xboole_0(sK0,sK1) | ~spl3_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f43])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.52    inference(resolution,[],[f26,f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f18])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.52    inference(cnf_transformation,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.52  fof(f67,plain,(
% 0.22/0.52    spl3_6 | ~spl3_5),
% 0.22/0.52    inference(avatar_split_clause,[],[f63,f55,f65])).
% 0.22/0.52  fof(f65,plain,(
% 0.22/0.52    spl3_6 <=> sK2 = k2_xboole_0(sK2,sK1)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    spl3_5 <=> k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    sK2 = k2_xboole_0(sK2,sK1) | ~spl3_5),
% 0.22/0.52    inference(forward_demodulation,[],[f62,f23])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    k2_xboole_0(sK2,sK1) = k2_xboole_0(sK2,k1_xboole_0) | ~spl3_5),
% 0.22/0.52    inference(superposition,[],[f25,f56])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl3_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f55])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.52  fof(f57,plain,(
% 0.22/0.52    spl3_5 | ~spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f52,f39,f55])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    k1_xboole_0 = k4_xboole_0(sK1,sK2) | ~spl3_2),
% 0.22/0.52    inference(resolution,[],[f31,f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    r1_tarski(sK1,sK2) | ~spl3_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f39])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.52    inference(nnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    spl3_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f20,f43])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    r2_xboole_0(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f15])).
% 0.22/0.52  fof(f15,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => (~r2_xboole_0(sK0,sK2) & r1_tarski(sK1,sK2) & r2_xboole_0(sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & r1_tarski(X1,X2) & r2_xboole_0(X0,X1))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0,X1,X2] : (~r2_xboole_0(X0,X2) & (r1_tarski(X1,X2) & r2_xboole_0(X0,X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.52    inference(negated_conjecture,[],[f8])).
% 0.22/0.52  fof(f8,conjecture,(
% 0.22/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r2_xboole_0(X0,X1)) => r2_xboole_0(X0,X2))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    spl3_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f21,f39])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    r1_tarski(sK1,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ~spl3_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f22,f35])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ~r2_xboole_0(sK0,sK2)),
% 0.22/0.52    inference(cnf_transformation,[],[f16])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (17123)------------------------------
% 0.22/0.52  % (17123)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17123)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (17123)Memory used [KB]: 10618
% 0.22/0.52  % (17123)Time elapsed: 0.067 s
% 0.22/0.52  % (17123)------------------------------
% 0.22/0.52  % (17123)------------------------------
% 0.22/0.52  % (17116)Success in time 0.15 s
%------------------------------------------------------------------------------
