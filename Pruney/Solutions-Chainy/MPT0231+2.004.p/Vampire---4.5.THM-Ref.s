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
% DateTime   : Thu Dec  3 12:36:54 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   58 (  86 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :  124 ( 178 expanded)
%              Number of equality atoms :   44 (  64 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f69,f76,f86,f114,f139,f149])).

fof(f149,plain,
    ( spl3_1
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl3_1
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f145,f39])).

fof(f39,plain,
    ( sK0 != sK2
    | spl3_1 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl3_1
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f145,plain,
    ( sK0 = sK2
    | ~ spl3_9 ),
    inference(resolution,[],[f138,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),k1_tarski(X1))
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

fof(f138,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK2))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl3_9
  <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f139,plain,
    ( spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f129,f62,f136])).

fof(f62,plain,
    ( spl3_3
  <=> k2_tarski(sK0,sK1) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f129,plain,
    ( r1_tarski(k1_tarski(sK0),k1_tarski(sK2))
    | ~ spl3_3 ),
    inference(superposition,[],[f31,f64])).

fof(f64,plain,
    ( k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f114,plain,
    ( spl3_1
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f107])).

fof(f107,plain,
    ( $false
    | spl3_1
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f39,f94])).

fof(f94,plain,
    ( ! [X2] : sK0 = X2
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f90,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

% (4146)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (4122)Termination reason: Refutation not found, incomplete strategy

% (4122)Memory used [KB]: 1663
% (4122)Time elapsed: 0.128 s
% (4122)------------------------------
% (4122)------------------------------
fof(f90,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_xboole_0,k1_tarski(X2))
        | sK0 = X2 )
    | ~ spl3_6 ),
    inference(superposition,[],[f26,f85])).

fof(f85,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl3_6
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f86,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f81,f73,f83])).

fof(f73,plain,
    ( spl3_5
  <=> r1_tarski(k1_tarski(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f81,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f79,f32])).

fof(f79,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | ~ spl3_5 ),
    inference(resolution,[],[f52,f75])).

fof(f75,plain,
    ( r1_tarski(k1_tarski(sK0),k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f73])).

fof(f52,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X3,X2)
      | X2 = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f48,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f48,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = X3
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f76,plain,
    ( spl3_5
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f71,f66,f73])).

fof(f66,plain,
    ( spl3_4
  <=> k1_xboole_0 = k2_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f71,plain,
    ( r1_tarski(k1_tarski(sK0),k1_xboole_0)
    | ~ spl3_4 ),
    inference(superposition,[],[f31,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f69,plain,
    ( spl3_3
    | spl3_4
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f58,f42,f66,f62])).

fof(f42,plain,
    ( spl3_2
  <=> r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f58,plain,
    ( k1_xboole_0 = k2_tarski(sK0,sK1)
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f23,f44])).

fof(f44,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f42])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f45,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f42])).

fof(f20,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( sK0 != sK2
    & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2] :
        ( X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) )
   => ( sK0 != sK2
      & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f12])).

% (4126)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% (4125)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => X0 = X2 ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f40,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f21,f37])).

fof(f21,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:51:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.44/0.55  % (4142)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.44/0.55  % (4123)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.44/0.55  % (4133)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.44/0.56  % (4122)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.44/0.56  % (4122)Refutation not found, incomplete strategy% (4122)------------------------------
% 1.44/0.56  % (4122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.44/0.56  % (4150)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.57/0.57  % (4142)Refutation found. Thanks to Tanya!
% 1.57/0.57  % SZS status Theorem for theBenchmark
% 1.57/0.57  % (4150)Refutation not found, incomplete strategy% (4150)------------------------------
% 1.57/0.57  % (4150)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (4150)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (4150)Memory used [KB]: 1663
% 1.57/0.57  % (4150)Time elapsed: 0.139 s
% 1.57/0.57  % (4150)------------------------------
% 1.57/0.57  % (4150)------------------------------
% 1.57/0.57  % SZS output start Proof for theBenchmark
% 1.57/0.57  fof(f150,plain,(
% 1.57/0.57    $false),
% 1.57/0.57    inference(avatar_sat_refutation,[],[f40,f45,f69,f76,f86,f114,f139,f149])).
% 1.57/0.57  fof(f149,plain,(
% 1.57/0.57    spl3_1 | ~spl3_9),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f148])).
% 1.57/0.57  fof(f148,plain,(
% 1.57/0.57    $false | (spl3_1 | ~spl3_9)),
% 1.57/0.57    inference(subsumption_resolution,[],[f145,f39])).
% 1.57/0.57  fof(f39,plain,(
% 1.57/0.57    sK0 != sK2 | spl3_1),
% 1.57/0.57    inference(avatar_component_clause,[],[f37])).
% 1.57/0.57  fof(f37,plain,(
% 1.57/0.57    spl3_1 <=> sK0 = sK2),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.57/0.57  fof(f145,plain,(
% 1.57/0.57    sK0 = sK2 | ~spl3_9),
% 1.57/0.57    inference(resolution,[],[f138,f26])).
% 1.57/0.57  fof(f26,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 1.57/0.57    inference(cnf_transformation,[],[f14])).
% 1.57/0.57  fof(f14,plain,(
% 1.57/0.57    ! [X0,X1] : (X0 = X1 | ~r1_tarski(k1_tarski(X0),k1_tarski(X1)))),
% 1.57/0.57    inference(ennf_transformation,[],[f10])).
% 1.57/0.57  fof(f10,axiom,(
% 1.57/0.57    ! [X0,X1] : (r1_tarski(k1_tarski(X0),k1_tarski(X1)) => X0 = X1)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).
% 1.57/0.57  fof(f138,plain,(
% 1.57/0.57    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) | ~spl3_9),
% 1.57/0.57    inference(avatar_component_clause,[],[f136])).
% 1.57/0.57  fof(f136,plain,(
% 1.57/0.57    spl3_9 <=> r1_tarski(k1_tarski(sK0),k1_tarski(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.57/0.57  fof(f139,plain,(
% 1.57/0.57    spl3_9 | ~spl3_3),
% 1.57/0.57    inference(avatar_split_clause,[],[f129,f62,f136])).
% 1.57/0.57  fof(f62,plain,(
% 1.57/0.57    spl3_3 <=> k2_tarski(sK0,sK1) = k1_tarski(sK2)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.57/0.57  fof(f129,plain,(
% 1.57/0.57    r1_tarski(k1_tarski(sK0),k1_tarski(sK2)) | ~spl3_3),
% 1.57/0.57    inference(superposition,[],[f31,f64])).
% 1.57/0.57  fof(f64,plain,(
% 1.57/0.57    k2_tarski(sK0,sK1) = k1_tarski(sK2) | ~spl3_3),
% 1.57/0.57    inference(avatar_component_clause,[],[f62])).
% 1.57/0.57  fof(f31,plain,(
% 1.57/0.57    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 1.57/0.57    inference(cnf_transformation,[],[f9])).
% 1.57/0.57  fof(f9,axiom,(
% 1.57/0.57    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 1.57/0.57  fof(f114,plain,(
% 1.57/0.57    spl3_1 | ~spl3_6),
% 1.57/0.57    inference(avatar_contradiction_clause,[],[f107])).
% 1.57/0.57  fof(f107,plain,(
% 1.57/0.57    $false | (spl3_1 | ~spl3_6)),
% 1.57/0.57    inference(unit_resulting_resolution,[],[f39,f94])).
% 1.57/0.57  fof(f94,plain,(
% 1.57/0.57    ( ! [X2] : (sK0 = X2) ) | ~spl3_6),
% 1.57/0.57    inference(subsumption_resolution,[],[f90,f32])).
% 1.57/0.57  fof(f32,plain,(
% 1.57/0.57    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f3])).
% 1.57/0.57  fof(f3,axiom,(
% 1.57/0.57    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.57/0.57  % (4146)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.57/0.57  % (4122)Termination reason: Refutation not found, incomplete strategy
% 1.57/0.57  
% 1.57/0.57  % (4122)Memory used [KB]: 1663
% 1.57/0.57  % (4122)Time elapsed: 0.128 s
% 1.57/0.57  % (4122)------------------------------
% 1.57/0.57  % (4122)------------------------------
% 1.57/0.57  fof(f90,plain,(
% 1.57/0.57    ( ! [X2] : (~r1_tarski(k1_xboole_0,k1_tarski(X2)) | sK0 = X2) ) | ~spl3_6),
% 1.57/0.57    inference(superposition,[],[f26,f85])).
% 1.57/0.57  fof(f85,plain,(
% 1.57/0.57    k1_xboole_0 = k1_tarski(sK0) | ~spl3_6),
% 1.57/0.57    inference(avatar_component_clause,[],[f83])).
% 1.57/0.57  fof(f83,plain,(
% 1.57/0.57    spl3_6 <=> k1_xboole_0 = k1_tarski(sK0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.57/0.57  fof(f86,plain,(
% 1.57/0.57    spl3_6 | ~spl3_5),
% 1.57/0.57    inference(avatar_split_clause,[],[f81,f73,f83])).
% 1.57/0.57  fof(f73,plain,(
% 1.57/0.57    spl3_5 <=> r1_tarski(k1_tarski(sK0),k1_xboole_0)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.57/0.57  fof(f81,plain,(
% 1.57/0.57    k1_xboole_0 = k1_tarski(sK0) | ~spl3_5),
% 1.57/0.57    inference(subsumption_resolution,[],[f79,f32])).
% 1.57/0.57  fof(f79,plain,(
% 1.57/0.57    k1_xboole_0 = k1_tarski(sK0) | ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | ~spl3_5),
% 1.57/0.57    inference(resolution,[],[f52,f75])).
% 1.57/0.57  fof(f75,plain,(
% 1.57/0.57    r1_tarski(k1_tarski(sK0),k1_xboole_0) | ~spl3_5),
% 1.57/0.57    inference(avatar_component_clause,[],[f73])).
% 1.57/0.57  fof(f52,plain,(
% 1.57/0.57    ( ! [X2,X3] : (~r1_tarski(X3,X2) | X2 = X3 | ~r1_tarski(X2,X3)) )),
% 1.57/0.57    inference(superposition,[],[f48,f27])).
% 1.57/0.57  fof(f27,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f15])).
% 1.57/0.57  fof(f15,plain,(
% 1.57/0.57    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.57/0.57    inference(ennf_transformation,[],[f2])).
% 1.57/0.57  fof(f2,axiom,(
% 1.57/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.57/0.57  fof(f48,plain,(
% 1.57/0.57    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = X3 | ~r1_tarski(X2,X3)) )),
% 1.57/0.57    inference(superposition,[],[f27,f29])).
% 1.57/0.57  fof(f29,plain,(
% 1.57/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.57/0.57    inference(cnf_transformation,[],[f1])).
% 1.57/0.57  fof(f1,axiom,(
% 1.57/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.57/0.57  fof(f76,plain,(
% 1.57/0.57    spl3_5 | ~spl3_4),
% 1.57/0.57    inference(avatar_split_clause,[],[f71,f66,f73])).
% 1.57/0.57  fof(f66,plain,(
% 1.57/0.57    spl3_4 <=> k1_xboole_0 = k2_tarski(sK0,sK1)),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.57/0.57  fof(f71,plain,(
% 1.57/0.57    r1_tarski(k1_tarski(sK0),k1_xboole_0) | ~spl3_4),
% 1.57/0.57    inference(superposition,[],[f31,f68])).
% 1.57/0.57  fof(f68,plain,(
% 1.57/0.57    k1_xboole_0 = k2_tarski(sK0,sK1) | ~spl3_4),
% 1.57/0.57    inference(avatar_component_clause,[],[f66])).
% 1.57/0.57  fof(f69,plain,(
% 1.57/0.57    spl3_3 | spl3_4 | ~spl3_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f58,f42,f66,f62])).
% 1.57/0.57  fof(f42,plain,(
% 1.57/0.57    spl3_2 <=> r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.57/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.57/0.57  fof(f58,plain,(
% 1.57/0.57    k1_xboole_0 = k2_tarski(sK0,sK1) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | ~spl3_2),
% 1.57/0.57    inference(resolution,[],[f23,f44])).
% 1.57/0.57  fof(f44,plain,(
% 1.57/0.57    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) | ~spl3_2),
% 1.57/0.57    inference(avatar_component_clause,[],[f42])).
% 1.57/0.57  fof(f23,plain,(
% 1.57/0.57    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.57/0.57    inference(cnf_transformation,[],[f19])).
% 1.57/0.57  fof(f19,plain,(
% 1.57/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.57/0.57    inference(flattening,[],[f18])).
% 1.57/0.57  fof(f18,plain,(
% 1.57/0.57    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.57/0.57    inference(nnf_transformation,[],[f8])).
% 1.57/0.57  fof(f8,axiom,(
% 1.57/0.57    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.57/0.57  fof(f45,plain,(
% 1.57/0.57    spl3_2),
% 1.57/0.57    inference(avatar_split_clause,[],[f20,f42])).
% 1.57/0.57  fof(f20,plain,(
% 1.57/0.57    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  fof(f17,plain,(
% 1.57/0.57    sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 1.57/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f16])).
% 1.57/0.57  fof(f16,plain,(
% 1.57/0.57    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))) => (sK0 != sK2 & r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)))),
% 1.57/0.57    introduced(choice_axiom,[])).
% 1.57/0.57  fof(f13,plain,(
% 1.57/0.57    ? [X0,X1,X2] : (X0 != X2 & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 1.57/0.57    inference(ennf_transformation,[],[f12])).
% 1.57/0.57  % (4126)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.57/0.57  % (4125)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.57/0.57  fof(f12,negated_conjecture,(
% 1.57/0.57    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.57/0.57    inference(negated_conjecture,[],[f11])).
% 1.57/0.57  fof(f11,conjecture,(
% 1.57/0.57    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 1.57/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 1.57/0.57  fof(f40,plain,(
% 1.57/0.57    ~spl3_1),
% 1.57/0.57    inference(avatar_split_clause,[],[f21,f37])).
% 1.57/0.57  fof(f21,plain,(
% 1.57/0.57    sK0 != sK2),
% 1.57/0.57    inference(cnf_transformation,[],[f17])).
% 1.57/0.57  % SZS output end Proof for theBenchmark
% 1.57/0.57  % (4142)------------------------------
% 1.57/0.57  % (4142)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.57  % (4142)Termination reason: Refutation
% 1.57/0.57  
% 1.57/0.57  % (4142)Memory used [KB]: 6268
% 1.57/0.57  % (4142)Time elapsed: 0.140 s
% 1.57/0.57  % (4142)------------------------------
% 1.57/0.57  % (4142)------------------------------
% 1.57/0.57  % (4120)Success in time 0.208 s
%------------------------------------------------------------------------------
