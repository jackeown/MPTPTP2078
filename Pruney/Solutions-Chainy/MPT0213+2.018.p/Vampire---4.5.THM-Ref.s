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
% DateTime   : Thu Dec  3 12:34:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   32 (  41 expanded)
%              Number of leaves         :    9 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   84 ( 108 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f75,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f30,f42,f60,f71,f74])).

fof(f74,plain,
    ( spl4_1
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f72])).

fof(f72,plain,
    ( $false
    | spl4_1
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f25,f59,f59,f70])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r2_hidden(sK1(X0,X1),X1)
        | k3_tarski(X0) = X1 )
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_11
  <=> ! [X1,X0] :
        ( r2_hidden(sK3(X0,X1),X0)
        | r2_hidden(sK1(X0,X1),X1)
        | k3_tarski(X0) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f59,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_9
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f25,plain,
    ( k1_xboole_0 != k3_tarski(k1_xboole_0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl4_1
  <=> k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f71,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f16,f69])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r2_hidden(sK1(X0,X1),X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f60,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f56,f40,f28,f58])).

fof(f28,plain,
    ( spl4_2
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f40,plain,
    ( spl4_5
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ r2_hidden(X2,X1)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f56,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(condensation,[],[f55])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k1_xboole_0)
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f41,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | ~ r2_hidden(X2,X1)
        | ~ r2_hidden(X2,X0) )
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f40])).

fof(f42,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f11,f40])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f30,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f10,f28])).

fof(f10,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f26,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f9,f24])).

fof(f9,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(flattening,[],[f5])).

fof(f5,negated_conjecture,(
    k1_xboole_0 != k3_tarski(k1_xboole_0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:03:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (5259)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (5275)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.48  % (5262)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (5259)Refutation not found, incomplete strategy% (5259)------------------------------
% 0.22/0.48  % (5259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5259)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (5259)Memory used [KB]: 10490
% 0.22/0.48  % (5259)Time elapsed: 0.071 s
% 0.22/0.48  % (5259)------------------------------
% 0.22/0.48  % (5259)------------------------------
% 0.22/0.48  % (5262)Refutation not found, incomplete strategy% (5262)------------------------------
% 0.22/0.48  % (5262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (5262)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (5262)Memory used [KB]: 10490
% 0.22/0.48  % (5262)Time elapsed: 0.073 s
% 0.22/0.48  % (5262)------------------------------
% 0.22/0.48  % (5262)------------------------------
% 0.22/0.49  % (5275)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f26,f30,f42,f60,f71,f74])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    spl4_1 | ~spl4_9 | ~spl4_11),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    $false | (spl4_1 | ~spl4_9 | ~spl4_11)),
% 0.22/0.49    inference(unit_resulting_resolution,[],[f25,f59,f59,f70])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1) | k3_tarski(X0) = X1) ) | ~spl4_11),
% 0.22/0.49    inference(avatar_component_clause,[],[f69])).
% 0.22/0.49  fof(f69,plain,(
% 0.22/0.49    spl4_11 <=> ! [X1,X0] : (r2_hidden(sK3(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1) | k3_tarski(X0) = X1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl4_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f58])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl4_9 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    k1_xboole_0 != k3_tarski(k1_xboole_0) | spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    spl4_1 <=> k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl4_11),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f69])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r2_hidden(sK1(X0,X1),X1) | k3_tarski(X0) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl4_9 | ~spl4_2 | ~spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f56,f40,f28,f58])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    spl4_2 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    spl4_5 <=> ! [X1,X0,X2] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl4_2 | ~spl4_5)),
% 0.22/0.49    inference(condensation,[],[f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,k1_xboole_0) | ~r2_hidden(X0,X1)) ) | (~spl4_2 | ~spl4_5)),
% 0.22/0.49    inference(resolution,[],[f41,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f28])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) ) | ~spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f40])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    spl4_5),
% 0.22/0.49    inference(avatar_split_clause,[],[f11,f40])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f10,f28])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ~spl4_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f9,f24])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    k1_xboole_0 != k3_tarski(k1_xboole_0)),
% 0.22/0.49    inference(flattening,[],[f5])).
% 0.22/0.49  fof(f5,negated_conjecture,(
% 0.22/0.49    ~k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.49    inference(negated_conjecture,[],[f4])).
% 0.22/0.49  fof(f4,conjecture,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (5275)------------------------------
% 0.22/0.49  % (5275)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (5275)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (5275)Memory used [KB]: 10618
% 0.22/0.49  % (5275)Time elapsed: 0.074 s
% 0.22/0.49  % (5275)------------------------------
% 0.22/0.49  % (5275)------------------------------
% 0.22/0.49  % (5257)Success in time 0.123 s
%------------------------------------------------------------------------------
