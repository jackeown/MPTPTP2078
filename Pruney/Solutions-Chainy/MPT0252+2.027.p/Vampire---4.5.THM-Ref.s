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
% DateTime   : Thu Dec  3 12:38:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 (  85 expanded)
%              Number of leaves         :   18 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :  142 ( 201 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f51,f55,f59,f71,f75,f79,f128,f156,f208,f274,f285])).

fof(f285,plain,
    ( ~ spl3_3
    | ~ spl3_16
    | ~ spl3_32 ),
    inference(avatar_contradiction_clause,[],[f278])).

fof(f278,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_16
    | ~ spl3_32 ),
    inference(unit_resulting_resolution,[],[f127,f54,f273])).

fof(f273,plain,
    ( ! [X16] :
        ( ~ r1_tarski(X16,k2_xboole_0(k2_tarski(sK0,sK1),sK2))
        | r1_tarski(X16,sK2) )
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f272])).

fof(f272,plain,
    ( spl3_32
  <=> ! [X16] :
        ( r1_tarski(X16,sK2)
        | ~ r1_tarski(X16,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f54,plain,
    ( ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl3_3
  <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f127,plain,
    ( ! [X0] : ~ r1_tarski(k2_tarski(sK0,X0),sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_16
  <=> ! [X0] : ~ r1_tarski(k2_tarski(sK0,X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f274,plain,
    ( spl3_32
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f225,f206,f154,f272])).

fof(f154,plain,
    ( spl3_22
  <=> ! [X0] : r1_tarski(k3_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),sK2),X0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f206,plain,
    ( spl3_28
  <=> ! [X3,X2] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f225,plain,
    ( ! [X16] :
        ( r1_tarski(X16,sK2)
        | ~ r1_tarski(X16,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) )
    | ~ spl3_22
    | ~ spl3_28 ),
    inference(superposition,[],[f155,f207])).

fof(f207,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f206])).

fof(f155,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),sK2),X0),sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f154])).

fof(f208,plain,
    ( spl3_28
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f94,f69,f57,f206])).

fof(f57,plain,
    ( spl3_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f69,plain,
    ( spl3_7
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f94,plain,
    ( ! [X2,X3] :
        ( k3_xboole_0(X3,X2) = X2
        | ~ r1_tarski(X2,X3) )
    | ~ spl3_4
    | ~ spl3_7 ),
    inference(superposition,[],[f70,f58])).

fof(f58,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f70,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f69])).

fof(f156,plain,
    ( spl3_22
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f103,f73,f48,f154])).

fof(f48,plain,
    ( spl3_2
  <=> r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f73,plain,
    ( spl3_8
  <=> ! [X1,X0,X2] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f103,plain,
    ( ! [X0] : r1_tarski(k3_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),sK2),X0),sK2)
    | ~ spl3_2
    | ~ spl3_8 ),
    inference(unit_resulting_resolution,[],[f50,f74])).

fof(f74,plain,
    ( ! [X2,X0,X1] :
        ( r1_tarski(k3_xboole_0(X0,X2),X1)
        | ~ r1_tarski(X0,X1) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f73])).

fof(f50,plain,
    ( r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f128,plain,
    ( spl3_16
    | spl3_1
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f108,f77,f43,f126])).

fof(f43,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f77,plain,
    ( spl3_9
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,X2)
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f108,plain,
    ( ! [X0] : ~ r1_tarski(k2_tarski(sK0,X0),sK2)
    | spl3_1
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f45,f78])).

fof(f78,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k2_tarski(X0,X1),X2)
        | r2_hidden(X0,X2) )
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f77])).

fof(f45,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f79,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f35,f77])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f75,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f34,f73])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f71,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f69])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f26,f53])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

% (546)Refutation not found, incomplete strategy% (546)------------------------------
% (546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

% (546)Termination reason: Refutation not found, incomplete strategy
fof(f51,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f21])).

% (546)Memory used [KB]: 10746
% (546)Time elapsed: 0.074 s
% (546)------------------------------
% (546)------------------------------
fof(f21,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f46,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f25,f43])).

fof(f25,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:08:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.22/0.46  % (540)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.46  % (539)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.46  % (535)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.46  % (550)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.46  % (542)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.46  % (538)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (537)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (543)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (546)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (540)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f286,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f46,f51,f55,f59,f71,f75,f79,f128,f156,f208,f274,f285])).
% 0.22/0.48  fof(f285,plain,(
% 0.22/0.48    ~spl3_3 | ~spl3_16 | ~spl3_32),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f278])).
% 0.22/0.48  fof(f278,plain,(
% 0.22/0.48    $false | (~spl3_3 | ~spl3_16 | ~spl3_32)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f127,f54,f273])).
% 0.22/0.48  fof(f273,plain,(
% 0.22/0.48    ( ! [X16] : (~r1_tarski(X16,k2_xboole_0(k2_tarski(sK0,sK1),sK2)) | r1_tarski(X16,sK2)) ) | ~spl3_32),
% 0.22/0.48    inference(avatar_component_clause,[],[f272])).
% 0.22/0.48  fof(f272,plain,(
% 0.22/0.48    spl3_32 <=> ! [X16] : (r1_tarski(X16,sK2) | ~r1_tarski(X16,k2_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) ) | ~spl3_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f53])).
% 0.22/0.48  fof(f53,plain,(
% 0.22/0.48    spl3_3 <=> ! [X1,X0] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.48  fof(f127,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k2_tarski(sK0,X0),sK2)) ) | ~spl3_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f126])).
% 0.22/0.48  fof(f126,plain,(
% 0.22/0.48    spl3_16 <=> ! [X0] : ~r1_tarski(k2_tarski(sK0,X0),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.22/0.48  fof(f274,plain,(
% 0.22/0.48    spl3_32 | ~spl3_22 | ~spl3_28),
% 0.22/0.48    inference(avatar_split_clause,[],[f225,f206,f154,f272])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    spl3_22 <=> ! [X0] : r1_tarski(k3_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),sK2),X0),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.22/0.48  fof(f206,plain,(
% 0.22/0.48    spl3_28 <=> ! [X3,X2] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.22/0.48  fof(f225,plain,(
% 0.22/0.48    ( ! [X16] : (r1_tarski(X16,sK2) | ~r1_tarski(X16,k2_xboole_0(k2_tarski(sK0,sK1),sK2))) ) | (~spl3_22 | ~spl3_28)),
% 0.22/0.48    inference(superposition,[],[f155,f207])).
% 0.22/0.48  fof(f207,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | ~spl3_28),
% 0.22/0.48    inference(avatar_component_clause,[],[f206])).
% 0.22/0.48  fof(f155,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k3_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),sK2),X0),sK2)) ) | ~spl3_22),
% 0.22/0.48    inference(avatar_component_clause,[],[f154])).
% 0.22/0.48  fof(f208,plain,(
% 0.22/0.48    spl3_28 | ~spl3_4 | ~spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f94,f69,f57,f206])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl3_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    spl3_7 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.22/0.48  fof(f94,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k3_xboole_0(X3,X2) = X2 | ~r1_tarski(X2,X3)) ) | (~spl3_4 | ~spl3_7)),
% 0.22/0.48    inference(superposition,[],[f70,f58])).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl3_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f57])).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl3_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f69])).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    spl3_22 | ~spl3_2 | ~spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f103,f73,f48,f154])).
% 0.22/0.48  fof(f48,plain,(
% 0.22/0.48    spl3_2 <=> r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    spl3_8 <=> ! [X1,X0,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k3_xboole_0(k2_xboole_0(k2_tarski(sK0,sK1),sK2),X0),sK2)) ) | (~spl3_2 | ~spl3_8)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f50,f74])).
% 0.22/0.48  fof(f74,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) ) | ~spl3_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f73])).
% 0.22/0.48  fof(f50,plain,(
% 0.22/0.48    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) | ~spl3_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f48])).
% 0.22/0.48  fof(f128,plain,(
% 0.22/0.48    spl3_16 | spl3_1 | ~spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f108,f77,f43,f126])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    spl3_1 <=> r2_hidden(sK0,sK2)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.48  fof(f77,plain,(
% 0.22/0.48    spl3_9 <=> ! [X1,X0,X2] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(k2_tarski(sK0,X0),sK2)) ) | (spl3_1 | ~spl3_9)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f45,f78])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) ) | ~spl3_9),
% 0.22/0.48    inference(avatar_component_clause,[],[f77])).
% 0.22/0.48  fof(f45,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK2) | spl3_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f43])).
% 0.22/0.48  fof(f79,plain,(
% 0.22/0.48    spl3_9),
% 0.22/0.48    inference(avatar_split_clause,[],[f35,f77])).
% 0.22/0.48  fof(f35,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f23])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.48    inference(flattening,[],[f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.22/0.48    inference(nnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl3_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f34,f73])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl3_7),
% 0.22/0.48    inference(avatar_split_clause,[],[f32,f69])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl3_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f57])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    spl3_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f26,f53])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  % (546)Refutation not found, incomplete strategy% (546)------------------------------
% 0.22/0.48  % (546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.48  % (546)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    spl3_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f48])).
% 0.22/0.48  
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  % (546)Memory used [KB]: 10746
% 0.22/0.48  % (546)Time elapsed: 0.074 s
% 0.22/0.48  % (546)------------------------------
% 0.22/0.48  % (546)------------------------------
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.22/0.48    inference(negated_conjecture,[],[f15])).
% 0.22/0.48  fof(f15,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ~spl3_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f25,f43])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ~r2_hidden(sK0,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (540)------------------------------
% 0.22/0.48  % (540)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (540)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (540)Memory used [KB]: 6268
% 0.22/0.48  % (540)Time elapsed: 0.067 s
% 0.22/0.48  % (540)------------------------------
% 0.22/0.48  % (540)------------------------------
% 0.22/0.48  % (534)Success in time 0.126 s
%------------------------------------------------------------------------------
