%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    7
%              Number of atoms          :   99 ( 123 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (22075)Termination reason: Refutation not found, incomplete strategy

% (22075)Memory used [KB]: 9722
fof(f62,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f34,f38,f46,f59,f61])).

fof(f61,plain,
    ( ~ spl3_1
    | spl3_2
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f60,f57,f31,f26])).

% (22075)Time elapsed: 0.004 s
% (22075)------------------------------
% (22075)------------------------------
fof(f26,plain,
    ( spl3_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f31,plain,
    ( spl3_2
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f57,plain,
    ( spl3_8
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f60,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_2
    | ~ spl3_8 ),
    inference(resolution,[],[f58,f33])).

fof(f33,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f58,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f59,plain,
    ( spl3_8
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f55,f44,f36,f57])).

fof(f36,plain,
    ( spl3_3
  <=> ! [X0,X2] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f44,plain,
    ( spl3_5
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | r2_hidden(sK2(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f55,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl3_3
    | ~ spl3_5 ),
    inference(resolution,[],[f45,f37])).

fof(f37,plain,
    ( ! [X2,X0] :
        ( ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) )
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f36])).

fof(f45,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_tarski(X0,X1) )
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f44])).

fof(f46,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).

fof(f16,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f38,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f20,f36])).

fof(f20,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK1(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f12])).

fof(f12,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f34,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f18,f31])).

fof(f18,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).

fof(f8,plain,
    ( ? [X0] : ~ r1_tarski(k1_xboole_0,X0)
   => ~ r1_tarski(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0] : ~ r1_tarski(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f29,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:47:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (22075)dis+11_24_afp=40000:afq=1.1:amm=sco:anc=none:bs=on:gs=on:gsem=off:lcm=predicate:lma=on:nm=2:nwc=1:sos=on:sac=on:updr=off_91 on theBenchmark
% 0.22/0.46  % (22082)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.46  % (22075)Refutation not found, incomplete strategy% (22075)------------------------------
% 0.22/0.46  % (22075)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (22082)Refutation found. Thanks to Tanya!
% 0.22/0.46  % SZS status Theorem for theBenchmark
% 0.22/0.46  % SZS output start Proof for theBenchmark
% 0.22/0.46  % (22075)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (22075)Memory used [KB]: 9722
% 0.22/0.46  fof(f62,plain,(
% 0.22/0.46    $false),
% 0.22/0.46    inference(avatar_sat_refutation,[],[f29,f34,f38,f46,f59,f61])).
% 0.22/0.46  fof(f61,plain,(
% 0.22/0.46    ~spl3_1 | spl3_2 | ~spl3_8),
% 0.22/0.46    inference(avatar_split_clause,[],[f60,f57,f31,f26])).
% 0.22/0.46  % (22075)Time elapsed: 0.004 s
% 0.22/0.46  % (22075)------------------------------
% 0.22/0.46  % (22075)------------------------------
% 0.22/0.46  fof(f26,plain,(
% 0.22/0.46    spl3_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.46  fof(f31,plain,(
% 0.22/0.46    spl3_2 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.22/0.46  fof(f57,plain,(
% 0.22/0.46    spl3_8 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.22/0.46  fof(f60,plain,(
% 0.22/0.46    ~v1_xboole_0(k1_xboole_0) | (spl3_2 | ~spl3_8)),
% 0.22/0.46    inference(resolution,[],[f58,f33])).
% 0.22/0.46  fof(f33,plain,(
% 0.22/0.46    ~r1_tarski(k1_xboole_0,sK0) | spl3_2),
% 0.22/0.46    inference(avatar_component_clause,[],[f31])).
% 0.22/0.46  fof(f58,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) ) | ~spl3_8),
% 0.22/0.46    inference(avatar_component_clause,[],[f57])).
% 0.22/0.46  fof(f59,plain,(
% 0.22/0.46    spl3_8 | ~spl3_3 | ~spl3_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f55,f44,f36,f57])).
% 0.22/0.46  fof(f36,plain,(
% 0.22/0.46    spl3_3 <=> ! [X0,X2] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.22/0.46  fof(f44,plain,(
% 0.22/0.46    spl3_5 <=> ! [X1,X0] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0))),
% 0.22/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.22/0.46  fof(f55,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) ) | (~spl3_3 | ~spl3_5)),
% 0.22/0.46    inference(resolution,[],[f45,f37])).
% 0.22/0.46  fof(f37,plain,(
% 0.22/0.46    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) ) | ~spl3_3),
% 0.22/0.46    inference(avatar_component_clause,[],[f36])).
% 0.22/0.46  fof(f45,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) ) | ~spl3_5),
% 0.22/0.46    inference(avatar_component_clause,[],[f44])).
% 0.22/0.46  fof(f46,plain,(
% 0.22/0.46    spl3_5),
% 0.22/0.46    inference(avatar_split_clause,[],[f23,f44])).
% 0.22/0.46  fof(f23,plain,(
% 0.22/0.46    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK2(X0,X1),X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f17])).
% 0.22/0.46  fof(f17,plain,(
% 0.22/0.46    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f15,f16])).
% 0.22/0.46  fof(f16,plain,(
% 0.22/0.46    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f15,plain,(
% 0.22/0.46    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.46    inference(rectify,[],[f14])).
% 0.22/0.46  fof(f14,plain,(
% 0.22/0.46    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.46    inference(nnf_transformation,[],[f7])).
% 0.22/0.46  fof(f7,plain,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.46    inference(ennf_transformation,[],[f2])).
% 0.22/0.46  fof(f2,axiom,(
% 0.22/0.46    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.46  fof(f38,plain,(
% 0.22/0.46    spl3_3),
% 0.22/0.46    inference(avatar_split_clause,[],[f20,f36])).
% 0.22/0.46  fof(f20,plain,(
% 0.22/0.46    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 0.22/0.46    inference(cnf_transformation,[],[f13])).
% 0.22/0.46  fof(f13,plain,(
% 0.22/0.46    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK1(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f12])).
% 0.22/0.46  fof(f12,plain,(
% 0.22/0.46    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f11,plain,(
% 0.22/0.46    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.46    inference(rectify,[],[f10])).
% 0.22/0.46  fof(f10,plain,(
% 0.22/0.46    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 0.22/0.46    inference(nnf_transformation,[],[f1])).
% 0.22/0.46  fof(f1,axiom,(
% 0.22/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.46  fof(f34,plain,(
% 0.22/0.46    ~spl3_2),
% 0.22/0.46    inference(avatar_split_clause,[],[f18,f31])).
% 0.22/0.46  fof(f18,plain,(
% 0.22/0.46    ~r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.46    inference(cnf_transformation,[],[f9])).
% 0.22/0.46  fof(f9,plain,(
% 0.22/0.46    ~r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f8])).
% 0.22/0.46  fof(f8,plain,(
% 0.22/0.46    ? [X0] : ~r1_tarski(k1_xboole_0,X0) => ~r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.46    introduced(choice_axiom,[])).
% 0.22/0.46  fof(f6,plain,(
% 0.22/0.46    ? [X0] : ~r1_tarski(k1_xboole_0,X0)),
% 0.22/0.46    inference(ennf_transformation,[],[f5])).
% 0.22/0.46  fof(f5,negated_conjecture,(
% 0.22/0.46    ~! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.46    inference(negated_conjecture,[],[f4])).
% 0.22/0.46  fof(f4,conjecture,(
% 0.22/0.46    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.46  fof(f29,plain,(
% 0.22/0.46    spl3_1),
% 0.22/0.46    inference(avatar_split_clause,[],[f19,f26])).
% 0.22/0.46  fof(f19,plain,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    inference(cnf_transformation,[],[f3])).
% 0.22/0.46  fof(f3,axiom,(
% 0.22/0.46    v1_xboole_0(k1_xboole_0)),
% 0.22/0.46    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.46  % SZS output end Proof for theBenchmark
% 0.22/0.46  % (22082)------------------------------
% 0.22/0.46  % (22082)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (22082)Termination reason: Refutation
% 0.22/0.46  
% 0.22/0.46  % (22082)Memory used [KB]: 5373
% 0.22/0.46  % (22082)Time elapsed: 0.006 s
% 0.22/0.46  % (22082)------------------------------
% 0.22/0.46  % (22082)------------------------------
% 0.22/0.46  % (22061)Success in time 0.1 s
%------------------------------------------------------------------------------
