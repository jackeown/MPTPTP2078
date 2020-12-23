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
% DateTime   : Thu Dec  3 12:29:31 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   41 (  51 expanded)
%              Number of leaves         :   12 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   98 ( 124 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f66,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f25,f30,f34,f38,f51,f62,f65])).

fof(f65,plain,
    ( spl2_2
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f64])).

fof(f64,plain,
    ( $false
    | spl2_2
    | ~ spl2_9 ),
    inference(resolution,[],[f61,f29])).

fof(f29,plain,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f27])).

fof(f27,plain,
    ( spl2_2
  <=> r1_tarski(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f61,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_9
  <=> ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f62,plain,
    ( spl2_9
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f58,f49,f22,f60])).

fof(f22,plain,
    ( spl2_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f49,plain,
    ( spl2_7
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f58,plain,
    ( ! [X0] : r1_tarski(k1_xboole_0,X0)
    | ~ spl2_1
    | ~ spl2_7 ),
    inference(resolution,[],[f50,f24])).

fof(f24,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f22])).

fof(f50,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | r1_tarski(X0,X1) )
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f49])).

fof(f51,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f47,f36,f32,f49])).

fof(f32,plain,
    ( spl2_3
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f36,plain,
    ( spl2_4
  <=> ! [X1,X0] :
        ( r1_tarski(X0,X1)
        | r2_hidden(sK1(X0,X1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f47,plain,
    ( ! [X0,X1] :
        ( r1_tarski(X0,X1)
        | ~ v1_xboole_0(X0) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f37,f33])).

fof(f33,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ v1_xboole_0(X1) )
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f32])).

fof(f37,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK1(X0,X1),X0)
        | r1_tarski(X0,X1) )
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f36])).

fof(f38,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f36])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f13])).

fof(f13,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f34,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f20,f32])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f30,plain,(
    ~ spl2_2 ),
    inference(avatar_split_clause,[],[f15,f27])).

fof(f15,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ~ r1_tarski(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f9])).

fof(f9,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f25,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f16,f22])).

fof(f16,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:32:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (18944)lrs+1003_2:3_afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=on:fde=unused:gs=on:inw=on:nm=0:newcnf=on:nwc=1:sas=z3:stl=30:sac=on:sp=occurrence:tha=off:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (18952)dis+1011_4_awrs=decay:awrsf=32:afp=40000:afq=1.0:amm=off:anc=all:bs=on:cond=on:fsr=off:gsp=input_only:lma=on:nm=16:nwc=1:nicw=on:sac=on:sp=frequency:thi=all:updr=off:uhcvi=on_670 on theBenchmark
% 0.22/0.49  % (18940)dis+1_3_add=large:afp=4000:afq=1.0:anc=none:gs=on:gsem=off:inw=on:lcm=reverse:lwlo=on:nm=64:nwc=1:sas=z3:sos=all:sac=on:thi=all:uwa=all:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (18941)dis+1002_8_awrs=converge:awrsf=64:av=off:cond=fast:fsr=off:gsp=input_only:lma=on:nm=64:nwc=1.2:s2a=on:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_12 on theBenchmark
% 0.22/0.49  % (18952)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f25,f30,f34,f38,f51,f62,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    spl2_2 | ~spl2_9),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f64])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    $false | (spl2_2 | ~spl2_9)),
% 0.22/0.49    inference(resolution,[],[f61,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,sK0) | spl2_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    spl2_2 <=> r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | ~spl2_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    spl2_9 <=> ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    spl2_9 | ~spl2_1 | ~spl2_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f58,f49,f22,f60])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    spl2_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    spl2_7 <=> ! [X1,X0] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) ) | (~spl2_1 | ~spl2_7)),
% 0.22/0.49    inference(resolution,[],[f50,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0) | ~spl2_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f22])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | r1_tarski(X0,X1)) ) | ~spl2_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f49])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    spl2_7 | ~spl2_3 | ~spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f47,f36,f32,f49])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    spl2_3 <=> ! [X1,X0] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    spl2_4 <=> ! [X1,X0] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~v1_xboole_0(X0)) ) | (~spl2_3 | ~spl2_4)),
% 0.22/0.49    inference(resolution,[],[f37,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v1_xboole_0(X1)) ) | ~spl2_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f32])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r2_hidden(sK1(X0,X1),X0) | r1_tarski(X0,X1)) ) | ~spl2_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f36])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    spl2_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f18,f36])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f12,f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f11])).
% 0.22/0.49  fof(f11,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 0.22/0.49    inference(nnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    spl2_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f20,f32])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,plain,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ~spl2_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f15,f27])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,plain,(
% 0.22/0.49    ~r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f6,f9])).
% 0.22/0.49  fof(f9,plain,(
% 0.22/0.49    ? [X0] : ~r1_tarski(k1_xboole_0,X0) => ~r1_tarski(k1_xboole_0,sK0)),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f6,plain,(
% 0.22/0.49    ? [X0] : ~r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,negated_conjecture,(
% 0.22/0.49    ~! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    inference(negated_conjecture,[],[f4])).
% 0.22/0.49  fof(f4,conjecture,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    spl2_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f16,f22])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (18952)------------------------------
% 0.22/0.49  % (18952)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (18952)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (18952)Memory used [KB]: 5373
% 0.22/0.49  % (18952)Time elapsed: 0.072 s
% 0.22/0.49  % (18952)------------------------------
% 0.22/0.49  % (18952)------------------------------
% 0.22/0.49  % (18935)Success in time 0.13 s
%------------------------------------------------------------------------------
