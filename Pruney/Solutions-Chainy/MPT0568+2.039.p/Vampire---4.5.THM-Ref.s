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
% DateTime   : Thu Dec  3 12:50:15 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.23s
% Verified   : 
% Statistics : Number of formulae       :   58 (  66 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :   12
%              Number of atoms          :  134 ( 150 expanded)
%              Number of equality atoms :   28 (  33 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (3265)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f43,f47,f51,f59,f64,f70,f83])).

fof(f83,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f82])).

fof(f82,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(subsumption_resolution,[],[f42,f81])).

fof(f81,plain,
    ( ! [X1] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(resolution,[],[f78,f69])).

fof(f69,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_7
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f78,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,k1_xboole_0)
        | k1_xboole_0 = X0 )
    | ~ spl2_2 ),
    inference(resolution,[],[f77,f46])).

fof(f46,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f77,plain,(
    ! [X4,X5] :
      ( ~ v1_xboole_0(X5)
      | X4 = X5
      | ~ r1_tarski(X4,X5) ) ),
    inference(resolution,[],[f72,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f72,plain,(
    ! [X2,X1] :
      ( r2_hidden(sK1(X2,X1),X2)
      | ~ r1_tarski(X1,X2)
      | X1 = X2 ) ),
    inference(resolution,[],[f34,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).

fof(f22,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f42,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f70,plain,
    ( ~ spl2_6
    | spl2_7
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f65,f57,f68,f62])).

fof(f62,plain,
    ( spl2_6
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f57,plain,
    ( spl2_5
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f65,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl2_5 ),
    inference(superposition,[],[f31,f58])).

fof(f58,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f57])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f64,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f60,f49,f62])).

fof(f49,plain,
    ( spl2_3
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f60,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f29,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f29,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f59,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f27,f57])).

fof(f27,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f51,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f26,f49])).

fof(f26,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

fof(f47,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f25,f45])).

fof(f25,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f43,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f24,f41])).

fof(f24,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).

fof(f16,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:59:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (3255)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.52  % (3257)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.52  % (3261)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.52  % (3266)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (3261)Refutation not found, incomplete strategy% (3261)------------------------------
% 0.22/0.52  % (3261)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (3261)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (3261)Memory used [KB]: 10618
% 0.22/0.52  % (3261)Time elapsed: 0.104 s
% 0.22/0.52  % (3261)------------------------------
% 0.22/0.52  % (3261)------------------------------
% 0.22/0.52  % (3279)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.52  % (3260)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.23/0.52  % (3260)Refutation not found, incomplete strategy% (3260)------------------------------
% 1.23/0.52  % (3260)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.52  % (3260)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.52  
% 1.23/0.52  % (3260)Memory used [KB]: 10618
% 1.23/0.52  % (3260)Time elapsed: 0.105 s
% 1.23/0.52  % (3260)------------------------------
% 1.23/0.52  % (3260)------------------------------
% 1.23/0.52  % (3258)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.52  % (3271)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.23/0.52  % (3252)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.52  % (3271)Refutation found. Thanks to Tanya!
% 1.23/0.52  % SZS status Theorem for theBenchmark
% 1.23/0.52  % SZS output start Proof for theBenchmark
% 1.23/0.52  % (3265)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.23/0.52  fof(f84,plain,(
% 1.23/0.52    $false),
% 1.23/0.52    inference(avatar_sat_refutation,[],[f43,f47,f51,f59,f64,f70,f83])).
% 1.23/0.52  fof(f83,plain,(
% 1.23/0.52    spl2_1 | ~spl2_2 | ~spl2_7),
% 1.23/0.52    inference(avatar_contradiction_clause,[],[f82])).
% 1.23/0.52  fof(f82,plain,(
% 1.23/0.52    $false | (spl2_1 | ~spl2_2 | ~spl2_7)),
% 1.23/0.52    inference(subsumption_resolution,[],[f42,f81])).
% 1.23/0.52  fof(f81,plain,(
% 1.23/0.52    ( ! [X1] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X1)) ) | (~spl2_2 | ~spl2_7)),
% 1.23/0.52    inference(resolution,[],[f78,f69])).
% 1.23/0.52  fof(f69,plain,(
% 1.23/0.52    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl2_7),
% 1.23/0.52    inference(avatar_component_clause,[],[f68])).
% 1.23/0.52  fof(f68,plain,(
% 1.23/0.52    spl2_7 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 1.23/0.52  fof(f78,plain,(
% 1.23/0.52    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) ) | ~spl2_2),
% 1.23/0.52    inference(resolution,[],[f77,f46])).
% 1.23/0.52  fof(f46,plain,(
% 1.23/0.52    v1_xboole_0(k1_xboole_0) | ~spl2_2),
% 1.23/0.52    inference(avatar_component_clause,[],[f45])).
% 1.23/0.52  fof(f45,plain,(
% 1.23/0.52    spl2_2 <=> v1_xboole_0(k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 1.23/0.52  fof(f77,plain,(
% 1.23/0.52    ( ! [X4,X5] : (~v1_xboole_0(X5) | X4 = X5 | ~r1_tarski(X4,X5)) )),
% 1.23/0.52    inference(resolution,[],[f72,f30])).
% 1.23/0.52  fof(f30,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f13])).
% 1.23/0.52  fof(f13,plain,(
% 1.23/0.52    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.23/0.52    inference(ennf_transformation,[],[f11])).
% 1.23/0.52  fof(f11,plain,(
% 1.23/0.52    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.23/0.52    inference(unused_predicate_definition_removal,[],[f1])).
% 1.23/0.52  fof(f1,axiom,(
% 1.23/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.23/0.52  fof(f72,plain,(
% 1.23/0.52    ( ! [X2,X1] : (r2_hidden(sK1(X2,X1),X2) | ~r1_tarski(X1,X2) | X1 = X2) )),
% 1.23/0.52    inference(resolution,[],[f34,f36])).
% 1.23/0.52  fof(f36,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f23])).
% 1.23/0.52  fof(f23,plain,(
% 1.23/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.23/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f21,f22])).
% 1.23/0.52  fof(f22,plain,(
% 1.23/0.52    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 1.23/0.52    introduced(choice_axiom,[])).
% 1.23/0.52  fof(f21,plain,(
% 1.23/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 1.23/0.52    inference(rectify,[],[f20])).
% 1.23/0.52  fof(f20,plain,(
% 1.23/0.52    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 1.23/0.52    inference(nnf_transformation,[],[f15])).
% 1.23/0.52  fof(f15,plain,(
% 1.23/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 1.23/0.52    inference(ennf_transformation,[],[f2])).
% 1.23/0.52  fof(f2,axiom,(
% 1.23/0.52    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 1.23/0.52  fof(f34,plain,(
% 1.23/0.52    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f19])).
% 1.23/0.52  fof(f19,plain,(
% 1.23/0.52    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.52    inference(flattening,[],[f18])).
% 1.23/0.52  fof(f18,plain,(
% 1.23/0.52    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.23/0.52    inference(nnf_transformation,[],[f4])).
% 1.23/0.52  fof(f4,axiom,(
% 1.23/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.23/0.52  fof(f42,plain,(
% 1.23/0.52    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl2_1),
% 1.23/0.52    inference(avatar_component_clause,[],[f41])).
% 1.23/0.52  fof(f41,plain,(
% 1.23/0.52    spl2_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.23/0.52  fof(f70,plain,(
% 1.23/0.52    ~spl2_6 | spl2_7 | ~spl2_5),
% 1.23/0.52    inference(avatar_split_clause,[],[f65,f57,f68,f62])).
% 1.23/0.52  fof(f62,plain,(
% 1.23/0.52    spl2_6 <=> v1_relat_1(k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.23/0.52  fof(f57,plain,(
% 1.23/0.52    spl2_5 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.23/0.52  fof(f65,plain,(
% 1.23/0.52    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | ~spl2_5),
% 1.23/0.52    inference(superposition,[],[f31,f58])).
% 1.23/0.52  fof(f58,plain,(
% 1.23/0.52    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl2_5),
% 1.23/0.52    inference(avatar_component_clause,[],[f57])).
% 1.23/0.52  fof(f31,plain,(
% 1.23/0.52    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.23/0.52    inference(cnf_transformation,[],[f14])).
% 1.23/0.52  fof(f14,plain,(
% 1.23/0.52    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 1.23/0.52    inference(ennf_transformation,[],[f6])).
% 1.23/0.53  fof(f6,axiom,(
% 1.23/0.53    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 1.23/0.53  fof(f64,plain,(
% 1.23/0.53    spl2_6 | ~spl2_3),
% 1.23/0.53    inference(avatar_split_clause,[],[f60,f49,f62])).
% 1.23/0.53  fof(f49,plain,(
% 1.23/0.53    spl2_3 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.23/0.53  fof(f60,plain,(
% 1.23/0.53    v1_relat_1(k1_xboole_0) | ~spl2_3),
% 1.23/0.53    inference(superposition,[],[f29,f50])).
% 1.23/0.53  fof(f50,plain,(
% 1.23/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl2_3),
% 1.23/0.53    inference(avatar_component_clause,[],[f49])).
% 1.23/0.53  fof(f29,plain,(
% 1.23/0.53    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 1.23/0.53    inference(cnf_transformation,[],[f5])).
% 1.23/0.53  fof(f5,axiom,(
% 1.23/0.53    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 1.23/0.53  fof(f59,plain,(
% 1.23/0.53    spl2_5),
% 1.23/0.53    inference(avatar_split_clause,[],[f27,f57])).
% 1.23/0.53  fof(f27,plain,(
% 1.23/0.53    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.23/0.53    inference(cnf_transformation,[],[f7])).
% 1.23/0.53  fof(f7,axiom,(
% 1.23/0.53    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 1.23/0.53  fof(f51,plain,(
% 1.23/0.53    spl2_3),
% 1.23/0.53    inference(avatar_split_clause,[],[f26,f49])).
% 1.23/0.53  fof(f26,plain,(
% 1.23/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.23/0.53    inference(cnf_transformation,[],[f8])).
% 1.23/0.53  fof(f8,axiom,(
% 1.23/0.53    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).
% 1.23/0.53  fof(f47,plain,(
% 1.23/0.53    spl2_2),
% 1.23/0.53    inference(avatar_split_clause,[],[f25,f45])).
% 1.23/0.53  fof(f25,plain,(
% 1.23/0.53    v1_xboole_0(k1_xboole_0)),
% 1.23/0.53    inference(cnf_transformation,[],[f3])).
% 1.23/0.53  fof(f3,axiom,(
% 1.23/0.53    v1_xboole_0(k1_xboole_0)),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.23/0.53  fof(f43,plain,(
% 1.23/0.53    ~spl2_1),
% 1.23/0.53    inference(avatar_split_clause,[],[f24,f41])).
% 1.23/0.53  fof(f24,plain,(
% 1.23/0.53    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.23/0.53    inference(cnf_transformation,[],[f17])).
% 1.23/0.53  fof(f17,plain,(
% 1.23/0.53    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).
% 1.23/0.53  fof(f16,plain,(
% 1.23/0.53    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 1.23/0.53    introduced(choice_axiom,[])).
% 1.23/0.53  fof(f12,plain,(
% 1.23/0.53    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 1.23/0.53    inference(ennf_transformation,[],[f10])).
% 1.23/0.53  fof(f10,negated_conjecture,(
% 1.23/0.53    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.23/0.53    inference(negated_conjecture,[],[f9])).
% 1.23/0.53  fof(f9,conjecture,(
% 1.23/0.53    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 1.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 1.23/0.53  % SZS output end Proof for theBenchmark
% 1.23/0.53  % (3271)------------------------------
% 1.23/0.53  % (3271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (3271)Termination reason: Refutation
% 1.23/0.53  
% 1.23/0.53  % (3271)Memory used [KB]: 10746
% 1.23/0.53  % (3271)Time elapsed: 0.124 s
% 1.23/0.53  % (3271)------------------------------
% 1.23/0.53  % (3271)------------------------------
% 1.23/0.53  % (3252)Refutation not found, incomplete strategy% (3252)------------------------------
% 1.23/0.53  % (3252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (3252)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (3252)Memory used [KB]: 1663
% 1.23/0.53  % (3252)Time elapsed: 0.116 s
% 1.23/0.53  % (3252)------------------------------
% 1.23/0.53  % (3252)------------------------------
% 1.23/0.53  % (3251)Success in time 0.162 s
%------------------------------------------------------------------------------
