%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:35 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   58 (  82 expanded)
%              Number of leaves         :   16 (  35 expanded)
%              Depth                    :    7
%              Number of atoms          :  125 ( 183 expanded)
%              Number of equality atoms :   30 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f573,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f63,f71,f114,f120,f492,f540,f562])).

fof(f562,plain,
    ( spl4_1
    | ~ spl4_65 ),
    inference(avatar_split_clause,[],[f558,f536,f51])).

fof(f51,plain,
    ( spl4_1
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f536,plain,
    ( spl4_65
  <=> k1_xboole_0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).

fof(f558,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_65 ),
    inference(trivial_inequality_removal,[],[f555])).

fof(f555,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK1)
    | ~ spl4_65 ),
    inference(superposition,[],[f45,f538])).

fof(f538,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_65 ),
    inference(avatar_component_clause,[],[f536])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f540,plain,
    ( spl4_65
    | ~ spl4_59 ),
    inference(avatar_split_clause,[],[f529,f489,f536])).

fof(f489,plain,
    ( spl4_59
  <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).

fof(f529,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK1)
    | ~ spl4_59 ),
    inference(superposition,[],[f33,f491])).

fof(f491,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl4_59 ),
    inference(avatar_component_clause,[],[f489])).

fof(f33,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f492,plain,
    ( spl4_59
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f463,f117,f68,f489])).

fof(f68,plain,
    ( spl4_4
  <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f117,plain,
    ( spl4_11
  <=> k1_xboole_0 = k3_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f463,plain,
    ( k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(superposition,[],[f306,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f306,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(X0,sK2)))
    | ~ spl4_11 ),
    inference(superposition,[],[f35,f125])).

fof(f125,plain,
    ( ! [X1] : k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X1),k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f48,f119])).

fof(f119,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f48,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f120,plain,
    ( spl4_11
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f115,f55,f117])).

fof(f55,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f115,plain,
    ( k1_xboole_0 = k3_xboole_0(sK0,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f56,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f56,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f114,plain,
    ( spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f113,f60,f55])).

fof(f60,plain,
    ( spl4_3
  <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f113,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl4_3 ),
    inference(resolution,[],[f64,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f64,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k4_xboole_0(sK1,sK2),X0)
        | r1_xboole_0(sK0,X0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f62,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f62,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f71,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f65,f60,f68])).

fof(f65,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl4_3 ),
    inference(resolution,[],[f62,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f63,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f30,f60])).

fof(f30,plain,(
    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ~ r1_xboole_0(sK0,sK2)
      | ~ r1_tarski(sK0,sK1) )
    & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ r1_xboole_0(X0,X2)
          | ~ r1_tarski(X0,X1) )
        & r1_tarski(X0,k4_xboole_0(X1,X2)) )
   => ( ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_tarski(sK0,sK1) )
      & r1_tarski(sK0,k4_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,X2)
        | ~ r1_tarski(X0,X1) )
      & r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,k4_xboole_0(X1,X2))
       => ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f58,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f31,f55,f51])).

fof(f31,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:46:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.42  % (9106)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.44  % (9123)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.47  % (9109)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (9112)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (9121)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (9118)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (9113)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (9110)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (9107)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (9117)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (9120)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (9117)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % (9115)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (9111)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (9108)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.50  % (9114)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.50  % SZS output start Proof for theBenchmark
% 0.22/0.50  fof(f573,plain,(
% 0.22/0.50    $false),
% 0.22/0.50    inference(avatar_sat_refutation,[],[f58,f63,f71,f114,f120,f492,f540,f562])).
% 0.22/0.50  fof(f562,plain,(
% 0.22/0.50    spl4_1 | ~spl4_65),
% 0.22/0.50    inference(avatar_split_clause,[],[f558,f536,f51])).
% 0.22/0.50  fof(f51,plain,(
% 0.22/0.50    spl4_1 <=> r1_tarski(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.50  fof(f536,plain,(
% 0.22/0.50    spl4_65 <=> k1_xboole_0 = k4_xboole_0(sK0,sK1)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_65])])).
% 0.22/0.50  fof(f558,plain,(
% 0.22/0.50    r1_tarski(sK0,sK1) | ~spl4_65),
% 0.22/0.50    inference(trivial_inequality_removal,[],[f555])).
% 0.22/0.50  fof(f555,plain,(
% 0.22/0.50    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK1) | ~spl4_65),
% 0.22/0.50    inference(superposition,[],[f45,f538])).
% 0.22/0.50  fof(f538,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl4_65),
% 0.22/0.50    inference(avatar_component_clause,[],[f536])).
% 0.22/0.50  fof(f45,plain,(
% 0.22/0.50    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.50    inference(cnf_transformation,[],[f29])).
% 0.22/0.50  fof(f29,plain,(
% 0.22/0.50    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.22/0.50    inference(nnf_transformation,[],[f4])).
% 0.22/0.50  fof(f4,axiom,(
% 0.22/0.50    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.50  fof(f540,plain,(
% 0.22/0.50    spl4_65 | ~spl4_59),
% 0.22/0.50    inference(avatar_split_clause,[],[f529,f489,f536])).
% 0.22/0.50  fof(f489,plain,(
% 0.22/0.50    spl4_59 <=> k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_59])])).
% 0.22/0.50  fof(f529,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK0,sK1) | ~spl4_59),
% 0.22/0.50    inference(superposition,[],[f33,f491])).
% 0.22/0.50  fof(f491,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | ~spl4_59),
% 0.22/0.50    inference(avatar_component_clause,[],[f489])).
% 0.22/0.50  fof(f33,plain,(
% 0.22/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.50    inference(cnf_transformation,[],[f9])).
% 0.22/0.50  fof(f9,axiom,(
% 0.22/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.50  fof(f492,plain,(
% 0.22/0.50    spl4_59 | ~spl4_4 | ~spl4_11),
% 0.22/0.50    inference(avatar_split_clause,[],[f463,f117,f68,f489])).
% 0.22/0.50  fof(f68,plain,(
% 0.22/0.50    spl4_4 <=> k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.50  fof(f117,plain,(
% 0.22/0.50    spl4_11 <=> k1_xboole_0 = k3_xboole_0(sK0,sK2)),
% 0.22/0.50    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.50  fof(f463,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) | (~spl4_4 | ~spl4_11)),
% 0.22/0.50    inference(superposition,[],[f306,f70])).
% 0.22/0.50  fof(f70,plain,(
% 0.22/0.50    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl4_4),
% 0.22/0.50    inference(avatar_component_clause,[],[f68])).
% 0.22/0.50  fof(f306,plain,(
% 0.22/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),k4_xboole_0(sK0,k4_xboole_0(X0,sK2)))) ) | ~spl4_11),
% 0.22/0.50    inference(superposition,[],[f35,f125])).
% 0.22/0.50  fof(f125,plain,(
% 0.22/0.50    ( ! [X1] : (k4_xboole_0(sK0,k4_xboole_0(X1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,X1),k1_xboole_0)) ) | ~spl4_11),
% 0.22/0.50    inference(superposition,[],[f48,f119])).
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl4_11),
% 0.22/0.51    inference(avatar_component_clause,[],[f117])).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.22/0.51  fof(f120,plain,(
% 0.22/0.51    spl4_11 | ~spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f115,f55,f117])).
% 0.22/0.51  fof(f55,plain,(
% 0.22/0.51    spl4_2 <=> r1_xboole_0(sK0,sK2)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.51  fof(f115,plain,(
% 0.22/0.51    k1_xboole_0 = k3_xboole_0(sK0,sK2) | ~spl4_2),
% 0.22/0.51    inference(resolution,[],[f56,f43])).
% 0.22/0.51  fof(f43,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(nnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    r1_xboole_0(sK0,sK2) | ~spl4_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f55])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    spl4_2 | ~spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f113,f60,f55])).
% 0.22/0.51  fof(f60,plain,(
% 0.22/0.51    spl4_3 <=> r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    r1_xboole_0(sK0,sK2) | ~spl4_3),
% 0.22/0.51    inference(resolution,[],[f64,f34])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (~r1_xboole_0(k4_xboole_0(sK1,sK2),X0) | r1_xboole_0(sK0,X0)) ) | ~spl4_3),
% 0.22/0.51    inference(resolution,[],[f62,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 0.22/0.51    inference(flattening,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f12])).
% 0.22/0.51  fof(f12,axiom,(
% 0.22/0.51    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 0.22/0.51  fof(f62,plain,(
% 0.22/0.51    r1_tarski(sK0,k4_xboole_0(sK1,sK2)) | ~spl4_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f60])).
% 0.22/0.51  fof(f71,plain,(
% 0.22/0.51    spl4_4 | ~spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f65,f60,f68])).
% 0.22/0.51  fof(f65,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) | ~spl4_3),
% 0.22/0.51    inference(resolution,[],[f62,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f29])).
% 0.22/0.51  fof(f63,plain,(
% 0.22/0.51    spl4_3),
% 0.22/0.51    inference(avatar_split_clause,[],[f30,f60])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    (~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2))) => ((~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)) & r1_tarski(sK0,k4_xboole_0(sK1,sK2)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ? [X0,X1,X2] : ((~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) & r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 0.22/0.51    inference(ennf_transformation,[],[f17])).
% 0.22/0.51  fof(f17,negated_conjecture,(
% 0.22/0.51    ~! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.51    inference(negated_conjecture,[],[f16])).
% 0.22/0.51  fof(f16,conjecture,(
% 0.22/0.51    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ~spl4_1 | ~spl4_2),
% 0.22/0.51    inference(avatar_split_clause,[],[f31,f55,f51])).
% 0.22/0.51  fof(f31,plain,(
% 0.22/0.51    ~r1_xboole_0(sK0,sK2) | ~r1_tarski(sK0,sK1)),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (9117)------------------------------
% 0.22/0.51  % (9117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (9117)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (9117)Memory used [KB]: 11001
% 0.22/0.51  % (9117)Time elapsed: 0.079 s
% 0.22/0.51  % (9117)------------------------------
% 0.22/0.51  % (9117)------------------------------
% 0.22/0.51  % (9105)Success in time 0.144 s
%------------------------------------------------------------------------------
