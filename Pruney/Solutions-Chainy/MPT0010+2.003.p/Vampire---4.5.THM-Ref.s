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
% DateTime   : Thu Dec  3 12:29:32 EST 2020

% Result     : Theorem 1.23s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :   27 (  32 expanded)
%              Number of leaves         :    7 (   9 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  65 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f29,plain,(
    $false ),
    inference(subsumption_resolution,[],[f28,f19])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f28,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[],[f27,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f27,plain,(
    r2_hidden(sK1(sK0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f26,f18])).

fof(f18,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != sK0
    & r1_tarski(sK0,k1_xboole_0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_xboole_0 != X0
        & r1_tarski(X0,k1_xboole_0) )
   => ( k1_xboole_0 != sK0
      & r1_tarski(sK0,k1_xboole_0) ) ),
    introduced(choice_axiom,[])).

% (17975)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% (17969)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (17991)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% (17995)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% (17985)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (17971)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
fof(f9,plain,(
    ? [X0] :
      ( k1_xboole_0 != X0
      & r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( r1_tarski(X0,k1_xboole_0)
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f26,plain,
    ( r2_hidden(sK1(sK0),k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f25,f21])).

fof(f21,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f15])).

fof(f15,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK1(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f25,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | r2_hidden(X0,k1_xboole_0) ) ),
    inference(resolution,[],[f22,f17])).

fof(f17,plain,(
    r1_tarski(sK0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n004.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:05:39 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.23/0.54  % (17976)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.23/0.54  % (17976)Refutation found. Thanks to Tanya!
% 1.23/0.54  % SZS status Theorem for theBenchmark
% 1.23/0.54  % SZS output start Proof for theBenchmark
% 1.23/0.54  fof(f29,plain,(
% 1.23/0.54    $false),
% 1.23/0.54    inference(subsumption_resolution,[],[f28,f19])).
% 1.23/0.54  fof(f19,plain,(
% 1.23/0.54    v1_xboole_0(k1_xboole_0)),
% 1.23/0.54    inference(cnf_transformation,[],[f3])).
% 1.23/0.54  fof(f3,axiom,(
% 1.23/0.54    v1_xboole_0(k1_xboole_0)),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.23/0.54  fof(f28,plain,(
% 1.23/0.54    ~v1_xboole_0(k1_xboole_0)),
% 1.23/0.54    inference(resolution,[],[f27,f20])).
% 1.23/0.54  fof(f20,plain,(
% 1.23/0.54    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 1.23/0.54    inference(cnf_transformation,[],[f10])).
% 1.23/0.54  fof(f10,plain,(
% 1.23/0.54    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 1.23/0.54    inference(ennf_transformation,[],[f8])).
% 1.23/0.54  fof(f8,plain,(
% 1.23/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 1.23/0.54    inference(unused_predicate_definition_removal,[],[f1])).
% 1.23/0.54  fof(f1,axiom,(
% 1.23/0.54    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.23/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.23/0.54  fof(f27,plain,(
% 1.23/0.54    r2_hidden(sK1(sK0),k1_xboole_0)),
% 1.23/0.54    inference(subsumption_resolution,[],[f26,f18])).
% 1.23/0.54  fof(f18,plain,(
% 1.23/0.54    k1_xboole_0 != sK0),
% 1.23/0.54    inference(cnf_transformation,[],[f14])).
% 1.23/0.54  fof(f14,plain,(
% 1.23/0.54    k1_xboole_0 != sK0 & r1_tarski(sK0,k1_xboole_0)),
% 1.23/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f9,f13])).
% 1.23/0.54  fof(f13,plain,(
% 1.23/0.54    ? [X0] : (k1_xboole_0 != X0 & r1_tarski(X0,k1_xboole_0)) => (k1_xboole_0 != sK0 & r1_tarski(sK0,k1_xboole_0))),
% 1.23/0.54    introduced(choice_axiom,[])).
% 1.23/0.54  % (17975)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.54  % (17969)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.38/0.55  % (17991)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.55  % (17995)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.38/0.55  % (17985)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.38/0.55  % (17971)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.38/0.55  fof(f9,plain,(
% 1.38/0.55    ? [X0] : (k1_xboole_0 != X0 & r1_tarski(X0,k1_xboole_0))),
% 1.38/0.55    inference(ennf_transformation,[],[f6])).
% 1.38/0.55  fof(f6,negated_conjecture,(
% 1.38/0.55    ~! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.38/0.55    inference(negated_conjecture,[],[f5])).
% 1.38/0.55  fof(f5,conjecture,(
% 1.38/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.38/0.55  fof(f26,plain,(
% 1.38/0.55    r2_hidden(sK1(sK0),k1_xboole_0) | k1_xboole_0 = sK0),
% 1.38/0.55    inference(resolution,[],[f25,f21])).
% 1.38/0.55  fof(f21,plain,(
% 1.38/0.55    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.38/0.55    inference(cnf_transformation,[],[f16])).
% 1.38/0.55  fof(f16,plain,(
% 1.38/0.55    ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0)),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f11,f15])).
% 1.38/0.55  fof(f15,plain,(
% 1.38/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK1(X0),X0))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f11,plain,(
% 1.38/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.38/0.55    inference(ennf_transformation,[],[f4])).
% 1.38/0.55  fof(f4,axiom,(
% 1.38/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.38/0.55  fof(f25,plain,(
% 1.38/0.55    ( ! [X0] : (~r2_hidden(X0,sK0) | r2_hidden(X0,k1_xboole_0)) )),
% 1.38/0.55    inference(resolution,[],[f22,f17])).
% 1.38/0.55  fof(f17,plain,(
% 1.38/0.55    r1_tarski(sK0,k1_xboole_0)),
% 1.38/0.55    inference(cnf_transformation,[],[f14])).
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r2_hidden(X2,X0) | r2_hidden(X2,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f12])).
% 1.38/0.55  fof(f12,plain,(
% 1.38/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f7])).
% 1.38/0.55  fof(f7,plain,(
% 1.38/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.55    inference(unused_predicate_definition_removal,[],[f2])).
% 1.38/0.55  fof(f2,axiom,(
% 1.38/0.55    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 1.38/0.55  % SZS output end Proof for theBenchmark
% 1.38/0.55  % (17976)------------------------------
% 1.38/0.55  % (17976)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (17976)Termination reason: Refutation
% 1.38/0.55  
% 1.38/0.55  % (17976)Memory used [KB]: 6140
% 1.38/0.55  % (17976)Time elapsed: 0.114 s
% 1.38/0.55  % (17976)------------------------------
% 1.38/0.55  % (17976)------------------------------
% 1.38/0.55  % (17968)Success in time 0.178 s
%------------------------------------------------------------------------------
