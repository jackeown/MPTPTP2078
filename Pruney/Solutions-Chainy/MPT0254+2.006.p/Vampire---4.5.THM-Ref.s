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
% DateTime   : Thu Dec  3 12:39:13 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   36 (  47 expanded)
%              Number of leaves         :   10 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   64 (  86 expanded)
%              Number of equality atoms :   24 (  33 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f64,f71,f78,f89])).

fof(f89,plain,
    ( ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f87,f82])).

fof(f82,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f77,f70])).

fof(f70,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl2_3
  <=> k1_xboole_0 = k1_tarski(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f77,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_5
  <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f87,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_3 ),
    inference(superposition,[],[f49,f70])).

fof(f49,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f78,plain,
    ( spl2_5
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f57,f53,f76])).

fof(f53,plain,
    ( spl2_1
  <=> k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f57,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f30,f54])).

fof(f54,plain,
    ( k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f71,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f67,f62,f69])).

fof(f62,plain,
    ( spl2_2
  <=> r1_tarski(k1_tarski(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f67,plain,
    ( k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f65,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_tarski(sK0))
    | k1_xboole_0 = k1_tarski(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f63,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f63,plain,
    ( r1_tarski(k1_tarski(sK0),k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f64,plain,
    ( spl2_2
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f56,f53,f62])).

fof(f56,plain,
    ( r1_tarski(k1_tarski(sK0),k1_xboole_0)
    | ~ spl2_1 ),
    inference(superposition,[],[f31,f54])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f55,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:08:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (14241)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (14242)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (14229)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (14241)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f55,f64,f71,f78,f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    ~spl2_3 | ~spl2_5),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f88])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    $false | (~spl2_3 | ~spl2_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f87,f82])).
% 0.21/0.51  fof(f82,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl2_3 | ~spl2_5)),
% 0.21/0.51    inference(forward_demodulation,[],[f77,f70])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tarski(sK0) | ~spl2_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    spl2_3 <=> k1_xboole_0 = k1_tarski(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.51  fof(f77,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_xboole_0) | ~spl2_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f76])).
% 0.21/0.51  fof(f76,plain,(
% 0.21/0.51    spl2_5 <=> k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    k1_xboole_0 != k4_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_3),
% 0.21/0.51    inference(superposition,[],[f49,f70])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.21/0.51    inference(equality_resolution,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f21])).
% 0.21/0.51  fof(f21,axiom,(
% 0.21/0.51    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl2_5 | ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f57,f53,f76])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    spl2_1 <=> k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),k1_xboole_0) | ~spl2_1),
% 0.21/0.51    inference(superposition,[],[f30,f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) | ~spl2_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f53])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    spl2_3 | ~spl2_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f67,f62,f69])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl2_2 <=> r1_tarski(k1_tarski(sK0),k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.51  fof(f67,plain,(
% 0.21/0.51    k1_xboole_0 = k1_tarski(sK0) | ~spl2_2),
% 0.21/0.51    inference(subsumption_resolution,[],[f65,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.51  fof(f65,plain,(
% 0.21/0.51    ~r1_tarski(k1_xboole_0,k1_tarski(sK0)) | k1_xboole_0 = k1_tarski(sK0) | ~spl2_2),
% 0.21/0.51    inference(resolution,[],[f63,f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    r1_tarski(k1_tarski(sK0),k1_xboole_0) | ~spl2_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f62])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    spl2_2 | ~spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f56,f53,f62])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    r1_tarski(k1_tarski(sK0),k1_xboole_0) | ~spl2_1),
% 0.21/0.51    inference(superposition,[],[f31,f54])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    spl2_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f29,f53])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.51    inference(ennf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.51    inference(negated_conjecture,[],[f22])).
% 0.21/0.51  fof(f22,conjecture,(
% 0.21/0.51    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (14241)------------------------------
% 0.21/0.51  % (14241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (14241)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (14241)Memory used [KB]: 6268
% 0.21/0.51  % (14241)Time elapsed: 0.057 s
% 0.21/0.51  % (14241)------------------------------
% 0.21/0.51  % (14241)------------------------------
% 0.21/0.52  % (14213)Success in time 0.151 s
%------------------------------------------------------------------------------
