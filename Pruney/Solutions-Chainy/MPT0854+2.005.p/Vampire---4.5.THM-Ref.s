%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:12 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   33 (  72 expanded)
%              Number of leaves         :    6 (  19 expanded)
%              Depth                    :   10
%              Number of atoms          :   57 ( 146 expanded)
%              Number of equality atoms :   10 (  24 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f51,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f24,f46,f50])).

fof(f50,plain,(
    spl5_2 ),
    inference(avatar_contradiction_clause,[],[f49])).

fof(f49,plain,
    ( $false
    | spl5_2 ),
    inference(subsumption_resolution,[],[f48,f23])).

fof(f23,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl5_2
  <=> r2_hidden(k1_mcart_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f48,plain,(
    r2_hidden(k1_mcart_1(sK0),sK1) ),
    inference(forward_demodulation,[],[f47,f29])).

fof(f29,plain,(
    k1_mcart_1(sK0) = sK3(sK0) ),
    inference(superposition,[],[f10,f25])).

fof(f25,plain,(
    sK0 = k4_tarski(sK3(sK0),sK4(sK0)) ),
    inference(resolution,[],[f12,f9])).

fof(f9,plain,(
    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( ( ~ r2_hidden(k2_mcart_1(X0),X2)
        | ~ r2_hidden(k1_mcart_1(X0),X1) )
      & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
       => ( r2_hidden(k2_mcart_1(X0),X2)
          & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

fof(f12,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
      | k4_tarski(sK3(X0),sK4(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ? [X3,X4] : k4_tarski(X3,X4) = X0
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ~ ( ! [X3,X4] : k4_tarski(X3,X4) != X0
        & r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

fof(f10,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f3])).

% (3461)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
fof(f3,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f47,plain,(
    r2_hidden(sK3(sK0),sK1) ),
    inference(resolution,[],[f27,f9])).

fof(f27,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X2,X3))
      | r2_hidden(sK3(sK0),X2) ) ),
    inference(superposition,[],[f13,f25])).

fof(f13,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f46,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f45])).

fof(f45,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f44,f19])).

fof(f19,plain,
    ( ~ r2_hidden(k2_mcart_1(sK0),sK2)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f17])).

fof(f17,plain,
    ( spl5_1
  <=> r2_hidden(k2_mcart_1(sK0),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f44,plain,(
    r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(forward_demodulation,[],[f43,f28])).

fof(f28,plain,(
    k2_mcart_1(sK0) = sK4(sK0) ),
    inference(superposition,[],[f11,f25])).

fof(f11,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f3])).

fof(f43,plain,(
    r2_hidden(sK4(sK0),sK2) ),
    inference(resolution,[],[f26,f9])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK0,k2_zfmisc_1(X0,X1))
      | r2_hidden(sK4(sK0),X1) ) ),
    inference(superposition,[],[f14,f25])).

fof(f14,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f24,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f8,f21,f17])).

fof(f8,plain,
    ( ~ r2_hidden(k1_mcart_1(sK0),sK1)
    | ~ r2_hidden(k2_mcart_1(sK0),sK2) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:14:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (3454)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.43  % (3465)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.43  % (3454)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f51,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(avatar_sat_refutation,[],[f24,f46,f50])).
% 0.22/0.43  fof(f50,plain,(
% 0.22/0.43    spl5_2),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f49])).
% 0.22/0.43  fof(f49,plain,(
% 0.22/0.43    $false | spl5_2),
% 0.22/0.43    inference(subsumption_resolution,[],[f48,f23])).
% 0.22/0.43  fof(f23,plain,(
% 0.22/0.43    ~r2_hidden(k1_mcart_1(sK0),sK1) | spl5_2),
% 0.22/0.43    inference(avatar_component_clause,[],[f21])).
% 0.22/0.43  fof(f21,plain,(
% 0.22/0.43    spl5_2 <=> r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.43  fof(f48,plain,(
% 0.22/0.43    r2_hidden(k1_mcart_1(sK0),sK1)),
% 0.22/0.43    inference(forward_demodulation,[],[f47,f29])).
% 0.22/0.43  fof(f29,plain,(
% 0.22/0.43    k1_mcart_1(sK0) = sK3(sK0)),
% 0.22/0.43    inference(superposition,[],[f10,f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    sK0 = k4_tarski(sK3(sK0),sK4(sK0))),
% 0.22/0.43    inference(resolution,[],[f12,f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    r2_hidden(sK0,k2_zfmisc_1(sK1,sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0,X1,X2] : ((~r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(k1_mcart_1(X0),X1)) & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.43    inference(ennf_transformation,[],[f5])).
% 0.22/0.43  fof(f5,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.43    inference(negated_conjecture,[],[f4])).
% 0.22/0.43  fof(f4,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (~r2_hidden(X0,k2_zfmisc_1(X1,X2)) | k4_tarski(sK3(X0),sK4(X0)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ! [X0,X1,X2] : (? [X3,X4] : k4_tarski(X3,X4) = X0 | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.43    inference(ennf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : ~(! [X3,X4] : k4_tarski(X3,X4) != X0 & r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  % (3461)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.43  fof(f3,axiom,(
% 0.22/0.43    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.43  fof(f47,plain,(
% 0.22/0.43    r2_hidden(sK3(sK0),sK1)),
% 0.22/0.43    inference(resolution,[],[f27,f9])).
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    ( ! [X2,X3] : (~r2_hidden(sK0,k2_zfmisc_1(X2,X3)) | r2_hidden(sK3(sK0),X2)) )),
% 0.22/0.43    inference(superposition,[],[f13,f25])).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.22/0.43  fof(f46,plain,(
% 0.22/0.43    spl5_1),
% 0.22/0.43    inference(avatar_contradiction_clause,[],[f45])).
% 0.22/0.43  fof(f45,plain,(
% 0.22/0.43    $false | spl5_1),
% 0.22/0.43    inference(subsumption_resolution,[],[f44,f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    ~r2_hidden(k2_mcart_1(sK0),sK2) | spl5_1),
% 0.22/0.43    inference(avatar_component_clause,[],[f17])).
% 0.22/0.43  fof(f17,plain,(
% 0.22/0.43    spl5_1 <=> r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.22/0.43    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.43  fof(f44,plain,(
% 0.22/0.43    r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.22/0.43    inference(forward_demodulation,[],[f43,f28])).
% 0.22/0.43  fof(f28,plain,(
% 0.22/0.43    k2_mcart_1(sK0) = sK4(sK0)),
% 0.22/0.43    inference(superposition,[],[f11,f25])).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.43    inference(cnf_transformation,[],[f3])).
% 0.22/0.43  fof(f43,plain,(
% 0.22/0.43    r2_hidden(sK4(sK0),sK2)),
% 0.22/0.43    inference(resolution,[],[f26,f9])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r2_hidden(sK0,k2_zfmisc_1(X0,X1)) | r2_hidden(sK4(sK0),X1)) )),
% 0.22/0.43    inference(superposition,[],[f14,f25])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f24,plain,(
% 0.22/0.43    ~spl5_1 | ~spl5_2),
% 0.22/0.43    inference(avatar_split_clause,[],[f8,f21,f17])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ~r2_hidden(k1_mcart_1(sK0),sK1) | ~r2_hidden(k2_mcart_1(sK0),sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (3454)------------------------------
% 0.22/0.44  % (3454)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (3454)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (3454)Memory used [KB]: 10618
% 0.22/0.44  % (3454)Time elapsed: 0.006 s
% 0.22/0.44  % (3454)------------------------------
% 0.22/0.44  % (3454)------------------------------
% 0.22/0.44  % (3453)Success in time 0.076 s
%------------------------------------------------------------------------------
