%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:51 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   35 (  59 expanded)
%              Number of leaves         :    5 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 141 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f55,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f19,f24,f27,f31,f34,f54])).

fof(f54,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f53])).

fof(f53,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f49,f13])).

fof(f13,plain,
    ( ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f12,plain,
    ( spl4_1
  <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f49,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f38,f23])).

fof(f23,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl4_3
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f38,plain,
    ( ! [X2,X3] :
        ( ~ r2_hidden(X2,X3)
        | r2_hidden(k4_tarski(sK0,X2),k2_zfmisc_1(sK2,X3)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f10,f18])).

fof(f18,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f16])).

fof(f16,plain,
    ( spl4_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f10,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

fof(f34,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_contradiction_clause,[],[f33])).

fof(f33,plain,
    ( $false
    | ~ spl4_1
    | spl4_2 ),
    inference(subsumption_resolution,[],[f28,f17])).

fof(f17,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f16])).

fof(f28,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl4_1 ),
    inference(resolution,[],[f8,f14])).

fof(f14,plain,
    ( r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f12])).

fof(f8,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f31,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f30])).

fof(f30,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f29,f22])).

fof(f22,plain,
    ( ~ r2_hidden(sK1,sK3)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f21])).

fof(f29,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_1 ),
    inference(resolution,[],[f9,f14])).

fof(f9,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | r2_hidden(X1,X3) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f27,plain,
    ( ~ spl4_3
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f26,f16,f12,f21])).

fof(f26,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f25,f14])).

fof(f25,plain,
    ( ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f5,f18])).

fof(f5,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ r2_hidden(sK1,sK3)
    | ~ r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,plain,(
    ? [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <~> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      <=> ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f2])).

fof(f2,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f24,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f7,f21,f12])).

fof(f7,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f19,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f6,f16,f12])).

fof(f6,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f4])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:30:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  % (9791)dis+1_8_afp=4000:afq=1.1:amm=sco:gsp=input_only:nm=64:newcnf=on:nwc=4:sac=on:sp=occurrence:updr=off_191 on theBenchmark
% 0.21/0.48  % (9799)dis+11_40_afr=on:afp=40000:afq=1.2:amm=sco:anc=none:br=off:fsr=off:gs=on:nm=64:nwc=1:sas=z3:sos=all:sp=reverse_arity:thf=on:urr=on:updr=off_2 on theBenchmark
% 0.21/0.48  % (9791)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f19,f24,f27,f31,f34,f54])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f53])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    $false | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f49,f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    spl4_1 <=> r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | (~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(resolution,[],[f38,f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    r2_hidden(sK1,sK3) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    spl4_3 <=> r2_hidden(sK1,sK3)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~r2_hidden(X2,X3) | r2_hidden(k4_tarski(sK0,X2),k2_zfmisc_1(sK2,X3))) ) | ~spl4_2),
% 0.21/0.48    inference(resolution,[],[f10,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    spl4_2 <=> r2_hidden(sK0,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f10,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(X0,X2) | ~r2_hidden(X1,X3) | r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ~spl4_1 | spl4_2),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    $false | (~spl4_1 | spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f28,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ~r2_hidden(sK0,sK2) | spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f16])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f8,f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f12])).
% 0.21/0.48  fof(f8,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X0,X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ~spl4_1 | spl4_3),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    $false | (~spl4_1 | spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f29,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK3) | spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f21])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    r2_hidden(sK1,sK3) | ~spl4_1),
% 0.21/0.48    inference(resolution,[],[f9,f14])).
% 0.21/0.48  fof(f9,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | r2_hidden(X1,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ~spl4_3 | ~spl4_1 | ~spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f26,f16,f12,f21])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK3) | (~spl4_1 | ~spl4_2)),
% 0.21/0.48    inference(subsumption_resolution,[],[f25,f14])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3)) | ~spl4_2),
% 0.21/0.48    inference(subsumption_resolution,[],[f5,f18])).
% 0.21/0.48  fof(f5,plain,(
% 0.21/0.48    ~r2_hidden(sK0,sK2) | ~r2_hidden(sK1,sK3) | ~r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,plain,(
% 0.21/0.48    ? [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <~> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.48    inference(negated_conjecture,[],[f2])).
% 0.21/0.48  fof(f2,conjecture,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    spl4_1 | spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f7,f21,f12])).
% 0.21/0.48  fof(f7,plain,(
% 0.21/0.48    r2_hidden(sK1,sK3) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    spl4_1 | spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f6,f16,f12])).
% 0.21/0.48  fof(f6,plain,(
% 0.21/0.48    r2_hidden(sK0,sK2) | r2_hidden(k4_tarski(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (9791)------------------------------
% 0.21/0.48  % (9791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (9791)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (9791)Memory used [KB]: 5373
% 0.21/0.48  % (9791)Time elapsed: 0.066 s
% 0.21/0.48  % (9791)------------------------------
% 0.21/0.48  % (9791)------------------------------
% 0.21/0.48  % (9781)Success in time 0.128 s
%------------------------------------------------------------------------------
