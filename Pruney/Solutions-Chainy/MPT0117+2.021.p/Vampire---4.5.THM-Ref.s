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
% DateTime   : Thu Dec  3 12:32:54 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   34 (  60 expanded)
%              Number of leaves         :    6 (  14 expanded)
%              Depth                    :    9
%              Number of atoms          :   68 ( 134 expanded)
%              Number of equality atoms :    5 (   8 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f57,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f47,f56])).

fof(f56,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f55])).

fof(f55,plain,
    ( $false
    | spl3_2 ),
    inference(subsumption_resolution,[],[f54,f17])).

fof(f17,plain,(
    r1_tarski(sK2,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(k5_xboole_0(X0,X2),X1)
      & r1_tarski(X2,X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_tarski(X2,X1)
          & r1_tarski(X0,X1) )
       => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f54,plain,
    ( ~ r1_tarski(sK2,sK1)
    | spl3_2 ),
    inference(forward_demodulation,[],[f49,f24])).

fof(f24,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f20,f16])).

fof(f16,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f49,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | spl3_2 ),
    inference(resolution,[],[f37,f21])).

fof(f21,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f37,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK0),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f36])).

fof(f36,plain,
    ( spl3_2
  <=> r1_tarski(k4_xboole_0(sK2,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f47,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f46])).

fof(f46,plain,
    ( $false
    | spl3_1 ),
    inference(subsumption_resolution,[],[f45,f16])).

fof(f45,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl3_1 ),
    inference(forward_demodulation,[],[f40,f25])).

fof(f25,plain,(
    sK1 = k2_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f20,f17])).

fof(f40,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK2,sK1))
    | spl3_1 ),
    inference(resolution,[],[f34,f21])).

fof(f34,plain,
    ( ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl3_1
  <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f38,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f30,f36,f33])).

fof(f30,plain,
    ( ~ r1_tarski(k4_xboole_0(sK2,sK0),sK1)
    | ~ r1_tarski(k4_xboole_0(sK0,sK2),sK1) ),
    inference(resolution,[],[f23,f18])).

fof(f18,plain,(
    ~ r1_tarski(k5_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X1),X2)
      | ~ r1_tarski(k4_xboole_0(X1,X0),X2)
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k4_xboole_0(X1,X0),X2)
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
     => r1_tarski(k5_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 19:31:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (29866)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.44  % (29874)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.44  % (29866)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f38,f47,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    spl3_2),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f55])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    $false | spl3_2),
% 0.21/0.44    inference(subsumption_resolution,[],[f54,f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    r1_tarski(sK2,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & r1_tarski(X2,X1) & r1_tarski(X0,X1))),
% 0.21/0.44    inference(flattening,[],[f8])).
% 0.21/0.44  fof(f8,plain,(
% 0.21/0.44    ? [X0,X1,X2] : (~r1_tarski(k5_xboole_0(X0,X2),X1) & (r1_tarski(X2,X1) & r1_tarski(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.44    inference(negated_conjecture,[],[f6])).
% 0.21/0.44  fof(f6,conjecture,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).
% 0.21/0.44  fof(f54,plain,(
% 0.21/0.44    ~r1_tarski(sK2,sK1) | spl3_2),
% 0.21/0.44    inference(forward_demodulation,[],[f49,f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    sK1 = k2_xboole_0(sK0,sK1)),
% 0.21/0.44    inference(resolution,[],[f20,f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    r1_tarski(sK0,sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.44    inference(cnf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,plain,(
% 0.21/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ~r1_tarski(sK2,k2_xboole_0(sK0,sK1)) | spl3_2),
% 0.21/0.44    inference(resolution,[],[f37,f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    ~r1_tarski(k4_xboole_0(sK2,sK0),sK1) | spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    spl3_2 <=> r1_tarski(k4_xboole_0(sK2,sK0),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f46])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    $false | spl3_1),
% 0.21/0.44    inference(subsumption_resolution,[],[f45,f16])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ~r1_tarski(sK0,sK1) | spl3_1),
% 0.21/0.44    inference(forward_demodulation,[],[f40,f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    sK1 = k2_xboole_0(sK2,sK1)),
% 0.21/0.44    inference(resolution,[],[f20,f17])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ~r1_tarski(sK0,k2_xboole_0(sK2,sK1)) | spl3_1),
% 0.21/0.44    inference(resolution,[],[f34,f21])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ~r1_tarski(k4_xboole_0(sK0,sK2),sK1) | spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl3_1 <=> r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ~spl3_1 | ~spl3_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f30,f36,f33])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ~r1_tarski(k4_xboole_0(sK2,sK0),sK1) | ~r1_tarski(k4_xboole_0(sK0,sK2),sK1)),
% 0.21/0.44    inference(resolution,[],[f23,f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ~r1_tarski(k5_xboole_0(sK0,sK2),sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X1),X2) | ~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X1),X2) | ~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.21/0.44    inference(flattening,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X1),X2) | (~r1_tarski(k4_xboole_0(X1,X0),X2) | ~r1_tarski(k4_xboole_0(X0,X1),X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((r1_tarski(k4_xboole_0(X1,X0),X2) & r1_tarski(k4_xboole_0(X0,X1),X2)) => r1_tarski(k5_xboole_0(X0,X1),X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_xboole_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (29866)------------------------------
% 0.21/0.44  % (29866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (29866)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (29866)Memory used [KB]: 10618
% 0.21/0.44  % (29866)Time elapsed: 0.006 s
% 0.21/0.44  % (29866)------------------------------
% 0.21/0.44  % (29866)------------------------------
% 0.21/0.44  % (29862)Success in time 0.075 s
%------------------------------------------------------------------------------
