%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:01 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   39 (  86 expanded)
%              Number of leaves         :    8 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 140 expanded)
%              Number of equality atoms :   20 (  60 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f65,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f55,f64])).

fof(f64,plain,(
    ~ spl3_1 ),
    inference(avatar_contradiction_clause,[],[f63])).

fof(f63,plain,
    ( $false
    | ~ spl3_1 ),
    inference(subsumption_resolution,[],[f57,f47])).

fof(f47,plain,(
    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK0) ),
    inference(superposition,[],[f21,f42])).

fof(f42,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f24,f22])).

fof(f22,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2)) ),
    inference(definition_unfolding,[],[f12,f14])).

fof(f14,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f12,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) != k1_tarski(X2)
      & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
       => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => k2_tarski(X0,X1) = k1_tarski(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2))
      | X0 = X2 ) ),
    inference(definition_unfolding,[],[f19,f14])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( X0 = X2
      | ~ r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),k1_tarski(X2))
     => X0 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

fof(f21,plain,(
    k2_tarski(sK0,sK1) != k2_tarski(sK2,sK2) ),
    inference(definition_unfolding,[],[f13,f14])).

fof(f13,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f57,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK0,sK0)
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f33,f42])).

fof(f33,plain,
    ( k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl3_1
  <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f55,plain,(
    spl3_2 ),
    inference(avatar_contradiction_clause,[],[f50])).

fof(f50,plain,
    ( $false
    | spl3_2 ),
    inference(unit_resulting_resolution,[],[f23,f25,f45,f20])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f45,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1))
    | spl3_2 ),
    inference(superposition,[],[f37,f42])).

fof(f37,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl3_2
  <=> r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f25,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f23,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f15,f14])).

fof(f15,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f38,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f28,f35,f31])).

fof(f28,plain,
    ( ~ r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) ),
    inference(resolution,[],[f18,f22])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.19/0.34  % CPULimit   : 60
% 0.19/0.34  % WCLimit    : 600
% 0.19/0.34  % DateTime   : Tue Dec  1 18:42:36 EST 2020
% 0.19/0.35  % CPUTime    : 
% 0.20/0.50  % (15464)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (15468)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.50  % (15468)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f65,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f38,f55,f64])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    ~spl3_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f63])).
% 0.20/0.51  fof(f63,plain,(
% 0.20/0.51    $false | ~spl3_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f57,f47])).
% 0.20/0.51  fof(f47,plain,(
% 0.20/0.51    k2_tarski(sK0,sK1) != k2_tarski(sK0,sK0)),
% 0.20/0.51    inference(superposition,[],[f21,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    sK0 = sK2),
% 0.20/0.51    inference(resolution,[],[f24,f22])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK2))),
% 0.20/0.51    inference(definition_unfolding,[],[f12,f14])).
% 0.20/0.51  fof(f14,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f12,plain,(
% 0.20/0.51    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,plain,(
% 0.20/0.51    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.20/0.51    inference(negated_conjecture,[],[f6])).
% 0.20/0.51  fof(f6,conjecture,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X2)) | X0 = X2) )),
% 0.20/0.51    inference(definition_unfolding,[],[f19,f14])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) | X0 = X2) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.20/0.51    inference(ennf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    k2_tarski(sK0,sK1) != k2_tarski(sK2,sK2)),
% 0.20/0.51    inference(definition_unfolding,[],[f13,f14])).
% 0.20/0.51  fof(f13,plain,(
% 0.20/0.51    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    k2_tarski(sK0,sK1) = k2_tarski(sK0,sK0) | ~spl3_1),
% 0.20/0.51    inference(forward_demodulation,[],[f33,f42])).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2) | ~spl3_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f31])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    spl3_1 <=> k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    spl3_2),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    $false | spl3_2),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f23,f25,f45,f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.51    inference(flattening,[],[f10])).
% 0.20/0.51  fof(f10,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.51    inference(ennf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    ~r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)) | spl3_2),
% 0.20/0.51    inference(superposition,[],[f37,f42])).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ~r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)) | spl3_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    spl3_2 <=> r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.51  fof(f25,plain,(
% 0.20/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.51    inference(equality_resolution,[],[f17])).
% 0.20/0.51  fof(f17,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f15,f14])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    spl3_1 | ~spl3_2),
% 0.20/0.51    inference(avatar_split_clause,[],[f28,f35,f31])).
% 0.20/0.51  fof(f28,plain,(
% 0.20/0.51    ~r1_tarski(k2_tarski(sK2,sK2),k2_tarski(sK0,sK1)) | k2_tarski(sK0,sK1) = k2_tarski(sK2,sK2)),
% 0.20/0.51    inference(resolution,[],[f18,f22])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (15468)------------------------------
% 0.20/0.51  % (15468)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (15468)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (15468)Memory used [KB]: 6140
% 0.20/0.51  % (15468)Time elapsed: 0.091 s
% 0.20/0.51  % (15468)------------------------------
% 0.20/0.51  % (15468)------------------------------
% 0.20/0.51  % (15451)Success in time 0.148 s
%------------------------------------------------------------------------------
