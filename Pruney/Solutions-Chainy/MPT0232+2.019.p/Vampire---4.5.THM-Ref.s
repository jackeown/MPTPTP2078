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
% DateTime   : Thu Dec  3 12:37:02 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   25 (  32 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  63 expanded)
%              Number of equality atoms :   13 (  17 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f27,f33])).

fof(f33,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f32])).

fof(f32,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f31,f17])).

fof(f17,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f31,plain,
    ( ~ r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1))
    | ~ spl3_1
    | spl3_2 ),
    inference(forward_demodulation,[],[f30,f28])).

fof(f28,plain,
    ( sK0 = sK2
    | ~ spl3_1 ),
    inference(resolution,[],[f22,f12])).

fof(f12,plain,(
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

fof(f22,plain,
    ( r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f21])).

fof(f21,plain,
    ( spl3_1
  <=> r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f30,plain,
    ( ~ r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f29,f26])).

fof(f26,plain,
    ( k2_tarski(sK0,sK1) != k1_tarski(sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl3_2
  <=> k2_tarski(sK0,sK1) = k1_tarski(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f29,plain,
    ( ~ r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1))
    | k2_tarski(sK0,sK1) = k1_tarski(sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f22,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f27,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f11,f25])).

fof(f11,plain,(
    k2_tarski(sK0,sK1) != k1_tarski(sK2) ),
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

fof(f23,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f10,f21])).

fof(f10,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:25 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.45  % (12270)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.19/0.47  % (12288)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.19/0.47  % (12288)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.47  % SZS output start Proof for theBenchmark
% 0.19/0.47  fof(f34,plain,(
% 0.19/0.47    $false),
% 0.19/0.47    inference(avatar_sat_refutation,[],[f23,f27,f33])).
% 0.19/0.47  fof(f33,plain,(
% 0.19/0.47    ~spl3_1 | spl3_2),
% 0.19/0.47    inference(avatar_contradiction_clause,[],[f32])).
% 0.19/0.47  fof(f32,plain,(
% 0.19/0.47    $false | (~spl3_1 | spl3_2)),
% 0.19/0.47    inference(subsumption_resolution,[],[f31,f17])).
% 0.19/0.47  fof(f17,plain,(
% 0.19/0.47    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.19/0.47    inference(cnf_transformation,[],[f4])).
% 0.19/0.47  fof(f4,axiom,(
% 0.19/0.47    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 0.19/0.47  fof(f31,plain,(
% 0.19/0.47    ~r1_tarski(k1_tarski(sK0),k2_tarski(sK0,sK1)) | (~spl3_1 | spl3_2)),
% 0.19/0.47    inference(forward_demodulation,[],[f30,f28])).
% 0.19/0.47  fof(f28,plain,(
% 0.19/0.47    sK0 = sK2 | ~spl3_1),
% 0.19/0.47    inference(resolution,[],[f22,f12])).
% 0.19/0.47  fof(f12,plain,(
% 0.19/0.47    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) | X0 = X2) )),
% 0.19/0.47    inference(cnf_transformation,[],[f9])).
% 0.19/0.47  fof(f9,plain,(
% 0.19/0.47    ! [X0,X1,X2] : (X0 = X2 | ~r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f5])).
% 0.19/0.47  fof(f5,axiom,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => X0 = X2)),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).
% 0.19/0.47  fof(f22,plain,(
% 0.19/0.47    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2)) | ~spl3_1),
% 0.19/0.47    inference(avatar_component_clause,[],[f21])).
% 0.19/0.47  fof(f21,plain,(
% 0.19/0.47    spl3_1 <=> r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.19/0.47  fof(f30,plain,(
% 0.19/0.47    ~r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1)) | (~spl3_1 | spl3_2)),
% 0.19/0.47    inference(subsumption_resolution,[],[f29,f26])).
% 0.19/0.47  fof(f26,plain,(
% 0.19/0.47    k2_tarski(sK0,sK1) != k1_tarski(sK2) | spl3_2),
% 0.19/0.47    inference(avatar_component_clause,[],[f25])).
% 0.19/0.47  fof(f25,plain,(
% 0.19/0.47    spl3_2 <=> k2_tarski(sK0,sK1) = k1_tarski(sK2)),
% 0.19/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.19/0.47  fof(f29,plain,(
% 0.19/0.47    ~r1_tarski(k1_tarski(sK2),k2_tarski(sK0,sK1)) | k2_tarski(sK0,sK1) = k1_tarski(sK2) | ~spl3_1),
% 0.19/0.47    inference(resolution,[],[f22,f15])).
% 0.19/0.47  fof(f15,plain,(
% 0.19/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.19/0.47    inference(cnf_transformation,[],[f1])).
% 0.19/0.47  fof(f1,axiom,(
% 0.19/0.47    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.19/0.47  fof(f27,plain,(
% 0.19/0.47    ~spl3_2),
% 0.19/0.47    inference(avatar_split_clause,[],[f11,f25])).
% 0.19/0.47  fof(f11,plain,(
% 0.19/0.47    k2_tarski(sK0,sK1) != k1_tarski(sK2)),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  fof(f8,plain,(
% 0.19/0.47    ? [X0,X1,X2] : (k2_tarski(X0,X1) != k1_tarski(X2) & r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)))),
% 0.19/0.47    inference(ennf_transformation,[],[f7])).
% 0.19/0.47  fof(f7,negated_conjecture,(
% 0.19/0.47    ~! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.19/0.47    inference(negated_conjecture,[],[f6])).
% 0.19/0.47  fof(f6,conjecture,(
% 0.19/0.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),k1_tarski(X2)) => k2_tarski(X0,X1) = k1_tarski(X2))),
% 0.19/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).
% 0.19/0.47  fof(f23,plain,(
% 0.19/0.47    spl3_1),
% 0.19/0.47    inference(avatar_split_clause,[],[f10,f21])).
% 0.19/0.47  fof(f10,plain,(
% 0.19/0.47    r1_tarski(k2_tarski(sK0,sK1),k1_tarski(sK2))),
% 0.19/0.47    inference(cnf_transformation,[],[f8])).
% 0.19/0.47  % SZS output end Proof for theBenchmark
% 0.19/0.47  % (12288)------------------------------
% 0.19/0.47  % (12288)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (12288)Termination reason: Refutation
% 0.19/0.47  
% 0.19/0.47  % (12288)Memory used [KB]: 6140
% 0.19/0.47  % (12288)Time elapsed: 0.067 s
% 0.19/0.47  % (12288)------------------------------
% 0.19/0.47  % (12288)------------------------------
% 0.19/0.47  % (12261)Success in time 0.121 s
%------------------------------------------------------------------------------
