%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  54 expanded)
%              Number of leaves         :    8 (  18 expanded)
%              Depth                    :    8
%              Number of atoms          :   89 ( 118 expanded)
%              Number of equality atoms :   15 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f84,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f57,f61,f79,f83])).

fof(f83,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f81])).

fof(f81,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f29,f71])).

fof(f71,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl2_1 ),
    inference(superposition,[],[f22,f26])).

fof(f26,plain,
    ( sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f22,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f29,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_2
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f79,plain,
    ( ~ spl2_1
    | spl2_2 ),
    inference(avatar_contradiction_clause,[],[f77])).

fof(f77,plain,
    ( $false
    | ~ spl2_1
    | spl2_2 ),
    inference(subsumption_resolution,[],[f30,f76])).

fof(f76,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl2_1 ),
    inference(trivial_inequality_removal,[],[f75])).

fof(f75,plain,
    ( sK0 != sK0
    | r2_hidden(sK1,sK0)
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f11,f26])).

fof(f11,plain,
    ( r2_hidden(sK1,sK0)
    | sK0 != k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <~> ~ r2_hidden(X1,X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k4_xboole_0(X0,k1_tarski(X1)) = X0
      <=> ~ r2_hidden(X1,X0) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f30,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f61,plain,(
    spl2_3 ),
    inference(avatar_contradiction_clause,[],[f58])).

fof(f58,plain,
    ( $false
    | spl2_3 ),
    inference(resolution,[],[f56,f21])).

fof(f21,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,
    ( ~ r1_tarski(sK0,sK0)
    | spl2_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_3
  <=> r1_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f57,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_2 ),
    inference(avatar_split_clause,[],[f52,f28,f54,f24])).

fof(f52,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))
    | spl2_2 ),
    inference(resolution,[],[f38,f12])).

fof(f12,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f38,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k4_xboole_0(X2,k1_tarski(sK1)),sK0)
        | ~ r1_tarski(sK0,X2)
        | sK0 = k4_xboole_0(X2,k1_tarski(sK1)) )
    | spl2_2 ),
    inference(resolution,[],[f33,f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f33,plain,
    ( ! [X1] :
        ( r1_tarski(sK0,k4_xboole_0(X1,k1_tarski(sK1)))
        | ~ r1_tarski(sK0,X1) )
    | spl2_2 ),
    inference(resolution,[],[f30,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r2_hidden(X2,X0)
      | r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
      | r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_zfmisc_1)).

fof(f31,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f10,f28,f24])).

fof(f10,plain,
    ( ~ r2_hidden(sK1,sK0)
    | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:59:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.48  % (11366)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.48  % (11366)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f31,f57,f61,f79,f83])).
% 0.20/0.48  fof(f83,plain,(
% 0.20/0.48    ~spl2_1 | ~spl2_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f81])).
% 0.20/0.48  fof(f81,plain,(
% 0.20/0.48    $false | (~spl2_1 | ~spl2_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f29,f71])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ~r2_hidden(sK1,sK0) | ~spl2_1),
% 0.20/0.48    inference(superposition,[],[f22,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | ~spl2_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    spl2_1 <=> sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.48    inference(equality_resolution,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    r2_hidden(sK1,sK0) | ~spl2_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    spl2_2 <=> r2_hidden(sK1,sK0)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.48  fof(f79,plain,(
% 0.20/0.48    ~spl2_1 | spl2_2),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f77])).
% 0.20/0.48  fof(f77,plain,(
% 0.20/0.48    $false | (~spl2_1 | spl2_2)),
% 0.20/0.48    inference(subsumption_resolution,[],[f30,f76])).
% 0.20/0.48  fof(f76,plain,(
% 0.20/0.48    r2_hidden(sK1,sK0) | ~spl2_1),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    sK0 != sK0 | r2_hidden(sK1,sK0) | ~spl2_1),
% 0.20/0.48    inference(forward_demodulation,[],[f11,f26])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    r2_hidden(sK1,sK0) | sK0 != k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,plain,(
% 0.20/0.48    ? [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <~> ~r2_hidden(X1,X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.48    inference(negated_conjecture,[],[f5])).
% 0.20/0.48  fof(f5,conjecture,(
% 0.20/0.48    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.20/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ~r2_hidden(sK1,sK0) | spl2_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f28])).
% 0.20/0.48  fof(f61,plain,(
% 0.20/0.48    spl2_3),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f58])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    $false | spl2_3),
% 0.20/0.48    inference(resolution,[],[f56,f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK0) | spl2_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl2_3 <=> r1_tarski(sK0,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    spl2_1 | ~spl2_3 | spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f52,f28,f54,f24])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ~r1_tarski(sK0,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1)) | spl2_2),
% 0.20/0.49    inference(resolution,[],[f38,f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X2] : (~r1_tarski(k4_xboole_0(X2,k1_tarski(sK1)),sK0) | ~r1_tarski(sK0,X2) | sK0 = k4_xboole_0(X2,k1_tarski(sK1))) ) | spl2_2),
% 0.20/0.49    inference(resolution,[],[f33,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X1] : (r1_tarski(sK0,k4_xboole_0(X1,k1_tarski(sK1))) | ~r1_tarski(sK0,X1)) ) | spl2_2),
% 0.20/0.49    inference(resolution,[],[f30,f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r2_hidden(X2,X0) | r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(flattening,[],[f8])).
% 0.20/0.49  fof(f8,plain,(
% 0.20/0.49    ! [X0,X1,X2] : ((r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(X0,k4_xboole_0(X1,k1_tarski(X2))) | r2_hidden(X2,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l2_zfmisc_1)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    spl2_1 | ~spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f10,f28,f24])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK0) | sK0 = k4_xboole_0(sK0,k1_tarski(sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (11366)------------------------------
% 0.20/0.49  % (11366)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (11366)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (11366)Memory used [KB]: 10618
% 0.20/0.49  % (11366)Time elapsed: 0.042 s
% 0.20/0.49  % (11366)------------------------------
% 0.20/0.49  % (11366)------------------------------
% 0.20/0.49  % (11340)Success in time 0.131 s
%------------------------------------------------------------------------------
