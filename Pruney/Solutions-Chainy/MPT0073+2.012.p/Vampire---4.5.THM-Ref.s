%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:34 EST 2020

% Result     : Theorem 1.34s
% Output     : Refutation 1.34s
% Verified   : 
% Statistics : Number of formulae       :   29 (  34 expanded)
%              Number of leaves         :    6 (   8 expanded)
%              Depth                    :   11
%              Number of atoms          :   59 (  73 expanded)
%              Number of equality atoms :   24 (  32 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f33,plain,(
    $false ),
    inference(subsumption_resolution,[],[f32,f15])).

fof(f15,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f32,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f31])).

fof(f31,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f24,f29])).

fof(f29,plain,(
    k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f28])).

fof(f28,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f27,f16])).

fof(f16,plain,(
    ! [X0] :
      ( r2_hidden(sK1(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f27,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,sK0)
      | k1_xboole_0 = sK0 ) ),
    inference(forward_demodulation,[],[f26,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f17,f18])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f17,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f26,plain,(
    ! [X2] :
      ( ~ r2_hidden(X2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)))
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f23,f13])).

% (32014)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
fof(f13,plain,
    ( r1_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f24,plain,
    ( k1_xboole_0 != sK0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(inner_rewriting,[],[f14])).

fof(f14,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 21:00:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (32001)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.51  % (32003)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.52  % (32002)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.53  % (32005)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.34/0.53  % (32005)Refutation found. Thanks to Tanya!
% 1.34/0.53  % SZS status Theorem for theBenchmark
% 1.34/0.53  % (32007)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.34/0.53  % (32021)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.34/0.53  % SZS output start Proof for theBenchmark
% 1.34/0.53  fof(f33,plain,(
% 1.34/0.53    $false),
% 1.34/0.53    inference(subsumption_resolution,[],[f32,f15])).
% 1.34/0.53  fof(f15,plain,(
% 1.34/0.53    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f5])).
% 1.34/0.53  fof(f5,axiom,(
% 1.34/0.53    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.34/0.53  fof(f32,plain,(
% 1.34/0.53    ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.34/0.53    inference(trivial_inequality_removal,[],[f31])).
% 1.34/0.53  fof(f31,plain,(
% 1.34/0.53    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.34/0.53    inference(backward_demodulation,[],[f24,f29])).
% 1.34/0.53  fof(f29,plain,(
% 1.34/0.53    k1_xboole_0 = sK0),
% 1.34/0.53    inference(duplicate_literal_removal,[],[f28])).
% 1.34/0.53  fof(f28,plain,(
% 1.34/0.53    k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.34/0.53    inference(resolution,[],[f27,f16])).
% 1.34/0.53  fof(f16,plain,(
% 1.34/0.53    ( ! [X0] : (r2_hidden(sK1(X0),X0) | k1_xboole_0 = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f11])).
% 1.34/0.53  fof(f11,plain,(
% 1.34/0.53    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.34/0.53    inference(ennf_transformation,[],[f3])).
% 1.34/0.53  fof(f3,axiom,(
% 1.34/0.53    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.34/0.53  fof(f27,plain,(
% 1.34/0.53    ( ! [X2] : (~r2_hidden(X2,sK0) | k1_xboole_0 = sK0) )),
% 1.34/0.53    inference(forward_demodulation,[],[f26,f21])).
% 1.34/0.53  fof(f21,plain,(
% 1.34/0.53    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 1.34/0.53    inference(definition_unfolding,[],[f17,f18])).
% 1.34/0.53  fof(f18,plain,(
% 1.34/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.34/0.53    inference(cnf_transformation,[],[f4])).
% 1.34/0.53  fof(f4,axiom,(
% 1.34/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.34/0.53  fof(f17,plain,(
% 1.34/0.53    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.34/0.53    inference(cnf_transformation,[],[f8])).
% 1.34/0.53  fof(f8,plain,(
% 1.34/0.53    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.34/0.53    inference(rectify,[],[f1])).
% 1.34/0.53  fof(f1,axiom,(
% 1.34/0.53    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.34/0.53  fof(f26,plain,(
% 1.34/0.53    ( ! [X2] : (~r2_hidden(X2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))) | k1_xboole_0 = sK0) )),
% 1.34/0.53    inference(resolution,[],[f23,f13])).
% 1.34/0.53  % (32014)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.34/0.53  fof(f13,plain,(
% 1.34/0.53    r1_xboole_0(sK0,sK0) | k1_xboole_0 = sK0),
% 1.34/0.53    inference(cnf_transformation,[],[f10])).
% 1.34/0.53  fof(f10,plain,(
% 1.34/0.53    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.34/0.53    inference(ennf_transformation,[],[f7])).
% 1.34/0.53  fof(f7,negated_conjecture,(
% 1.34/0.53    ~! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.34/0.53    inference(negated_conjecture,[],[f6])).
% 1.34/0.53  fof(f6,conjecture,(
% 1.34/0.53    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 1.34/0.53  fof(f23,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.34/0.53    inference(definition_unfolding,[],[f19,f18])).
% 1.34/0.53  fof(f19,plain,(
% 1.34/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 1.34/0.53    inference(cnf_transformation,[],[f12])).
% 1.34/0.53  fof(f12,plain,(
% 1.34/0.53    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.34/0.53    inference(ennf_transformation,[],[f9])).
% 1.34/0.53  fof(f9,plain,(
% 1.34/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.34/0.53    inference(rectify,[],[f2])).
% 1.34/0.53  fof(f2,axiom,(
% 1.34/0.53    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.34/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.34/0.53  fof(f24,plain,(
% 1.34/0.53    k1_xboole_0 != sK0 | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 1.34/0.53    inference(inner_rewriting,[],[f14])).
% 1.34/0.53  fof(f14,plain,(
% 1.34/0.53    ~r1_xboole_0(sK0,sK0) | k1_xboole_0 != sK0),
% 1.34/0.53    inference(cnf_transformation,[],[f10])).
% 1.34/0.53  % SZS output end Proof for theBenchmark
% 1.34/0.53  % (32005)------------------------------
% 1.34/0.53  % (32005)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (32005)Termination reason: Refutation
% 1.34/0.53  
% 1.34/0.53  % (32005)Memory used [KB]: 6140
% 1.34/0.53  % (32005)Time elapsed: 0.117 s
% 1.34/0.53  % (32005)------------------------------
% 1.34/0.53  % (32005)------------------------------
% 1.34/0.53  % (32016)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.34/0.53  % (32000)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.34/0.53  % (31999)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.34/0.53  % (31999)Refutation not found, incomplete strategy% (31999)------------------------------
% 1.34/0.53  % (31999)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (32025)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.34/0.53  % (31999)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (31999)Memory used [KB]: 1663
% 1.34/0.53  % (31999)Time elapsed: 0.120 s
% 1.34/0.53  % (31999)------------------------------
% 1.34/0.53  % (31999)------------------------------
% 1.34/0.53  % (32016)Refutation not found, incomplete strategy% (32016)------------------------------
% 1.34/0.53  % (32016)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.53  % (32016)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.53  
% 1.34/0.53  % (32016)Memory used [KB]: 10618
% 1.34/0.53  % (32016)Time elapsed: 0.131 s
% 1.34/0.53  % (32016)------------------------------
% 1.34/0.53  % (32016)------------------------------
% 1.34/0.54  % (31998)Success in time 0.174 s
%------------------------------------------------------------------------------
