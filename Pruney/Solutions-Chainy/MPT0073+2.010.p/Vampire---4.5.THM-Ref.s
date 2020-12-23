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
% DateTime   : Thu Dec  3 12:30:34 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   28 (  48 expanded)
%              Number of leaves         :    5 (  14 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  80 expanded)
%              Number of equality atoms :   31 (  54 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,plain,(
    $false ),
    inference(resolution,[],[f31,f28])).

fof(f28,plain,(
    ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f27])).

fof(f27,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f18,f25])).

fof(f25,plain,(
    k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f22])).

fof(f22,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f21,f11])).

fof(f11,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f21,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(forward_demodulation,[],[f20,f19])).

fof(f19,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f15,f11])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f10,f12])).

fof(f12,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f10,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f20,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0))
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f16,f8])).

fof(f8,plain,
    ( r1_xboole_0(sK0,sK0)
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ( r1_xboole_0(X0,X0)
        & k1_xboole_0 != X0 )
      | ( k1_xboole_0 = X0
        & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( ~ ( r1_xboole_0(X0,X0)
            & k1_xboole_0 != X0 )
        & ~ ( k1_xboole_0 = X0
            & ~ r1_xboole_0(X0,X0) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f14,f12])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f18,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != sK0 ),
    inference(inner_rewriting,[],[f9])).

fof(f9,plain,
    ( ~ r1_xboole_0(sK0,sK0)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f7])).

fof(f31,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f29,f19])).

fof(f29,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(X0,X0)
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f17,f11])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f13,f12])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n017.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:16:31 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (7377)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.50  % (7377)Refutation not found, incomplete strategy% (7377)------------------------------
% 0.22/0.50  % (7377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (7377)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (7377)Memory used [KB]: 10618
% 0.22/0.50  % (7377)Time elapsed: 0.081 s
% 0.22/0.50  % (7377)------------------------------
% 0.22/0.50  % (7377)------------------------------
% 0.22/0.52  % (7369)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.52  % (7397)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (7368)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.53  % (7368)Refutation not found, incomplete strategy% (7368)------------------------------
% 0.22/0.53  % (7368)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7368)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7368)Memory used [KB]: 1663
% 0.22/0.53  % (7368)Time elapsed: 0.114 s
% 0.22/0.53  % (7368)------------------------------
% 0.22/0.53  % (7368)------------------------------
% 0.22/0.53  % (7382)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (7388)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.53  % (7389)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (7389)Refutation not found, incomplete strategy% (7389)------------------------------
% 0.22/0.53  % (7389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7372)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (7372)Refutation not found, incomplete strategy% (7372)------------------------------
% 0.22/0.53  % (7372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (7372)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (7372)Memory used [KB]: 6140
% 0.22/0.53  % (7372)Time elapsed: 0.116 s
% 0.22/0.53  % (7372)------------------------------
% 0.22/0.53  % (7372)------------------------------
% 0.22/0.53  % (7374)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.54  % (7370)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (7374)Refutation found. Thanks to Tanya!
% 0.22/0.54  % SZS status Theorem for theBenchmark
% 0.22/0.54  % SZS output start Proof for theBenchmark
% 0.22/0.54  fof(f34,plain,(
% 0.22/0.54    $false),
% 0.22/0.54    inference(resolution,[],[f31,f28])).
% 0.22/0.54  fof(f28,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    inference(trivial_inequality_removal,[],[f27])).
% 0.22/0.54  fof(f27,plain,(
% 0.22/0.54    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.54    inference(backward_demodulation,[],[f18,f25])).
% 0.22/0.54  fof(f25,plain,(
% 0.22/0.54    k1_xboole_0 = sK0),
% 0.22/0.54    inference(duplicate_literal_removal,[],[f22])).
% 0.22/0.54  fof(f22,plain,(
% 0.22/0.54    k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 0.22/0.54    inference(superposition,[],[f21,f11])).
% 0.22/0.54  fof(f11,plain,(
% 0.22/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.54    inference(cnf_transformation,[],[f3])).
% 0.22/0.54  fof(f3,axiom,(
% 0.22/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.22/0.54  fof(f21,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(forward_demodulation,[],[f20,f19])).
% 0.22/0.54  fof(f19,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.54    inference(backward_demodulation,[],[f15,f11])).
% 0.22/0.54  fof(f15,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f10,f12])).
% 0.22/0.54  fof(f12,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(cnf_transformation,[],[f4])).
% 0.22/0.54  fof(f4,axiom,(
% 0.22/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.54  fof(f10,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f2])).
% 0.22/0.54  fof(f2,axiom,(
% 0.22/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.54  fof(f20,plain,(
% 0.22/0.54    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(resolution,[],[f16,f8])).
% 0.22/0.54  fof(f8,plain,(
% 0.22/0.54    r1_xboole_0(sK0,sK0) | k1_xboole_0 = sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f7,plain,(
% 0.22/0.54    ? [X0] : ((r1_xboole_0(X0,X0) & k1_xboole_0 != X0) | (k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.54    inference(ennf_transformation,[],[f6])).
% 0.22/0.54  fof(f6,negated_conjecture,(
% 0.22/0.54    ~! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.54    inference(negated_conjecture,[],[f5])).
% 0.22/0.54  fof(f5,conjecture,(
% 0.22/0.54    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.22/0.54  fof(f16,plain,(
% 0.22/0.54    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.54    inference(definition_unfolding,[],[f14,f12])).
% 0.22/0.54  fof(f14,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  fof(f1,axiom,(
% 0.22/0.54    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.22/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.22/0.54  fof(f18,plain,(
% 0.22/0.54    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | k1_xboole_0 != sK0),
% 0.22/0.54    inference(inner_rewriting,[],[f9])).
% 0.22/0.54  fof(f9,plain,(
% 0.22/0.54    ~r1_xboole_0(sK0,sK0) | k1_xboole_0 != sK0),
% 0.22/0.54    inference(cnf_transformation,[],[f7])).
% 0.22/0.54  fof(f31,plain,(
% 0.22/0.54    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(subsumption_resolution,[],[f29,f19])).
% 0.22/0.54  fof(f29,plain,(
% 0.22/0.54    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,X0) | r1_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.54    inference(superposition,[],[f17,f11])).
% 0.22/0.54  fof(f17,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(definition_unfolding,[],[f13,f12])).
% 0.22/0.54  fof(f13,plain,(
% 0.22/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 0.22/0.54    inference(cnf_transformation,[],[f1])).
% 0.22/0.54  % SZS output end Proof for theBenchmark
% 0.22/0.54  % (7374)------------------------------
% 0.22/0.54  % (7374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7374)Termination reason: Refutation
% 0.22/0.54  
% 0.22/0.54  % (7374)Memory used [KB]: 6140
% 0.22/0.54  % (7374)Time elapsed: 0.128 s
% 0.22/0.54  % (7374)------------------------------
% 0.22/0.54  % (7374)------------------------------
% 0.22/0.54  % (7370)Refutation not found, incomplete strategy% (7370)------------------------------
% 0.22/0.54  % (7370)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (7370)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (7370)Memory used [KB]: 10618
% 0.22/0.54  % (7370)Time elapsed: 0.126 s
% 0.22/0.54  % (7370)------------------------------
% 0.22/0.54  % (7370)------------------------------
% 0.22/0.54  % (7365)Success in time 0.173 s
%------------------------------------------------------------------------------
