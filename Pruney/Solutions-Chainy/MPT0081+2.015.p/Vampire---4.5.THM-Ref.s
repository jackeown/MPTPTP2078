%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:08 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   20 (  23 expanded)
%              Number of leaves         :    5 (   6 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  44 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f34,f15])).

fof(f15,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,X1)
      & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f34,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f32,f25])).

fof(f25,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f14,f19])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f14,plain,(
    ~ r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,k4_xboole_0(X0,X1))
      | ~ r1_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f22,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0 ),
    inference(resolution,[],[f20,f18])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:58:50 EST 2020
% 0.20/0.35  % CPUTime    : 
% 1.58/0.57  % (31046)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.58/0.57  % (31063)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.58/0.58  % (31055)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.58/0.58  % (31046)Refutation not found, incomplete strategy% (31046)------------------------------
% 1.58/0.58  % (31046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (31046)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (31046)Memory used [KB]: 10618
% 1.58/0.58  % (31046)Time elapsed: 0.140 s
% 1.58/0.58  % (31046)------------------------------
% 1.58/0.58  % (31046)------------------------------
% 1.58/0.58  % (31047)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.58/0.58  % (31038)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.58/0.58  % (31061)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.58/0.58  % (31038)Refutation not found, incomplete strategy% (31038)------------------------------
% 1.58/0.58  % (31038)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (31038)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (31038)Memory used [KB]: 1663
% 1.58/0.58  % (31038)Time elapsed: 0.148 s
% 1.58/0.58  % (31038)------------------------------
% 1.58/0.58  % (31038)------------------------------
% 1.58/0.58  % (31044)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.58/0.58  % (31044)Refutation found. Thanks to Tanya!
% 1.58/0.58  % SZS status Theorem for theBenchmark
% 1.73/0.59  % (31040)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.73/0.59  % SZS output start Proof for theBenchmark
% 1.73/0.59  fof(f37,plain,(
% 1.73/0.59    $false),
% 1.73/0.59    inference(subsumption_resolution,[],[f34,f15])).
% 1.73/0.59  fof(f15,plain,(
% 1.73/0.59    r1_xboole_0(sK0,sK1)),
% 1.73/0.59    inference(cnf_transformation,[],[f9])).
% 1.73/0.59  fof(f9,plain,(
% 1.73/0.59    ? [X0,X1,X2] : (r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.73/0.59    inference(ennf_transformation,[],[f8])).
% 1.73/0.59  fof(f8,negated_conjecture,(
% 1.73/0.59    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.73/0.59    inference(negated_conjecture,[],[f7])).
% 1.73/0.59  fof(f7,conjecture,(
% 1.73/0.59    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.73/0.59  fof(f34,plain,(
% 1.73/0.59    ~r1_xboole_0(sK0,sK1)),
% 1.73/0.59    inference(resolution,[],[f32,f25])).
% 1.73/0.59  fof(f25,plain,(
% 1.73/0.59    ~r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 1.73/0.59    inference(definition_unfolding,[],[f14,f19])).
% 1.73/0.59  fof(f19,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f4])).
% 1.73/0.59  fof(f4,axiom,(
% 1.73/0.59    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.73/0.59  fof(f14,plain,(
% 1.73/0.59    ~r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 1.73/0.59    inference(cnf_transformation,[],[f9])).
% 1.73/0.59  fof(f32,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (r1_xboole_0(X2,k4_xboole_0(X0,X1)) | ~r1_xboole_0(X2,X0)) )),
% 1.73/0.59    inference(superposition,[],[f22,f31])).
% 1.73/0.59  fof(f31,plain,(
% 1.73/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),X0) = X0) )),
% 1.73/0.59    inference(resolution,[],[f20,f18])).
% 1.73/0.59  fof(f18,plain,(
% 1.73/0.59    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f3])).
% 1.73/0.59  fof(f3,axiom,(
% 1.73/0.59    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 1.73/0.59  fof(f20,plain,(
% 1.73/0.59    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.73/0.59    inference(cnf_transformation,[],[f11])).
% 1.73/0.59  fof(f11,plain,(
% 1.73/0.59    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.73/0.59    inference(ennf_transformation,[],[f2])).
% 1.73/0.59  fof(f2,axiom,(
% 1.73/0.59    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.73/0.59  fof(f22,plain,(
% 1.73/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 1.73/0.59    inference(cnf_transformation,[],[f13])).
% 1.73/0.59  fof(f13,plain,(
% 1.73/0.59    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.73/0.59    inference(ennf_transformation,[],[f6])).
% 1.73/0.59  fof(f6,axiom,(
% 1.73/0.59    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.73/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.73/0.59  % SZS output end Proof for theBenchmark
% 1.73/0.59  % (31044)------------------------------
% 1.73/0.59  % (31044)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.73/0.59  % (31044)Termination reason: Refutation
% 1.73/0.59  
% 1.73/0.59  % (31044)Memory used [KB]: 6140
% 1.73/0.59  % (31044)Time elapsed: 0.153 s
% 1.73/0.59  % (31044)------------------------------
% 1.73/0.59  % (31044)------------------------------
% 1.73/0.59  % (31037)Success in time 0.222 s
%------------------------------------------------------------------------------
