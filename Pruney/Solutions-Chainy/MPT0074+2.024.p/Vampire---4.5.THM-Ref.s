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
% DateTime   : Thu Dec  3 12:30:38 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   20 (  32 expanded)
%              Number of leaves         :    3 (   6 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 ( 102 expanded)
%              Number of equality atoms :   11 (  23 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(subsumption_resolution,[],[f25,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f5])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X0
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

% (31475)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X2)
          & r1_tarski(X0,X1) )
       => k1_xboole_0 = X0 ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f25,plain,(
    k1_xboole_0 = sK0 ),
    inference(resolution,[],[f24,f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X0,X0) ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X0] :
      ( ( ~ r1_xboole_0(X0,X0)
        | k1_xboole_0 = X0 )
      & ( k1_xboole_0 != X0
        | r1_xboole_0(X0,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ~ ( r1_xboole_0(X0,X0)
          & k1_xboole_0 != X0 )
      & ~ ( k1_xboole_0 = X0
          & ~ r1_xboole_0(X0,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

fof(f24,plain,(
    r1_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f23,f11])).

fof(f11,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f6])).

fof(f23,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2)
      | r1_xboole_0(sK0,X0) ) ),
    inference(resolution,[],[f22,f10])).

fof(f10,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,sK1)
      | ~ r1_tarski(X1,sK2)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f12,f16])).

fof(f16,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X3)
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X1,X3)
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

fof(f12,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 12:29:26 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.19/0.45  % (31473)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.45  % (31473)Refutation not found, incomplete strategy% (31473)------------------------------
% 0.19/0.45  % (31473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.45  % (31473)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.45  
% 0.19/0.45  % (31473)Memory used [KB]: 10490
% 0.19/0.45  % (31473)Time elapsed: 0.028 s
% 0.19/0.45  % (31473)------------------------------
% 0.19/0.45  % (31473)------------------------------
% 0.19/0.48  % (31485)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.48  % (31485)Refutation found. Thanks to Tanya!
% 0.19/0.48  % SZS status Theorem for theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f27,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(subsumption_resolution,[],[f25,f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    k1_xboole_0 != sK0),
% 0.19/0.48    inference(cnf_transformation,[],[f6])).
% 0.19/0.48  fof(f6,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (k1_xboole_0 != X0 & r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1))),
% 0.19/0.48    inference(flattening,[],[f5])).
% 0.19/0.48  fof(f5,plain,(
% 0.19/0.48    ? [X0,X1,X2] : (k1_xboole_0 != X0 & (r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  % (31475)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.48  fof(f4,negated_conjecture,(
% 0.19/0.48    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.19/0.48    inference(negated_conjecture,[],[f3])).
% 0.19/0.48  fof(f3,conjecture,(
% 0.19/0.48    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    k1_xboole_0 = sK0),
% 0.19/0.48    inference(resolution,[],[f24,f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_xboole_0(X0,X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,plain,(
% 0.19/0.48    ! [X0] : ((~r1_xboole_0(X0,X0) | k1_xboole_0 = X0) & (k1_xboole_0 != X0 | r1_xboole_0(X0,X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f2])).
% 0.19/0.48  fof(f2,axiom,(
% 0.19/0.48    ! [X0] : (~(r1_xboole_0(X0,X0) & k1_xboole_0 != X0) & ~(k1_xboole_0 = X0 & ~r1_xboole_0(X0,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    r1_xboole_0(sK0,sK0)),
% 0.19/0.48    inference(resolution,[],[f23,f11])).
% 0.19/0.48  fof(f11,plain,(
% 0.19/0.48    r1_tarski(sK0,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f6])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(sK0,X0)) )),
% 0.19/0.48    inference(resolution,[],[f22,f10])).
% 0.19/0.48  fof(f10,plain,(
% 0.19/0.48    r1_tarski(sK0,sK1)),
% 0.19/0.48    inference(cnf_transformation,[],[f6])).
% 0.19/0.48  fof(f22,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_tarski(X0,sK1) | ~r1_tarski(X1,sK2) | r1_xboole_0(X0,X1)) )),
% 0.19/0.48    inference(resolution,[],[f12,f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ( ! [X2,X0,X3,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X3) | ~r1_xboole_0(X1,X3) | r1_xboole_0(X0,X2)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f9])).
% 0.19/0.48  fof(f9,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 0.19/0.48    inference(flattening,[],[f8])).
% 0.19/0.48  fof(f8,plain,(
% 0.19/0.48    ! [X0,X1,X2,X3] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X3) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1,X2,X3] : ((r1_xboole_0(X1,X3) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).
% 0.19/0.48  fof(f12,plain,(
% 0.19/0.48    r1_xboole_0(sK1,sK2)),
% 0.19/0.48    inference(cnf_transformation,[],[f6])).
% 0.19/0.48  % SZS output end Proof for theBenchmark
% 0.19/0.48  % (31485)------------------------------
% 0.19/0.48  % (31485)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (31485)Termination reason: Refutation
% 0.19/0.48  
% 0.19/0.48  % (31485)Memory used [KB]: 1535
% 0.19/0.48  % (31485)Time elapsed: 0.084 s
% 0.19/0.48  % (31485)------------------------------
% 0.19/0.48  % (31485)------------------------------
% 0.19/0.48  % (31471)Success in time 0.136 s
%------------------------------------------------------------------------------
