%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:15 EST 2020

% Result     : Theorem 1.48s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   44 ( 153 expanded)
%              Number of leaves         :   10 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 200 expanded)
%              Number of equality atoms :   54 ( 176 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f157,plain,(
    $false ),
    inference(resolution,[],[f94,f75])).

fof(f75,plain,(
    r2_hidden(sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))) ),
    inference(unit_resulting_resolution,[],[f72,f71,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f33,f49])).

fof(f49,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | r2_hidden(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( X1 != X2
          & r2_hidden(X2,X0) )
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ~ ( ! [X2] :
            ~ ( X1 != X2
              & r2_hidden(X2,X0) )
        & k1_xboole_0 != X0
        & k1_tarski(X1) != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).

fof(f71,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) ),
    inference(forward_demodulation,[],[f51,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

% (10743)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f51,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f24,f49,f47,f49])).

fof(f47,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f24,plain,(
    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)
      & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

fof(f72,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))) ),
    inference(forward_demodulation,[],[f52,f42])).

fof(f52,plain,(
    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))) ),
    inference(definition_unfolding,[],[f23,f47,f49])).

fof(f23,plain,(
    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f94,plain,(
    ! [X0] : ~ r2_hidden(sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X0,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0))))) ),
    inference(forward_demodulation,[],[f89,f42])).

fof(f89,plain,(
    ! [X0] : ~ r2_hidden(sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)))) ),
    inference(unit_resulting_resolution,[],[f79,f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2 ) ),
    inference(definition_unfolding,[],[f28,f47])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f79,plain,(
    ~ r2_hidden(sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0),k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f76,f68])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f76,plain,(
    sK0 != sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0) ),
    inference(unit_resulting_resolution,[],[f72,f71,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( sK3(X0,X1) != X1
      | k1_xboole_0 = X0
      | k2_enumset1(X1,X1,X1,X1) = X0 ) ),
    inference(definition_unfolding,[],[f34,f49])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | sK3(X0,X1) != X1 ) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n020.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:15:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 1.29/0.55  % (10748)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.29/0.56  % (10740)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.29/0.56  % (10742)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.48/0.56  % (10741)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.57  % (10758)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.48/0.57  % (10748)Refutation not found, incomplete strategy% (10748)------------------------------
% 1.48/0.57  % (10748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.57  % (10756)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.48/0.57  % (10748)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.57  
% 1.48/0.57  % (10748)Memory used [KB]: 1663
% 1.48/0.57  % (10748)Time elapsed: 0.131 s
% 1.48/0.57  % (10748)------------------------------
% 1.48/0.57  % (10748)------------------------------
% 1.48/0.57  % (10750)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.58  % (10757)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.48/0.58  % (10758)Refutation not found, incomplete strategy% (10758)------------------------------
% 1.48/0.58  % (10758)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (10750)Refutation not found, incomplete strategy% (10750)------------------------------
% 1.48/0.58  % (10750)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.58  % (10758)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.58  
% 1.48/0.58  % (10758)Memory used [KB]: 10618
% 1.48/0.58  % (10758)Time elapsed: 0.148 s
% 1.48/0.58  % (10758)------------------------------
% 1.48/0.58  % (10758)------------------------------
% 1.48/0.58  % (10749)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.59  % (10750)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.59  
% 1.48/0.59  % (10750)Memory used [KB]: 10618
% 1.48/0.59  % (10750)Time elapsed: 0.145 s
% 1.48/0.59  % (10750)------------------------------
% 1.48/0.59  % (10750)------------------------------
% 1.48/0.61  % (10739)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.48/0.62  % (10763)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.48/0.62  % (10763)Refutation not found, incomplete strategy% (10763)------------------------------
% 1.48/0.62  % (10763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.62  % (10763)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.62  
% 1.48/0.62  % (10763)Memory used [KB]: 1663
% 1.48/0.62  % (10763)Time elapsed: 0.002 s
% 1.48/0.62  % (10763)------------------------------
% 1.48/0.62  % (10763)------------------------------
% 1.48/0.62  % (10738)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.48/0.62  % (10737)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.48/0.63  % (10755)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.48/0.63  % (10754)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.63  % (10735)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.48/0.63  % (10753)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.63  % (10735)Refutation not found, incomplete strategy% (10735)------------------------------
% 1.48/0.63  % (10735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.63  % (10735)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.63  
% 1.48/0.63  % (10735)Memory used [KB]: 1663
% 1.48/0.63  % (10735)Time elapsed: 0.154 s
% 1.48/0.63  % (10735)------------------------------
% 1.48/0.63  % (10735)------------------------------
% 1.48/0.63  % (10751)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.63  % (10747)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.48/0.63  % (10746)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.48/0.63  % (10746)Refutation not found, incomplete strategy% (10746)------------------------------
% 1.48/0.63  % (10746)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.63  % (10746)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.63  
% 1.48/0.63  % (10746)Memory used [KB]: 10618
% 1.48/0.63  % (10746)Time elapsed: 0.197 s
% 1.48/0.63  % (10746)------------------------------
% 1.48/0.63  % (10746)------------------------------
% 1.48/0.64  % (10762)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.48/0.64  % (10761)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.48/0.64  % (10759)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.64  % (10761)Refutation not found, incomplete strategy% (10761)------------------------------
% 1.48/0.64  % (10761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.64  % (10761)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.64  
% 1.48/0.64  % (10761)Memory used [KB]: 6140
% 1.48/0.64  % (10761)Time elapsed: 0.203 s
% 1.48/0.64  % (10761)------------------------------
% 1.48/0.64  % (10761)------------------------------
% 1.48/0.64  % (10745)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.64  % (10759)Refutation found. Thanks to Tanya!
% 1.48/0.64  % SZS status Theorem for theBenchmark
% 1.48/0.64  % SZS output start Proof for theBenchmark
% 1.48/0.64  fof(f157,plain,(
% 1.48/0.64    $false),
% 1.48/0.64    inference(resolution,[],[f94,f75])).
% 1.48/0.65  fof(f75,plain,(
% 1.48/0.65    r2_hidden(sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))))),
% 1.48/0.65    inference(unit_resulting_resolution,[],[f72,f71,f60])).
% 1.48/0.65  fof(f60,plain,(
% 1.48/0.65    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 1.48/0.65    inference(definition_unfolding,[],[f33,f49])).
% 1.48/0.65  fof(f49,plain,(
% 1.48/0.65    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.48/0.65    inference(definition_unfolding,[],[f39,f48])).
% 1.48/0.65  fof(f48,plain,(
% 1.48/0.65    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.48/0.65    inference(definition_unfolding,[],[f45,f46])).
% 1.48/0.65  fof(f46,plain,(
% 1.48/0.65    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.48/0.65    inference(cnf_transformation,[],[f12])).
% 1.48/0.65  fof(f12,axiom,(
% 1.48/0.65    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.48/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.48/0.65  fof(f45,plain,(
% 1.48/0.65    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.48/0.65    inference(cnf_transformation,[],[f11])).
% 1.48/0.65  fof(f11,axiom,(
% 1.48/0.65    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.48/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.48/0.65  fof(f39,plain,(
% 1.48/0.65    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.48/0.65    inference(cnf_transformation,[],[f10])).
% 2.14/0.65  fof(f10,axiom,(
% 2.14/0.65    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.14/0.65  fof(f33,plain,(
% 2.14/0.65    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | r2_hidden(sK3(X0,X1),X0)) )),
% 2.14/0.65    inference(cnf_transformation,[],[f22])).
% 2.14/0.65  fof(f22,plain,(
% 2.14/0.65    ! [X0,X1] : (? [X2] : (X1 != X2 & r2_hidden(X2,X0)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0)),
% 2.14/0.65    inference(ennf_transformation,[],[f18])).
% 2.14/0.65  fof(f18,axiom,(
% 2.14/0.65    ! [X0,X1] : ~(! [X2] : ~(X1 != X2 & r2_hidden(X2,X0)) & k1_xboole_0 != X0 & k1_tarski(X1) != X0)),
% 2.14/0.65    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_zfmisc_1)).
% 2.14/0.65  fof(f71,plain,(
% 2.14/0.65    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))),
% 2.14/0.65    inference(forward_demodulation,[],[f51,f42])).
% 2.14/0.65  fof(f42,plain,(
% 2.14/0.65    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.14/0.65    inference(cnf_transformation,[],[f5])).
% 2.14/0.65  % (10743)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.14/0.67  fof(f5,axiom,(
% 2.14/0.67    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.14/0.67  fof(f51,plain,(
% 2.14/0.67    k2_enumset1(sK0,sK0,sK0,sK0) != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.14/0.67    inference(definition_unfolding,[],[f24,f49,f47,f49])).
% 2.14/0.67  fof(f47,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)))) )),
% 2.14/0.67    inference(definition_unfolding,[],[f31,f44])).
% 2.14/0.67  fof(f44,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.14/0.67    inference(cnf_transformation,[],[f7])).
% 2.14/0.67  fof(f7,axiom,(
% 2.14/0.67    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.14/0.67  fof(f31,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.14/0.67    inference(cnf_transformation,[],[f3])).
% 2.14/0.67  fof(f3,axiom,(
% 2.14/0.67    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.14/0.67  fof(f24,plain,(
% 2.14/0.67    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.14/0.67    inference(cnf_transformation,[],[f21])).
% 2.14/0.67  fof(f21,plain,(
% 2.14/0.67    ? [X0,X1] : (k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) & k1_xboole_0 != k4_xboole_0(k1_tarski(X0),X1))),
% 2.14/0.67    inference(ennf_transformation,[],[f20])).
% 2.14/0.67  fof(f20,negated_conjecture,(
% 2.14/0.67    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 2.14/0.67    inference(negated_conjecture,[],[f19])).
% 2.14/0.67  fof(f19,conjecture,(
% 2.14/0.67    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | k1_xboole_0 = k4_xboole_0(k1_tarski(X0),X1))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).
% 2.14/0.67  fof(f72,plain,(
% 2.14/0.67    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1))))),
% 2.14/0.67    inference(forward_demodulation,[],[f52,f42])).
% 2.14/0.67  fof(f52,plain,(
% 2.14/0.67    k1_xboole_0 != k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),
% 2.14/0.67    inference(definition_unfolding,[],[f23,f47,f49])).
% 2.14/0.67  fof(f23,plain,(
% 2.14/0.67    k1_xboole_0 != k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.14/0.67    inference(cnf_transformation,[],[f21])).
% 2.14/0.67  fof(f94,plain,(
% 2.14/0.67    ( ! [X0] : (~r2_hidden(sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(X0,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0)))))) )),
% 2.14/0.67    inference(forward_demodulation,[],[f89,f42])).
% 2.14/0.67  fof(f89,plain,(
% 2.14/0.67    ( ! [X0] : (~r2_hidden(sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0),k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X0))))) )),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f79,f67])).
% 2.14/0.67  fof(f67,plain,(
% 2.14/0.67    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))))) )),
% 2.14/0.67    inference(equality_resolution,[],[f55])).
% 2.14/0.67  fof(f55,plain,(
% 2.14/0.67    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) != X2) )),
% 2.14/0.67    inference(definition_unfolding,[],[f28,f47])).
% 2.14/0.67  fof(f28,plain,(
% 2.14/0.67    ( ! [X2,X0,X3,X1] : (r2_hidden(X3,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.14/0.67    inference(cnf_transformation,[],[f2])).
% 2.14/0.67  fof(f2,axiom,(
% 2.14/0.67    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.14/0.67  fof(f79,plain,(
% 2.14/0.67    ~r2_hidden(sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0),k2_enumset1(sK0,sK0,sK0,sK0))),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f76,f68])).
% 2.14/0.67  fof(f68,plain,(
% 2.14/0.67    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 2.14/0.67    inference(equality_resolution,[],[f63])).
% 2.14/0.67  fof(f63,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 2.14/0.67    inference(definition_unfolding,[],[f36,f49])).
% 2.14/0.67  fof(f36,plain,(
% 2.14/0.67    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.14/0.67    inference(cnf_transformation,[],[f9])).
% 2.14/0.67  fof(f9,axiom,(
% 2.14/0.67    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.14/0.67    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.14/0.67  fof(f76,plain,(
% 2.14/0.67    sK0 != sK3(k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k2_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),sK1)))),sK0)),
% 2.14/0.67    inference(unit_resulting_resolution,[],[f72,f71,f59])).
% 2.14/0.67  fof(f59,plain,(
% 2.14/0.67    ( ! [X0,X1] : (sK3(X0,X1) != X1 | k1_xboole_0 = X0 | k2_enumset1(X1,X1,X1,X1) = X0) )),
% 2.14/0.67    inference(definition_unfolding,[],[f34,f49])).
% 2.14/0.67  fof(f34,plain,(
% 2.14/0.67    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | sK3(X0,X1) != X1) )),
% 2.14/0.67    inference(cnf_transformation,[],[f22])).
% 2.14/0.67  % SZS output end Proof for theBenchmark
% 2.14/0.67  % (10759)------------------------------
% 2.14/0.67  % (10759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.67  % (10759)Termination reason: Refutation
% 2.14/0.67  
% 2.14/0.67  % (10759)Memory used [KB]: 6524
% 2.14/0.67  % (10759)Time elapsed: 0.167 s
% 2.14/0.67  % (10759)------------------------------
% 2.14/0.67  % (10759)------------------------------
% 2.14/0.67  % (10733)Success in time 0.298 s
%------------------------------------------------------------------------------
