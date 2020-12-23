%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:16 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   47 (  69 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   86 ( 126 expanded)
%              Number of equality atoms :   45 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f545,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f67,f407,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f38,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ( X0 = X1
          | r2_hidden(X1,X2) )
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).

fof(f407,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0)) ),
    inference(forward_demodulation,[],[f400,f121])).

fof(f121,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f86,f65])).

fof(f65,plain,(
    ! [X2,X1] :
      ( r2_hidden(X1,X2)
      | k2_tarski(X1,X1) = k4_xboole_0(k2_tarski(X1,X1),X2) ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | X0 != X1
      | k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | X0 != X1
      | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f86,plain,(
    ~ r2_hidden(sK0,k2_tarski(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f29,f30,f70])).

fof(f70,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X1))
      | X1 = X3
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( X0 = X3
      | X1 = X3
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f30,plain,(
    sK0 != sK3 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( X0 != X3
      & X0 != X2
      & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ~ ( X0 != X3
          & X0 != X2
          & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ~ ( X0 != X3
        & X0 != X2
        & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

fof(f29,plain,(
    sK0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f400,plain,(
    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3))) ),
    inference(unit_resulting_resolution,[],[f399,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f51])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f399,plain,(
    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f185,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f37,f38,f51,f38])).

fof(f37,plain,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

fof(f185,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k2_tarski(sK0,sK1))),k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f132,f57])).

fof(f57,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f39,f51,f51])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f132,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),X0)),k2_tarski(sK2,sK3)) ),
    inference(unit_resulting_resolution,[],[f55,f28,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f28,plain,(
    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f36,f51])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f67,plain,(
    ! [X0,X3] : r2_hidden(X3,k2_tarski(X0,X3)) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3] :
      ( r2_hidden(X3,X2)
      | k2_tarski(X0,X3) != X2 ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( X1 != X3
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (16089)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.50  % (16105)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.51  % (16103)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.51  % (16080)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.51  % (16082)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (16079)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.51  % (16090)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.51  % (16094)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (16095)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (16091)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.52  % (16079)Refutation not found, incomplete strategy% (16079)------------------------------
% 0.20/0.52  % (16079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16079)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16079)Memory used [KB]: 1663
% 0.20/0.52  % (16079)Time elapsed: 0.096 s
% 0.20/0.52  % (16079)------------------------------
% 0.20/0.52  % (16079)------------------------------
% 0.20/0.52  % (16088)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.52  % (16087)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (16078)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (16086)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (16096)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.52  % (16093)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.52  % (16100)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (16106)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (16097)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.53  % (16101)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.53  % (16102)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.53  % (16098)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.53  % (16081)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (16099)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.53  % (16084)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (16092)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.53  % (16083)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.54  % (16085)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.55  % (16107)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.56  % (16104)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (16104)Refutation not found, incomplete strategy% (16104)------------------------------
% 0.20/0.56  % (16104)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (16104)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (16104)Memory used [KB]: 6268
% 0.20/0.56  % (16104)Time elapsed: 0.149 s
% 0.20/0.56  % (16104)------------------------------
% 0.20/0.56  % (16104)------------------------------
% 0.20/0.56  % (16103)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  fof(f545,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f67,f407,f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k2_tarski(X0,X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f44,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,axiom,(
% 0.20/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k1_tarski(X0) != k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> ((X0 = X1 | r2_hidden(X1,X2)) & ~r2_hidden(X0,X2)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l38_zfmisc_1)).
% 0.20/0.56  fof(f407,plain,(
% 0.20/0.56    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK0))),
% 0.20/0.56    inference(forward_demodulation,[],[f400,f121])).
% 0.20/0.56  fof(f121,plain,(
% 0.20/0.56    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3))),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f86,f65])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ( ! [X2,X1] : (r2_hidden(X1,X2) | k2_tarski(X1,X1) = k4_xboole_0(k2_tarski(X1,X1),X2)) )),
% 0.20/0.56    inference(equality_resolution,[],[f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | X0 != X1 | k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f42,f38])).
% 0.20/0.56  fof(f42,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | X0 != X1 | k1_tarski(X0) = k4_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f86,plain,(
% 0.20/0.56    ~r2_hidden(sK0,k2_tarski(sK2,sK3))),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f29,f30,f70])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_tarski(X0,X1)) | X1 = X3 | X0 = X3) )),
% 0.20/0.56    inference(equality_resolution,[],[f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (X0 = X3 | X1 = X3 | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  fof(f11,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    sK0 != sK3),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ? [X0,X1,X2,X3] : (X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.56    inference(ennf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,negated_conjecture,(
% 0.20/0.56    ~! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.56    inference(negated_conjecture,[],[f21])).
% 0.20/0.56  fof(f21,conjecture,(
% 0.20/0.56    ! [X0,X1,X2,X3] : ~(X0 != X3 & X0 != X2 & r1_tarski(k2_tarski(X0,X1),k2_tarski(X2,X3)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    sK0 != sK2),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f400,plain,(
% 0.20/0.56    k2_tarski(sK0,sK0) = k4_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3)))),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f399,f54])).
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f35,f51])).
% 0.20/0.56  fof(f51,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.20/0.56    inference(cnf_transformation,[],[f27])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.20/0.56  fof(f399,plain,(
% 0.20/0.56    r1_tarski(k2_tarski(sK0,sK0),k2_tarski(sK2,sK3))),
% 0.20/0.56    inference(superposition,[],[f185,f56])).
% 0.20/0.56  fof(f56,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k2_tarski(X0,X0) = k4_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f37,f38,f51,f38])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f20,axiom,(
% 0.20/0.56    ! [X0,X1] : k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).
% 0.20/0.56  fof(f185,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,k2_tarski(sK0,sK1))),k2_tarski(sK2,sK3))) )),
% 0.20/0.56    inference(superposition,[],[f132,f57])).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.20/0.56    inference(definition_unfolding,[],[f39,f51,f51])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.20/0.56  fof(f132,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),X0)),k2_tarski(sK2,sK3))) )),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f55,f28,f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.56    inference(flattening,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3))),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f36,f51])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    ( ! [X0,X3] : (r2_hidden(X3,k2_tarski(X0,X3))) )),
% 0.20/0.56    inference(equality_resolution,[],[f66])).
% 0.20/0.56  fof(f66,plain,(
% 0.20/0.56    ( ! [X2,X0,X3] : (r2_hidden(X3,X2) | k2_tarski(X0,X3) != X2) )),
% 0.20/0.56    inference(equality_resolution,[],[f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X2,X0,X3,X1] : (X1 != X3 | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 0.20/0.56    inference(cnf_transformation,[],[f11])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (16103)------------------------------
% 0.20/0.56  % (16103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (16103)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (16103)Memory used [KB]: 6524
% 0.20/0.56  % (16103)Time elapsed: 0.146 s
% 0.20/0.56  % (16103)------------------------------
% 0.20/0.56  % (16103)------------------------------
% 0.20/0.56  % (16077)Success in time 0.203 s
%------------------------------------------------------------------------------
