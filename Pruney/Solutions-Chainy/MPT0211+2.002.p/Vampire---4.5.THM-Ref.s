%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:34:43 EST 2020

% Result     : Theorem 1.56s
% Output     : Refutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   47 (  66 expanded)
%              Number of leaves         :   13 (  22 expanded)
%              Depth                    :   14
%              Number of atoms          :   72 (  91 expanded)
%              Number of equality atoms :   39 (  58 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f249,plain,(
    $false ),
    inference(resolution,[],[f208,f122])).

fof(f122,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f208,plain,(
    ! [X0,X1] : ~ r1_tarski(k1_enumset1(sK0,X0,X1),k1_enumset1(sK0,sK1,sK2)) ),
    inference(superposition,[],[f194,f107])).

fof(f107,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X1,X2)) ),
    inference(definition_unfolding,[],[f80,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f194,plain,(
    ! [X0] : ~ r1_tarski(k2_xboole_0(k1_tarski(sK0),X0),k1_enumset1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f63,f168,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f168,plain,(
    ~ r1_tarski(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f162,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f162,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2)) ),
    inference(forward_demodulation,[],[f161,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).

fof(f161,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f132,f78])).

fof(f78,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

fof(f132,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK0,sK2)) ),
    inference(superposition,[],[f125,f115])).

fof(f115,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) ),
    inference(definition_unfolding,[],[f91,f90,f66,f66])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f125,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f124,f109])).

fof(f109,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0) ),
    inference(definition_unfolding,[],[f65,f66,f66])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f124,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK0,sK2)) ),
    inference(forward_demodulation,[],[f108,f109])).

fof(f108,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0)) ),
    inference(definition_unfolding,[],[f60,f66,f66])).

fof(f60,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f56])).

fof(f56,plain,
    ( ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))
   => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0)) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(ennf_transformation,[],[f42])).

fof(f42,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    inference(negated_conjecture,[],[f41])).

fof(f41,conjecture,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f63,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:23:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (20158)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.39/0.56  % (20154)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.56/0.56  % (20155)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.56/0.56  % (20167)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.56/0.56  % (20178)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.56/0.57  % (20156)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.56/0.57  % (20160)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.56/0.57  % (20172)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.56/0.57  % (20155)Refutation not found, incomplete strategy% (20155)------------------------------
% 1.56/0.57  % (20155)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (20164)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.56/0.58  % (20155)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (20155)Memory used [KB]: 1663
% 1.56/0.58  % (20155)Time elapsed: 0.137 s
% 1.56/0.58  % (20155)------------------------------
% 1.56/0.58  % (20155)------------------------------
% 1.56/0.58  % (20178)Refutation not found, incomplete strategy% (20178)------------------------------
% 1.56/0.58  % (20178)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.58  % (20162)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.56/0.58  % (20177)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.56/0.58  % (20159)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.56/0.58  % (20178)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.58  
% 1.56/0.58  % (20178)Memory used [KB]: 10746
% 1.56/0.58  % (20178)Time elapsed: 0.151 s
% 1.56/0.58  % (20178)------------------------------
% 1.56/0.58  % (20178)------------------------------
% 1.56/0.59  % (20172)Refutation not found, incomplete strategy% (20172)------------------------------
% 1.56/0.59  % (20172)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.59  % (20165)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.56/0.59  % (20172)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.59  
% 1.56/0.59  % (20172)Memory used [KB]: 1663
% 1.56/0.59  % (20172)Time elapsed: 0.157 s
% 1.56/0.59  % (20172)------------------------------
% 1.56/0.59  % (20172)------------------------------
% 1.56/0.59  % (20179)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.56/0.59  % (20168)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.56/0.60  % (20169)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.56/0.60  % (20157)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.56/0.60  % (20170)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.56/0.60  % (20161)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.56/0.61  % (20171)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.56/0.61  % (20173)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.56/0.61  % (20171)Refutation not found, incomplete strategy% (20171)------------------------------
% 1.56/0.61  % (20171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.61  % (20171)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.61  
% 1.56/0.61  % (20171)Memory used [KB]: 1791
% 1.56/0.61  % (20171)Time elapsed: 0.180 s
% 1.56/0.61  % (20171)------------------------------
% 1.56/0.61  % (20171)------------------------------
% 1.56/0.61  % (20176)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.56/0.61  % (20174)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.61  % (20163)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.56/0.61  % (20180)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.56/0.61  % (20183)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.56/0.61  % (20166)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.56/0.62  % (20183)Refutation not found, incomplete strategy% (20183)------------------------------
% 1.56/0.62  % (20183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (20183)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.62  
% 1.56/0.62  % (20183)Memory used [KB]: 1663
% 1.56/0.62  % (20183)Time elapsed: 0.002 s
% 1.56/0.62  % (20183)------------------------------
% 1.56/0.62  % (20183)------------------------------
% 1.56/0.62  % (20180)Refutation not found, incomplete strategy% (20180)------------------------------
% 1.56/0.62  % (20180)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (20180)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.62  
% 1.56/0.62  % (20180)Memory used [KB]: 6268
% 1.56/0.62  % (20180)Time elapsed: 0.151 s
% 1.56/0.62  % (20180)------------------------------
% 1.56/0.62  % (20180)------------------------------
% 1.56/0.62  % (20165)Refutation found. Thanks to Tanya!
% 1.56/0.62  % SZS status Theorem for theBenchmark
% 1.56/0.62  % SZS output start Proof for theBenchmark
% 1.56/0.62  fof(f249,plain,(
% 1.56/0.62    $false),
% 1.56/0.62    inference(resolution,[],[f208,f122])).
% 1.56/0.62  fof(f122,plain,(
% 1.56/0.62    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.56/0.62    inference(equality_resolution,[],[f75])).
% 1.56/0.62  fof(f75,plain,(
% 1.56/0.62    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.56/0.62    inference(cnf_transformation,[],[f59])).
% 1.56/0.62  fof(f59,plain,(
% 1.56/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.62    inference(flattening,[],[f58])).
% 1.56/0.62  fof(f58,plain,(
% 1.56/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.56/0.62    inference(nnf_transformation,[],[f1])).
% 1.56/0.62  fof(f1,axiom,(
% 1.56/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.56/0.62  fof(f208,plain,(
% 1.56/0.62    ( ! [X0,X1] : (~r1_tarski(k1_enumset1(sK0,X0,X1),k1_enumset1(sK0,sK1,sK2))) )),
% 1.56/0.62    inference(superposition,[],[f194,f107])).
% 1.56/0.62  fof(f107,plain,(
% 1.56/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X1,X2))) )),
% 1.56/0.62    inference(definition_unfolding,[],[f80,f66])).
% 1.56/0.62  fof(f66,plain,(
% 1.56/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f35])).
% 1.56/0.62  fof(f35,axiom,(
% 1.56/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.56/0.62  fof(f80,plain,(
% 1.56/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 1.56/0.62    inference(cnf_transformation,[],[f24])).
% 1.56/0.62  fof(f24,axiom,(
% 1.56/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 1.56/0.62  fof(f194,plain,(
% 1.56/0.62    ( ! [X0] : (~r1_tarski(k2_xboole_0(k1_tarski(sK0),X0),k1_enumset1(sK0,sK1,sK2))) )),
% 1.56/0.62    inference(unit_resulting_resolution,[],[f63,f168,f86])).
% 1.56/0.62  fof(f86,plain,(
% 1.56/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f50])).
% 1.56/0.62  fof(f50,plain,(
% 1.56/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 1.56/0.62    inference(flattening,[],[f49])).
% 1.56/0.62  fof(f49,plain,(
% 1.56/0.62    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.56/0.62    inference(ennf_transformation,[],[f5])).
% 1.56/0.62  fof(f5,axiom,(
% 1.56/0.62    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 1.56/0.62  fof(f168,plain,(
% 1.56/0.62    ~r1_tarski(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))),
% 1.56/0.62    inference(unit_resulting_resolution,[],[f162,f71])).
% 1.56/0.62  fof(f71,plain,(
% 1.56/0.62    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.56/0.62    inference(cnf_transformation,[],[f44])).
% 1.56/0.62  fof(f44,plain,(
% 1.56/0.62    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.56/0.62    inference(ennf_transformation,[],[f3])).
% 1.56/0.62  fof(f3,axiom,(
% 1.56/0.62    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.56/0.62  fof(f162,plain,(
% 1.56/0.62    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK1,sK2))),
% 1.56/0.62    inference(forward_demodulation,[],[f161,f77])).
% 1.56/0.62  fof(f77,plain,(
% 1.56/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f39])).
% 1.56/0.62  fof(f39,axiom,(
% 1.56/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X0,X2,X1)),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_enumset1)).
% 1.56/0.62  fof(f161,plain,(
% 1.56/0.62    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK0,sK2,sK1))),
% 1.56/0.62    inference(forward_demodulation,[],[f132,f78])).
% 1.56/0.62  fof(f78,plain,(
% 1.56/0.62    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f20])).
% 1.56/0.62  fof(f20,axiom,(
% 1.56/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X1,X2,X0)),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).
% 1.56/0.62  fof(f132,plain,(
% 1.56/0.62    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_tarski(sK0),k1_enumset1(sK1,sK0,sK2))),
% 1.56/0.62    inference(superposition,[],[f125,f115])).
% 1.56/0.62  fof(f115,plain,(
% 1.56/0.62    ( ! [X2,X0,X3,X1] : (k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_xboole_0(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) )),
% 1.56/0.62    inference(definition_unfolding,[],[f91,f90,f66,f66])).
% 1.56/0.62  fof(f90,plain,(
% 1.56/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 1.56/0.62    inference(cnf_transformation,[],[f26])).
% 1.56/0.62  fof(f26,axiom,(
% 1.56/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_enumset1)).
% 1.56/0.62  fof(f91,plain,(
% 1.56/0.62    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.56/0.62    inference(cnf_transformation,[],[f18])).
% 1.56/0.62  fof(f18,axiom,(
% 1.56/0.62    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.56/0.62  fof(f125,plain,(
% 1.56/0.62    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK0,sK0,sK2))),
% 1.56/0.62    inference(forward_demodulation,[],[f124,f109])).
% 1.56/0.62  fof(f109,plain,(
% 1.56/0.62    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k1_enumset1(X1,X1,X0)) )),
% 1.56/0.62    inference(definition_unfolding,[],[f65,f66,f66])).
% 1.56/0.62  fof(f65,plain,(
% 1.56/0.62    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.56/0.62    inference(cnf_transformation,[],[f17])).
% 1.56/0.62  fof(f17,axiom,(
% 1.56/0.62    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.56/0.62  fof(f124,plain,(
% 1.56/0.62    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK0,sK0,sK2))),
% 1.56/0.62    inference(forward_demodulation,[],[f108,f109])).
% 1.56/0.62  fof(f108,plain,(
% 1.56/0.62    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k1_enumset1(sK1,sK1,sK0),k1_enumset1(sK2,sK2,sK0))),
% 1.56/0.62    inference(definition_unfolding,[],[f60,f66,f66])).
% 1.56/0.62  fof(f60,plain,(
% 1.56/0.62    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.56/0.62    inference(cnf_transformation,[],[f57])).
% 1.56/0.62  fof(f57,plain,(
% 1.56/0.62    k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.56/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f43,f56])).
% 1.56/0.62  fof(f56,plain,(
% 1.56/0.62    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) => k1_enumset1(sK0,sK1,sK2) != k2_xboole_0(k2_tarski(sK1,sK0),k2_tarski(sK2,sK0))),
% 1.56/0.62    introduced(choice_axiom,[])).
% 1.56/0.62  fof(f43,plain,(
% 1.56/0.62    ? [X0,X1,X2] : k1_enumset1(X0,X1,X2) != k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.56/0.62    inference(ennf_transformation,[],[f42])).
% 1.56/0.62  fof(f42,negated_conjecture,(
% 1.56/0.62    ~! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.56/0.62    inference(negated_conjecture,[],[f41])).
% 1.56/0.62  fof(f41,conjecture,(
% 1.56/0.62    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.56/0.62  fof(f63,plain,(
% 1.56/0.62    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.56/0.62    inference(cnf_transformation,[],[f14])).
% 1.56/0.62  fof(f14,axiom,(
% 1.56/0.62    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.56/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.56/0.62  % SZS output end Proof for theBenchmark
% 1.56/0.62  % (20165)------------------------------
% 1.56/0.62  % (20165)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (20165)Termination reason: Refutation
% 1.56/0.62  
% 1.56/0.62  % (20165)Memory used [KB]: 6396
% 1.56/0.62  % (20165)Time elapsed: 0.194 s
% 1.56/0.62  % (20165)------------------------------
% 1.56/0.62  % (20165)------------------------------
% 1.56/0.62  % (20166)Refutation not found, incomplete strategy% (20166)------------------------------
% 1.56/0.62  % (20166)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.56/0.62  % (20166)Termination reason: Refutation not found, incomplete strategy
% 1.56/0.62  
% 1.56/0.62  % (20166)Memory used [KB]: 10618
% 1.56/0.62  % (20166)Time elapsed: 0.189 s
% 1.56/0.62  % (20166)------------------------------
% 1.56/0.62  % (20166)------------------------------
% 1.56/0.62  % (20153)Success in time 0.255 s
%------------------------------------------------------------------------------
