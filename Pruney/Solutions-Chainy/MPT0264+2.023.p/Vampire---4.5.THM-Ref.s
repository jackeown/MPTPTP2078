%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:24 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :   48 ( 112 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   82 ( 158 expanded)
%              Number of equality atoms :   56 ( 126 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f179,plain,(
    $false ),
    inference(subsumption_resolution,[],[f178,f98])).

fof(f98,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f66,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k2_enumset1(X1,X1,X1,X1) != k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1)) ) ),
    inference(definition_unfolding,[],[f26,f40,f40])).

fof(f40,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f30,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f66,plain,(
    ~ r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f21,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_enumset1(X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_enumset1(X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f23,f40])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f21,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( X0 != X1
      & r2_hidden(X1,X2)
      & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( X0 != X1
          & r2_hidden(X1,X2)
          & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( X0 != X1
        & r2_hidden(X1,X2)
        & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

fof(f178,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(forward_demodulation,[],[f164,f84])).

fof(f84,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0)) ),
    inference(unit_resulting_resolution,[],[f57,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f57,plain,(
    ! [X2,X1] : r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_enumset1(X2,X2,X2,X2) != X0
      | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2)) ) ),
    inference(definition_unfolding,[],[f36,f40,f39])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X2) != X0
      | r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f164,plain,(
    k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f91,f111])).

fof(f111,plain,(
    k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1)) ),
    inference(unit_resulting_resolution,[],[f20,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0)) ) ),
    inference(definition_unfolding,[],[f27,f40,f40])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).

fof(f20,plain,(
    r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f91,plain,(
    ! [X1] : k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X1) = k3_xboole_0(k3_xboole_0(sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1)) ),
    inference(superposition,[],[f73,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f73,plain,(
    ! [X10] : k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,X10)) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X10) ),
    inference(superposition,[],[f28,f41])).

fof(f41,plain,(
    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2) ),
    inference(definition_unfolding,[],[f19,f40,f39])).

fof(f19,plain,(
    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f28,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:49:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (22689)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.19/0.48  % (22679)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.49  % (22687)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.19/0.49  % (22681)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.19/0.50  % (22680)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.51  % (22682)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.19/0.51  % (22678)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.27/0.52  % (22691)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.27/0.52  % (22683)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.27/0.52  % (22701)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.27/0.52  % (22693)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.27/0.52  % (22684)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.27/0.52  % (22695)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.27/0.53  % (22702)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.27/0.53  % (22706)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.27/0.53  % (22703)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.27/0.53  % (22705)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.27/0.53  % (22699)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.27/0.53  % (22704)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.42/0.53  % (22696)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.42/0.53  % (22698)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.42/0.54  % (22690)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.42/0.54  % (22688)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.42/0.54  % (22685)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.42/0.54  % (22697)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.42/0.54  % (22700)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.42/0.54  % (22694)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.42/0.54  % (22686)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.42/0.54  % (22692)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.42/0.54  % (22707)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.42/0.55  % (22694)Refutation not found, incomplete strategy% (22694)------------------------------
% 1.42/0.55  % (22694)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (22707)Refutation not found, incomplete strategy% (22707)------------------------------
% 1.42/0.55  % (22707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.55  % (22707)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (22707)Memory used [KB]: 1663
% 1.42/0.55  % (22707)Time elapsed: 0.114 s
% 1.42/0.55  % (22707)------------------------------
% 1.42/0.55  % (22707)------------------------------
% 1.42/0.55  % (22697)Refutation found. Thanks to Tanya!
% 1.42/0.55  % SZS status Theorem for theBenchmark
% 1.42/0.55  % (22694)Termination reason: Refutation not found, incomplete strategy
% 1.42/0.55  
% 1.42/0.55  % (22694)Memory used [KB]: 10618
% 1.42/0.55  % (22694)Time elapsed: 0.151 s
% 1.42/0.55  % (22694)------------------------------
% 1.42/0.55  % (22694)------------------------------
% 1.42/0.57  % SZS output start Proof for theBenchmark
% 1.42/0.57  fof(f179,plain,(
% 1.42/0.57    $false),
% 1.42/0.57    inference(subsumption_resolution,[],[f178,f98])).
% 1.42/0.57  fof(f98,plain,(
% 1.42/0.57    k2_enumset1(sK1,sK1,sK1,sK1) != k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.42/0.57    inference(unit_resulting_resolution,[],[f66,f46])).
% 1.42/0.57  fof(f46,plain,(
% 1.42/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | k2_enumset1(X1,X1,X1,X1) != k3_xboole_0(X0,k2_enumset1(X1,X1,X1,X1))) )),
% 1.42/0.57    inference(definition_unfolding,[],[f26,f40,f40])).
% 1.42/0.57  fof(f40,plain,(
% 1.42/0.57    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f30,f39])).
% 1.42/0.57  fof(f39,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 1.42/0.57    inference(definition_unfolding,[],[f32,f38])).
% 1.42/0.57  fof(f38,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f7])).
% 1.42/0.57  fof(f7,axiom,(
% 1.42/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.57  fof(f32,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f6])).
% 1.42/0.57  fof(f6,axiom,(
% 1.42/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.57  fof(f30,plain,(
% 1.42/0.57    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f5])).
% 1.42/0.57  fof(f5,axiom,(
% 1.42/0.57    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.42/0.57  fof(f26,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) | r2_hidden(X1,X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f15])).
% 1.42/0.57  fof(f15,plain,(
% 1.42/0.57    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 1.42/0.57    inference(ennf_transformation,[],[f9])).
% 1.42/0.57  fof(f9,axiom,(
% 1.42/0.57    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 1.42/0.57  fof(f66,plain,(
% 1.42/0.57    ~r2_hidden(sK1,k2_enumset1(sK0,sK0,sK0,sK0))),
% 1.42/0.57    inference(unit_resulting_resolution,[],[f21,f53])).
% 1.42/0.57  fof(f53,plain,(
% 1.42/0.57    ( ! [X2,X0] : (~r2_hidden(X2,k2_enumset1(X0,X0,X0,X0)) | X0 = X2) )),
% 1.42/0.57    inference(equality_resolution,[],[f44])).
% 1.42/0.57  fof(f44,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_enumset1(X0,X0,X0,X0) != X1) )),
% 1.42/0.57    inference(definition_unfolding,[],[f23,f40])).
% 1.42/0.57  fof(f23,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 1.42/0.57    inference(cnf_transformation,[],[f4])).
% 1.42/0.57  fof(f4,axiom,(
% 1.42/0.57    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.42/0.57  fof(f21,plain,(
% 1.42/0.57    sK0 != sK1),
% 1.42/0.57    inference(cnf_transformation,[],[f14])).
% 1.42/0.57  fof(f14,plain,(
% 1.42/0.57    ? [X0,X1,X2] : (X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.42/0.57    inference(ennf_transformation,[],[f13])).
% 1.42/0.57  fof(f13,negated_conjecture,(
% 1.42/0.57    ~! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.42/0.57    inference(negated_conjecture,[],[f12])).
% 1.42/0.57  fof(f12,conjecture,(
% 1.42/0.57    ! [X0,X1,X2] : ~(X0 != X1 & r2_hidden(X1,X2) & k1_tarski(X0) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).
% 1.42/0.57  fof(f178,plain,(
% 1.42/0.57    k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.42/0.57    inference(forward_demodulation,[],[f164,f84])).
% 1.42/0.57  fof(f84,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(k2_enumset1(X0,X0,X0,X0),k2_enumset1(X1,X1,X1,X0))) )),
% 1.42/0.57    inference(unit_resulting_resolution,[],[f57,f31])).
% 1.42/0.57  fof(f31,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.42/0.57    inference(cnf_transformation,[],[f17])).
% 1.42/0.57  fof(f17,plain,(
% 1.42/0.57    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.42/0.57    inference(ennf_transformation,[],[f3])).
% 1.42/0.57  fof(f3,axiom,(
% 1.42/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.42/0.57  fof(f57,plain,(
% 1.42/0.57    ( ! [X2,X1] : (r1_tarski(k2_enumset1(X2,X2,X2,X2),k2_enumset1(X1,X1,X1,X2))) )),
% 1.42/0.57    inference(equality_resolution,[],[f49])).
% 1.42/0.57  fof(f49,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X2,X2,X2,X2) != X0 | r1_tarski(X0,k2_enumset1(X1,X1,X1,X2))) )),
% 1.42/0.57    inference(definition_unfolding,[],[f36,f40,f39])).
% 1.42/0.57  fof(f36,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (k1_tarski(X2) != X0 | r1_tarski(X0,k2_tarski(X1,X2))) )),
% 1.42/0.57    inference(cnf_transformation,[],[f18])).
% 1.42/0.57  fof(f18,plain,(
% 1.42/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.42/0.57    inference(ennf_transformation,[],[f11])).
% 1.42/0.57  fof(f11,axiom,(
% 1.42/0.57    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 1.42/0.57  fof(f164,plain,(
% 1.42/0.57    k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),k2_enumset1(sK1,sK1,sK1,sK1)) = k3_xboole_0(k2_enumset1(sK1,sK1,sK1,sK1),k2_enumset1(sK0,sK0,sK0,sK1))),
% 1.42/0.57    inference(superposition,[],[f91,f111])).
% 1.42/0.57  fof(f111,plain,(
% 1.42/0.57    k2_enumset1(sK1,sK1,sK1,sK1) = k3_xboole_0(sK2,k2_enumset1(sK1,sK1,sK1,sK1))),
% 1.42/0.57    inference(unit_resulting_resolution,[],[f20,f47])).
% 1.42/0.57  fof(f47,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k2_enumset1(X0,X0,X0,X0) = k3_xboole_0(X1,k2_enumset1(X0,X0,X0,X0))) )),
% 1.42/0.57    inference(definition_unfolding,[],[f27,f40,f40])).
% 1.42/0.57  fof(f27,plain,(
% 1.42/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0))) )),
% 1.42/0.57    inference(cnf_transformation,[],[f16])).
% 1.42/0.57  fof(f16,plain,(
% 1.42/0.57    ! [X0,X1] : (k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)) | ~r2_hidden(X0,X1))),
% 1.42/0.57    inference(ennf_transformation,[],[f10])).
% 1.42/0.57  fof(f10,axiom,(
% 1.42/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => k1_tarski(X0) = k3_xboole_0(X1,k1_tarski(X0)))),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l31_zfmisc_1)).
% 1.42/0.57  fof(f20,plain,(
% 1.42/0.57    r2_hidden(sK1,sK2)),
% 1.42/0.57    inference(cnf_transformation,[],[f14])).
% 1.42/0.57  fof(f91,plain,(
% 1.42/0.57    ( ! [X1] : (k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X1) = k3_xboole_0(k3_xboole_0(sK2,X1),k2_enumset1(sK0,sK0,sK0,sK1))) )),
% 1.42/0.57    inference(superposition,[],[f73,f29])).
% 1.42/0.57  fof(f29,plain,(
% 1.42/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.42/0.57    inference(cnf_transformation,[],[f1])).
% 1.42/0.57  fof(f1,axiom,(
% 1.42/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.42/0.57  fof(f73,plain,(
% 1.42/0.57    ( ! [X10] : (k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),k3_xboole_0(sK2,X10)) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK0),X10)) )),
% 1.42/0.57    inference(superposition,[],[f28,f41])).
% 1.42/0.57  fof(f41,plain,(
% 1.42/0.57    k2_enumset1(sK0,sK0,sK0,sK0) = k3_xboole_0(k2_enumset1(sK0,sK0,sK0,sK1),sK2)),
% 1.42/0.57    inference(definition_unfolding,[],[f19,f40,f39])).
% 1.42/0.57  fof(f19,plain,(
% 1.42/0.57    k1_tarski(sK0) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.42/0.57    inference(cnf_transformation,[],[f14])).
% 1.42/0.57  fof(f28,plain,(
% 1.42/0.57    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.42/0.57    inference(cnf_transformation,[],[f2])).
% 1.42/0.57  fof(f2,axiom,(
% 1.42/0.57    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.42/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.42/0.57  % SZS output end Proof for theBenchmark
% 1.42/0.57  % (22697)------------------------------
% 1.42/0.57  % (22697)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.57  % (22697)Termination reason: Refutation
% 1.42/0.57  
% 1.42/0.57  % (22697)Memory used [KB]: 1918
% 1.42/0.57  % (22697)Time elapsed: 0.148 s
% 1.42/0.57  % (22697)------------------------------
% 1.42/0.57  % (22697)------------------------------
% 1.42/0.57  % (22677)Success in time 0.221 s
%------------------------------------------------------------------------------
