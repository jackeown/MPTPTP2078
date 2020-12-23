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
% DateTime   : Thu Dec  3 12:39:28 EST 2020

% Result     : Theorem 1.36s
% Output     : Refutation 1.36s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 123 expanded)
%              Number of leaves         :   13 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   72 ( 145 expanded)
%              Number of equality atoms :   46 ( 113 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f188,plain,(
    $false ),
    inference(subsumption_resolution,[],[f184,f137])).

fof(f137,plain,(
    ! [X0] : ~ r1_tarski(k1_enumset1(X0,X0,X0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f130,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f130,plain,(
    ! [X2] : k1_xboole_0 != k1_enumset1(X2,X2,X2) ),
    inference(subsumption_resolution,[],[f127,f76])).

fof(f76,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(unit_resulting_resolution,[],[f56,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k1_enumset1(X0,X0,X1))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k1_enumset1(X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f39,f43])).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f56,plain,(
    ! [X3,X1] : sP3(X3,X1,X3) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP3(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f127,plain,(
    ! [X2] :
      ( k1_xboole_0 != k1_enumset1(X2,X2,X2)
      | ~ r2_hidden(X2,k1_enumset1(X2,X2,X2)) ) ),
    inference(superposition,[],[f47,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f62,f32])).

fof(f62,plain,(
    ! [X1] : r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0) ),
    inference(superposition,[],[f35,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f30,f44,f44])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f31,f43])).

fof(f31,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f184,plain,(
    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_xboole_0) ),
    inference(backward_demodulation,[],[f181,f183])).

fof(f183,plain,(
    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f182,f57])).

fof(f57,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f26,f33])).

fof(f33,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f26,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f182,plain,(
    k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f169,f26])).

fof(f169,plain,(
    k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0) ),
    inference(superposition,[],[f97,f45])).

fof(f45,plain,(
    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f24,f28,f44])).

fof(f28,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f97,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    inference(forward_demodulation,[],[f82,f57])).

fof(f82,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f25,f34])).

fof(f25,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f181,plain,(
    r1_tarski(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_xboole_0) ),
    inference(backward_demodulation,[],[f158,f178])).

fof(f178,plain,(
    ! [X8,X7] : k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7) ),
    inference(forward_demodulation,[],[f165,f97])).

fof(f165,plain,(
    ! [X8,X7] : k4_xboole_0(k4_xboole_0(X8,X7),X7) = k5_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7))) ),
    inference(superposition,[],[f97,f46])).

fof(f46,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0)) ),
    inference(definition_unfolding,[],[f27,f28,f28])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f158,plain,(
    r1_tarski(k4_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_xboole_0) ),
    inference(superposition,[],[f63,f45])).

fof(f63,plain,(
    ! [X2,X3] : r1_tarski(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f35,f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:46:40 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (20100)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.49  % (20113)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.50  % (20116)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.50  % (20105)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.50  % (20113)Refutation not found, incomplete strategy% (20113)------------------------------
% 0.20/0.50  % (20113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (20121)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.51  % (20113)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20113)Memory used [KB]: 1663
% 0.20/0.51  % (20113)Time elapsed: 0.093 s
% 0.20/0.51  % (20113)------------------------------
% 0.20/0.51  % (20113)------------------------------
% 0.20/0.51  % (20108)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.52  % (20128)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (20128)Refutation not found, incomplete strategy% (20128)------------------------------
% 0.20/0.52  % (20128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20128)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20128)Memory used [KB]: 1663
% 0.20/0.52  % (20128)Time elapsed: 0.002 s
% 0.20/0.52  % (20128)------------------------------
% 0.20/0.52  % (20128)------------------------------
% 0.20/0.52  % (20120)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (20099)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (20101)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (20126)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (20102)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (20103)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.36/0.53  % (20112)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.36/0.54  % (20118)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.36/0.54  % (20114)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.36/0.54  % (20127)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.36/0.54  % (20117)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.36/0.54  % (20118)Refutation found. Thanks to Tanya!
% 1.36/0.54  % SZS status Theorem for theBenchmark
% 1.36/0.54  % SZS output start Proof for theBenchmark
% 1.36/0.54  fof(f188,plain,(
% 1.36/0.54    $false),
% 1.36/0.54    inference(subsumption_resolution,[],[f184,f137])).
% 1.36/0.54  fof(f137,plain,(
% 1.36/0.54    ( ! [X0] : (~r1_tarski(k1_enumset1(X0,X0,X0),k1_xboole_0)) )),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f130,f32])).
% 1.36/0.54  fof(f32,plain,(
% 1.36/0.54    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f23])).
% 1.36/0.54  fof(f23,plain,(
% 1.36/0.54    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 1.36/0.54    inference(ennf_transformation,[],[f4])).
% 1.36/0.54  fof(f4,axiom,(
% 1.36/0.54    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 1.36/0.54  fof(f130,plain,(
% 1.36/0.54    ( ! [X2] : (k1_xboole_0 != k1_enumset1(X2,X2,X2)) )),
% 1.36/0.54    inference(subsumption_resolution,[],[f127,f76])).
% 1.36/0.54  fof(f76,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f56,f54])).
% 1.36/0.54  fof(f54,plain,(
% 1.36/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,k1_enumset1(X0,X0,X1)) | ~sP3(X3,X1,X0)) )),
% 1.36/0.54    inference(equality_resolution,[],[f52])).
% 1.36/0.54  fof(f52,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k1_enumset1(X0,X0,X1) != X2) )),
% 1.36/0.54    inference(definition_unfolding,[],[f39,f43])).
% 1.36/0.54  fof(f43,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f12])).
% 1.36/0.54  fof(f12,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.36/0.54  fof(f39,plain,(
% 1.36/0.54    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 1.36/0.54    inference(cnf_transformation,[],[f10])).
% 1.36/0.54  fof(f10,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.36/0.54  fof(f56,plain,(
% 1.36/0.54    ( ! [X3,X1] : (sP3(X3,X1,X3)) )),
% 1.36/0.54    inference(equality_resolution,[],[f36])).
% 1.36/0.54  fof(f36,plain,(
% 1.36/0.54    ( ! [X0,X3,X1] : (X0 != X3 | sP3(X3,X1,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f10])).
% 1.36/0.54  fof(f127,plain,(
% 1.36/0.54    ( ! [X2] : (k1_xboole_0 != k1_enumset1(X2,X2,X2) | ~r2_hidden(X2,k1_enumset1(X2,X2,X2))) )),
% 1.36/0.54    inference(superposition,[],[f47,f78])).
% 1.36/0.54  fof(f78,plain,(
% 1.36/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.36/0.54    inference(unit_resulting_resolution,[],[f62,f32])).
% 1.36/0.54  fof(f62,plain,(
% 1.36/0.54    ( ! [X1] : (r1_tarski(k4_xboole_0(X1,X1),k1_xboole_0)) )),
% 1.36/0.54    inference(superposition,[],[f35,f34])).
% 1.36/0.54  fof(f34,plain,(
% 1.36/0.54    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f7])).
% 1.36/0.54  fof(f7,axiom,(
% 1.36/0.54    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.36/0.54  fof(f35,plain,(
% 1.36/0.54    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f8])).
% 1.36/0.54  fof(f8,axiom,(
% 1.36/0.54    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_xboole_1)).
% 1.36/0.54  fof(f47,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k1_enumset1(X0,X0,X0) != k4_xboole_0(k1_enumset1(X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f30,f44,f44])).
% 1.36/0.54  fof(f44,plain,(
% 1.36/0.54    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.36/0.54    inference(definition_unfolding,[],[f31,f43])).
% 1.36/0.54  fof(f31,plain,(
% 1.36/0.54    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f11])).
% 1.36/0.54  fof(f11,axiom,(
% 1.36/0.54    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.36/0.54  fof(f30,plain,(
% 1.36/0.54    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f18])).
% 1.36/0.54  fof(f18,axiom,(
% 1.36/0.54    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 1.36/0.54  fof(f184,plain,(
% 1.36/0.54    r1_tarski(k1_enumset1(sK0,sK0,sK0),k1_xboole_0)),
% 1.36/0.54    inference(backward_demodulation,[],[f181,f183])).
% 1.36/0.54  fof(f183,plain,(
% 1.36/0.54    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),
% 1.36/0.54    inference(forward_demodulation,[],[f182,f57])).
% 1.36/0.54  fof(f57,plain,(
% 1.36/0.54    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.36/0.54    inference(superposition,[],[f26,f33])).
% 1.36/0.54  fof(f33,plain,(
% 1.36/0.54    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.36/0.54    inference(cnf_transformation,[],[f5])).
% 1.36/0.54  fof(f5,axiom,(
% 1.36/0.54    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.36/0.54  fof(f26,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f1])).
% 1.36/0.54  fof(f1,axiom,(
% 1.36/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.36/0.54  fof(f182,plain,(
% 1.36/0.54    k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(k1_xboole_0,k1_enumset1(sK0,sK0,sK0))),
% 1.36/0.54    inference(forward_demodulation,[],[f169,f26])).
% 1.36/0.54  fof(f169,plain,(
% 1.36/0.54    k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k1_xboole_0)),
% 1.36/0.54    inference(superposition,[],[f97,f45])).
% 1.36/0.54  fof(f45,plain,(
% 1.36/0.54    k1_xboole_0 = k5_xboole_0(k1_enumset1(sK0,sK0,sK0),k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),
% 1.36/0.54    inference(definition_unfolding,[],[f24,f28,f44])).
% 1.36/0.54  fof(f28,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f9])).
% 1.36/0.54  fof(f9,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.36/0.54  fof(f24,plain,(
% 1.36/0.54    k1_xboole_0 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 1.36/0.54    inference(cnf_transformation,[],[f22])).
% 1.36/0.54  fof(f22,plain,(
% 1.36/0.54    ? [X0,X1] : k1_xboole_0 = k2_xboole_0(k1_tarski(X0),X1)),
% 1.36/0.54    inference(ennf_transformation,[],[f21])).
% 1.36/0.54  fof(f21,negated_conjecture,(
% 1.36/0.54    ~! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.36/0.54    inference(negated_conjecture,[],[f20])).
% 1.36/0.54  fof(f20,conjecture,(
% 1.36/0.54    ! [X0,X1] : k1_xboole_0 != k2_xboole_0(k1_tarski(X0),X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 1.36/0.54  fof(f97,plain,(
% 1.36/0.54    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) )),
% 1.36/0.54    inference(forward_demodulation,[],[f82,f57])).
% 1.36/0.54  fof(f82,plain,(
% 1.36/0.54    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) )),
% 1.36/0.54    inference(superposition,[],[f25,f34])).
% 1.36/0.54  fof(f25,plain,(
% 1.36/0.54    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.36/0.54    inference(cnf_transformation,[],[f6])).
% 1.36/0.54  fof(f6,axiom,(
% 1.36/0.54    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.36/0.54  fof(f181,plain,(
% 1.36/0.54    r1_tarski(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_xboole_0)),
% 1.36/0.54    inference(backward_demodulation,[],[f158,f178])).
% 1.36/0.54  fof(f178,plain,(
% 1.36/0.54    ( ! [X8,X7] : (k4_xboole_0(X8,X7) = k4_xboole_0(k4_xboole_0(X8,X7),X7)) )),
% 1.36/0.54    inference(forward_demodulation,[],[f165,f97])).
% 1.36/0.54  fof(f165,plain,(
% 1.36/0.54    ( ! [X8,X7] : (k4_xboole_0(k4_xboole_0(X8,X7),X7) = k5_xboole_0(X7,k5_xboole_0(X7,k4_xboole_0(X8,X7)))) )),
% 1.36/0.54    inference(superposition,[],[f97,f46])).
% 1.36/0.54  fof(f46,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,X0),X0))) )),
% 1.36/0.54    inference(definition_unfolding,[],[f27,f28,f28])).
% 1.36/0.54  fof(f27,plain,(
% 1.36/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.36/0.54    inference(cnf_transformation,[],[f3])).
% 1.36/0.54  fof(f3,axiom,(
% 1.36/0.54    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.36/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.36/0.54  fof(f158,plain,(
% 1.36/0.54    r1_tarski(k4_xboole_0(k4_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)),k1_xboole_0)),
% 1.36/0.54    inference(superposition,[],[f63,f45])).
% 1.36/0.54  fof(f63,plain,(
% 1.36/0.54    ( ! [X2,X3] : (r1_tarski(k4_xboole_0(X2,X3),k5_xboole_0(X3,X2))) )),
% 1.36/0.54    inference(superposition,[],[f35,f26])).
% 1.36/0.54  % SZS output end Proof for theBenchmark
% 1.36/0.54  % (20118)------------------------------
% 1.36/0.54  % (20118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (20118)Termination reason: Refutation
% 1.36/0.54  
% 1.36/0.54  % (20118)Memory used [KB]: 1791
% 1.36/0.54  % (20118)Time elapsed: 0.142 s
% 1.36/0.54  % (20118)------------------------------
% 1.36/0.54  % (20118)------------------------------
% 1.36/0.54  % (20117)Refutation not found, incomplete strategy% (20117)------------------------------
% 1.36/0.54  % (20117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.36/0.54  % (20117)Termination reason: Refutation not found, incomplete strategy
% 1.36/0.54  
% 1.36/0.54  % (20117)Memory used [KB]: 1663
% 1.36/0.54  % (20117)Time elapsed: 0.136 s
% 1.36/0.54  % (20117)------------------------------
% 1.36/0.54  % (20117)------------------------------
% 1.36/0.54  % (20107)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.36/0.54  % (20098)Success in time 0.188 s
%------------------------------------------------------------------------------
