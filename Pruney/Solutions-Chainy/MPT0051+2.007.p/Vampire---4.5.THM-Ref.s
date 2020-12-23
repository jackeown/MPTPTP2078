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
% DateTime   : Thu Dec  3 12:29:55 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   41 (  60 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   16
%              Number of atoms          :   80 ( 128 expanded)
%              Number of equality atoms :   19 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1267,plain,(
    $false ),
    inference(global_subsumption,[],[f19,f1266])).

fof(f1266,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f1264])).

fof(f1264,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f22,f1225])).

fof(f1225,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f1224,f111])).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(resolution,[],[f25,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k4_xboole_0(X1,X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k4_xboole_0(X1,X0))
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f1224,plain,(
    ! [X12,X13] : r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X12)),k2_xboole_0(X13,sK2)) ),
    inference(trivial_inequality_removal,[],[f1222])).

fof(f1222,plain,(
    ! [X12,X13] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X12)),k2_xboole_0(X13,sK2)) ) ),
    inference(superposition,[],[f22,f1189])).

fof(f1189,plain,(
    ! [X8,X9] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,X8)),k2_xboole_0(X9,sK2)) ),
    inference(resolution,[],[f1183,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X2,X1)) ) ),
    inference(resolution,[],[f24,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(X0,k2_xboole_0(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

fof(f1183,plain,(
    ! [X7] : r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X7)),sK2) ),
    inference(trivial_inequality_removal,[],[f1181])).

fof(f1181,plain,(
    ! [X7] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X7)),sK2) ) ),
    inference(superposition,[],[f22,f1174])).

fof(f1174,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,X0)),sK2) ),
    inference(resolution,[],[f1172,f20])).

fof(f20,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1172,plain,(
    ! [X0] :
      ( ~ r1_tarski(sK1,X0)
      | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),sK2) ) ),
    inference(resolution,[],[f1129,f25])).

fof(f1129,plain,(
    ! [X26] :
      ( ~ r1_tarski(X26,k4_xboole_0(sK0,sK1))
      | k1_xboole_0 = k4_xboole_0(X26,sK2) ) ),
    inference(resolution,[],[f40,f18])).

fof(f18,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

% (30775)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
       => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f40,plain,(
    ! [X6,X7,X5] :
      ( ~ r1_tarski(X5,X6)
      | ~ r1_tarski(X7,X5)
      | k1_xboole_0 = k4_xboole_0(X7,X6) ) ),
    inference(resolution,[],[f26,f23])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f19,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 12:35:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (30778)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.20/0.41  % (30774)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.20/0.41  % (30772)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.42  % (30770)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.43  % (30773)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.44  % (30776)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.20/0.44  % (30781)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.20/0.45  % (30774)Refutation found. Thanks to Tanya!
% 0.20/0.45  % SZS status Theorem for theBenchmark
% 0.20/0.45  % SZS output start Proof for theBenchmark
% 0.20/0.45  fof(f1267,plain,(
% 0.20/0.45    $false),
% 0.20/0.45    inference(global_subsumption,[],[f19,f1266])).
% 0.20/0.45  fof(f1266,plain,(
% 0.20/0.45    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f1264])).
% 0.20/0.45  fof(f1264,plain,(
% 0.20/0.45    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(superposition,[],[f22,f1225])).
% 0.20/0.45  fof(f1225,plain,(
% 0.20/0.45    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(resolution,[],[f1224,f111])).
% 0.20/0.45  fof(f111,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.45    inference(resolution,[],[f25,f21])).
% 0.20/0.45  fof(f21,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X0)) | k1_xboole_0 = X0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f10])).
% 0.20/0.45  fof(f10,plain,(
% 0.20/0.45    ! [X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k4_xboole_0(X1,X0)))),
% 0.20/0.45    inference(ennf_transformation,[],[f5])).
% 0.20/0.45  fof(f5,axiom,(
% 0.20/0.45    ! [X0,X1] : (r1_tarski(X0,k4_xboole_0(X1,X0)) => k1_xboole_0 = X0)),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).
% 0.20/0.45  fof(f25,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f12])).
% 0.20/0.45  fof(f12,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f4])).
% 0.20/0.45  fof(f4,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 0.20/0.45  fof(f1224,plain,(
% 0.20/0.45    ( ! [X12,X13] : (r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X12)),k2_xboole_0(X13,sK2))) )),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f1222])).
% 0.20/0.45  fof(f1222,plain,(
% 0.20/0.45    ( ! [X12,X13] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X12)),k2_xboole_0(X13,sK2))) )),
% 0.20/0.45    inference(superposition,[],[f22,f1189])).
% 0.20/0.45  fof(f1189,plain,(
% 0.20/0.45    ( ! [X8,X9] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,X8)),k2_xboole_0(X9,sK2))) )),
% 0.20/0.45    inference(resolution,[],[f1183,f36])).
% 0.20/0.45  fof(f36,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X2,X1))) )),
% 0.20/0.45    inference(resolution,[],[f24,f23])).
% 0.20/0.45  fof(f23,plain,(
% 0.20/0.45    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f17,plain,(
% 0.20/0.45    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.45    inference(nnf_transformation,[],[f1])).
% 0.20/0.45  fof(f1,axiom,(
% 0.20/0.45    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.45  fof(f24,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f11])).
% 0.20/0.45  fof(f11,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X2,X1)) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(ennf_transformation,[],[f2])).
% 0.20/0.45  fof(f2,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(X0,k2_xboole_0(X2,X1)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).
% 0.20/0.45  fof(f1183,plain,(
% 0.20/0.45    ( ! [X7] : (r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X7)),sK2)) )),
% 0.20/0.45    inference(trivial_inequality_removal,[],[f1181])).
% 0.20/0.45  fof(f1181,plain,(
% 0.20/0.45    ( ! [X7] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,k2_xboole_0(sK1,X7)),sK2)) )),
% 0.20/0.45    inference(superposition,[],[f22,f1174])).
% 0.20/0.45  fof(f1174,plain,(
% 0.20/0.45    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k2_xboole_0(sK1,X0)),sK2)) )),
% 0.20/0.45    inference(resolution,[],[f1172,f20])).
% 0.20/0.45  fof(f20,plain,(
% 0.20/0.45    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.20/0.45    inference(cnf_transformation,[],[f6])).
% 0.20/0.45  fof(f6,axiom,(
% 0.20/0.45    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.20/0.45  fof(f1172,plain,(
% 0.20/0.45    ( ! [X0] : (~r1_tarski(sK1,X0) | k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),sK2)) )),
% 0.20/0.45    inference(resolution,[],[f1129,f25])).
% 0.20/0.45  fof(f1129,plain,(
% 0.20/0.45    ( ! [X26] : (~r1_tarski(X26,k4_xboole_0(sK0,sK1)) | k1_xboole_0 = k4_xboole_0(X26,sK2)) )),
% 0.20/0.45    inference(resolution,[],[f40,f18])).
% 0.20/0.45  fof(f18,plain,(
% 0.20/0.45    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  fof(f16,plain,(
% 0.20/0.45    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.20/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f15])).
% 0.20/0.45  fof(f15,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 0.20/0.45    introduced(choice_axiom,[])).
% 0.20/0.45  % (30775)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.20/0.45  fof(f9,plain,(
% 0.20/0.45    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.20/0.45    inference(ennf_transformation,[],[f8])).
% 0.20/0.45  fof(f8,negated_conjecture,(
% 0.20/0.45    ~! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.45    inference(negated_conjecture,[],[f7])).
% 0.20/0.45  fof(f7,conjecture,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.20/0.45  fof(f40,plain,(
% 0.20/0.45    ( ! [X6,X7,X5] : (~r1_tarski(X5,X6) | ~r1_tarski(X7,X5) | k1_xboole_0 = k4_xboole_0(X7,X6)) )),
% 0.20/0.45    inference(resolution,[],[f26,f23])).
% 0.20/0.45  fof(f26,plain,(
% 0.20/0.45    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f14])).
% 0.20/0.45  fof(f14,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.45    inference(flattening,[],[f13])).
% 0.20/0.45  fof(f13,plain,(
% 0.20/0.45    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.45    inference(ennf_transformation,[],[f3])).
% 0.20/0.45  fof(f3,axiom,(
% 0.20/0.45    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.45  fof(f22,plain,(
% 0.20/0.45    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.45    inference(cnf_transformation,[],[f17])).
% 0.20/0.45  fof(f19,plain,(
% 0.20/0.45    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.45    inference(cnf_transformation,[],[f16])).
% 0.20/0.45  % SZS output end Proof for theBenchmark
% 0.20/0.45  % (30774)------------------------------
% 0.20/0.45  % (30774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (30774)Termination reason: Refutation
% 0.20/0.45  
% 0.20/0.45  % (30774)Memory used [KB]: 7036
% 0.20/0.45  % (30774)Time elapsed: 0.041 s
% 0.20/0.45  % (30774)------------------------------
% 0.20/0.45  % (30774)------------------------------
% 0.20/0.45  % (30769)Success in time 0.096 s
%------------------------------------------------------------------------------
