%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:04 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   27 (  44 expanded)
%              Number of leaves         :    6 (  12 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 ( 116 expanded)
%              Number of equality atoms :   15 (  22 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f164,plain,(
    $false ),
    inference(subsumption_resolution,[],[f163,f25])).

fof(f25,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(unit_resulting_resolution,[],[f15,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f15,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( ~ r1_tarski(sK0,sK1)
    & r1_xboole_0(sK0,sK2)
    & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,X1)
        & r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
   => ( ~ r1_tarski(sK0,sK1)
      & r1_xboole_0(sK0,sK2)
      & r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,X1)
      & r1_xboole_0(X0,X2)
      & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X0,X2)
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
       => r1_tarski(X0,X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,k2_xboole_0(X1,X2)) )
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

fof(f163,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f160,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f160,plain,(
    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f157,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f157,plain,(
    ~ r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(unit_resulting_resolution,[],[f16,f18,f24,f23])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = X0
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

fof(f24,plain,(
    k1_xboole_0 != k4_xboole_0(sK0,sK1) ),
    inference(unit_resulting_resolution,[],[f17,f20])).

fof(f17,plain,(
    ~ r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f18,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f16,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (31939)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.20/0.41  % (31932)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.20/0.42  % (31929)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.20/0.42  % (31931)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.20/0.42  % (31933)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.20/0.42  % (31932)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.42  % SZS output start Proof for theBenchmark
% 0.20/0.42  fof(f164,plain,(
% 0.20/0.42    $false),
% 0.20/0.42    inference(subsumption_resolution,[],[f163,f25])).
% 0.20/0.42  fof(f25,plain,(
% 0.20/0.42    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f15,f21])).
% 0.20/0.42  fof(f21,plain,(
% 0.20/0.42    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f14,plain,(
% 0.20/0.42    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.20/0.42    inference(nnf_transformation,[],[f2])).
% 0.20/0.42  fof(f2,axiom,(
% 0.20/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.42  fof(f15,plain,(
% 0.20/0.42    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f13,plain,(
% 0.20/0.42    ~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f9,f12])).
% 0.20/0.42  fof(f12,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => (~r1_tarski(sK0,sK1) & r1_xboole_0(sK0,sK2) & r1_tarski(sK0,k2_xboole_0(sK1,sK2)))),
% 0.20/0.42    introduced(choice_axiom,[])).
% 0.20/0.42  fof(f9,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.20/0.42    inference(flattening,[],[f8])).
% 0.20/0.42  fof(f8,plain,(
% 0.20/0.42    ? [X0,X1,X2] : (~r1_tarski(X0,X1) & (r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 0.20/0.42    inference(ennf_transformation,[],[f7])).
% 0.20/0.42  fof(f7,negated_conjecture,(
% 0.20/0.42    ~! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.42    inference(negated_conjecture,[],[f6])).
% 0.20/0.42  fof(f6,conjecture,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,k2_xboole_0(X1,X2))) => r1_tarski(X0,X1))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).
% 0.20/0.42  fof(f163,plain,(
% 0.20/0.42    k1_xboole_0 != k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.20/0.42    inference(superposition,[],[f160,f22])).
% 0.20/0.42  fof(f22,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.42    inference(cnf_transformation,[],[f4])).
% 0.20/0.42  fof(f4,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.42  fof(f160,plain,(
% 0.20/0.42    k1_xboole_0 != k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f157,f20])).
% 0.20/0.42  fof(f20,plain,(
% 0.20/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f14])).
% 0.20/0.42  fof(f157,plain,(
% 0.20/0.42    ~r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f16,f18,f24,f23])).
% 0.20/0.42  fof(f23,plain,(
% 0.20/0.42    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | k1_xboole_0 = X0 | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f11])).
% 0.20/0.42  fof(f11,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k1_xboole_0 = X0 | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.42    inference(flattening,[],[f10])).
% 0.20/0.42  fof(f10,plain,(
% 0.20/0.42    ! [X0,X1,X2] : (k1_xboole_0 = X0 | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.42    inference(ennf_transformation,[],[f5])).
% 0.20/0.42  fof(f5,axiom,(
% 0.20/0.42    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X2) & r1_tarski(X0,X1)) => k1_xboole_0 = X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).
% 0.20/0.42  fof(f24,plain,(
% 0.20/0.42    k1_xboole_0 != k4_xboole_0(sK0,sK1)),
% 0.20/0.42    inference(unit_resulting_resolution,[],[f17,f20])).
% 0.20/0.42  fof(f17,plain,(
% 0.20/0.42    ~r1_tarski(sK0,sK1)),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  fof(f18,plain,(
% 0.20/0.42    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.20/0.42    inference(cnf_transformation,[],[f3])).
% 0.20/0.42  fof(f3,axiom,(
% 0.20/0.42    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.20/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.20/0.42  fof(f16,plain,(
% 0.20/0.42    r1_xboole_0(sK0,sK2)),
% 0.20/0.42    inference(cnf_transformation,[],[f13])).
% 0.20/0.42  % SZS output end Proof for theBenchmark
% 0.20/0.42  % (31932)------------------------------
% 0.20/0.42  % (31932)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.42  % (31932)Termination reason: Refutation
% 0.20/0.42  
% 0.20/0.42  % (31932)Memory used [KB]: 6140
% 0.20/0.42  % (31932)Time elapsed: 0.007 s
% 0.20/0.42  % (31932)------------------------------
% 0.20/0.42  % (31932)------------------------------
% 0.20/0.42  % (31923)Success in time 0.07 s
%------------------------------------------------------------------------------
