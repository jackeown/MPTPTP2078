%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:29:55 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   18 (  25 expanded)
%              Number of leaves         :    4 (   7 expanded)
%              Depth                    :    9
%              Number of atoms          :   32 (  50 expanded)
%              Number of equality atoms :   10 (  13 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27,plain,(
    $false ),
    inference(global_subsumption,[],[f10,f26])).

fof(f26,plain,(
    r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(trivial_inequality_removal,[],[f25])).

fof(f25,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f11,f19])).

fof(f19,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f13,f14])).

fof(f14,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f12,f9])).

fof(f9,plain,(
    r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
    & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).

fof(f6,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
        & r1_tarski(k4_xboole_0(X0,X1),X2) )
   => ( ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2))
      & r1_tarski(k4_xboole_0(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      & r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k4_xboole_0(X0,X1),X2)
       => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
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

fof(f13,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f11,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f10,plain,(
    ~ r1_tarski(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f7])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:08:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (15867)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.42  % (15865)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.43  % (15865)Refutation found. Thanks to Tanya!
% 0.22/0.43  % SZS status Theorem for theBenchmark
% 0.22/0.43  % SZS output start Proof for theBenchmark
% 0.22/0.43  fof(f27,plain,(
% 0.22/0.43    $false),
% 0.22/0.43    inference(global_subsumption,[],[f10,f26])).
% 0.22/0.43  fof(f26,plain,(
% 0.22/0.43    r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.43    inference(trivial_inequality_removal,[],[f25])).
% 0.22/0.43  fof(f25,plain,(
% 0.22/0.43    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.43    inference(superposition,[],[f11,f19])).
% 0.22/0.43  fof(f19,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.43    inference(superposition,[],[f13,f14])).
% 0.22/0.43  fof(f14,plain,(
% 0.22/0.43    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,sK1),sK2)),
% 0.22/0.43    inference(resolution,[],[f12,f9])).
% 0.22/0.43  fof(f9,plain,(
% 0.22/0.43    r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  fof(f7,plain,(
% 0.22/0.43    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) & r1_tarski(k4_xboole_0(sK0,sK1),sK2)),
% 0.22/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f5,f6])).
% 0.22/0.43  fof(f6,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2)) => (~r1_tarski(sK0,k2_xboole_0(sK1,sK2)) & r1_tarski(k4_xboole_0(sK0,sK1),sK2))),
% 0.22/0.43    introduced(choice_axiom,[])).
% 0.22/0.43  fof(f5,plain,(
% 0.22/0.43    ? [X0,X1,X2] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) & r1_tarski(k4_xboole_0(X0,X1),X2))),
% 0.22/0.43    inference(ennf_transformation,[],[f4])).
% 0.22/0.43  fof(f4,negated_conjecture,(
% 0.22/0.43    ~! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.43    inference(negated_conjecture,[],[f3])).
% 0.22/0.43  fof(f3,conjecture,(
% 0.22/0.43    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).
% 0.22/0.43  fof(f12,plain,(
% 0.22/0.43    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f8,plain,(
% 0.22/0.43    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.22/0.43    inference(nnf_transformation,[],[f1])).
% 0.22/0.43  fof(f1,axiom,(
% 0.22/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.22/0.43  fof(f13,plain,(
% 0.22/0.43    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.43    inference(cnf_transformation,[],[f2])).
% 0.22/0.43  fof(f2,axiom,(
% 0.22/0.43    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.43  fof(f11,plain,(
% 0.22/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 0.22/0.43    inference(cnf_transformation,[],[f8])).
% 0.22/0.43  fof(f10,plain,(
% 0.22/0.43    ~r1_tarski(sK0,k2_xboole_0(sK1,sK2))),
% 0.22/0.43    inference(cnf_transformation,[],[f7])).
% 0.22/0.43  % SZS output end Proof for theBenchmark
% 0.22/0.43  % (15865)------------------------------
% 0.22/0.43  % (15865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.43  % (15865)Termination reason: Refutation
% 0.22/0.43  
% 0.22/0.43  % (15865)Memory used [KB]: 6012
% 0.22/0.43  % (15865)Time elapsed: 0.004 s
% 0.22/0.43  % (15865)------------------------------
% 0.22/0.43  % (15865)------------------------------
% 0.22/0.43  % (15864)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.44  % (15860)Success in time 0.073 s
%------------------------------------------------------------------------------
