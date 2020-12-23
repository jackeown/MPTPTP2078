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
% DateTime   : Thu Dec  3 12:29:46 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   23 (  32 expanded)
%              Number of leaves         :    6 (  10 expanded)
%              Depth                    :    8
%              Number of atoms          :   33 (  49 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f102,plain,(
    $false ),
    inference(subsumption_resolution,[],[f23,f97])).

fof(f97,plain,(
    ! [X2] : k3_xboole_0(sK1,k2_xboole_0(sK0,X2)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X2)) ),
    inference(superposition,[],[f25,f37])).

fof(f37,plain,(
    sK0 = k3_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f16,f22])).

fof(f22,plain,(
    sK1 = k2_xboole_0(sK0,sK1) ),
    inference(resolution,[],[f17,f12])).

fof(f12,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,
    ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).

fof(f10,plain,
    ( ? [X0,X1,X2] :
        ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_tarski(X0,X1) )
   => ( k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0,X1,X2] :
      ( k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(X0,X1)
       => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f16,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2)) ),
    inference(superposition,[],[f18,f15])).

fof(f15,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f18,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f23,plain,(
    k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f19,f15])).

fof(f19,plain,(
    k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(backward_demodulation,[],[f13,f15])).

fof(f13,plain,(
    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f11])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:51:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.43  % (19683)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.43  % (19693)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.22/0.44  % (19693)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f102,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(subsumption_resolution,[],[f23,f97])).
% 0.22/0.44  fof(f97,plain,(
% 0.22/0.44    ( ! [X2] : (k3_xboole_0(sK1,k2_xboole_0(sK0,X2)) = k2_xboole_0(sK0,k3_xboole_0(sK1,X2))) )),
% 0.22/0.44    inference(superposition,[],[f25,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    sK0 = k3_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(superposition,[],[f16,f22])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    sK1 = k2_xboole_0(sK0,sK1)),
% 0.22/0.44    inference(resolution,[],[f17,f12])).
% 0.22/0.44  fof(f12,plain,(
% 0.22/0.44    r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  fof(f11,plain,(
% 0.22/0.44    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1)),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f8,f10])).
% 0.22/0.44  fof(f10,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1) & r1_tarski(X0,X1)) => (k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_tarski(sK0,sK1))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f8,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (k2_xboole_0(X0,k3_xboole_0(X2,X1)) != k3_xboole_0(k2_xboole_0(X0,X2),X1) & r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.44    inference(negated_conjecture,[],[f6])).
% 0.22/0.44  fof(f6,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k3_xboole_0(X2,X1)) = k3_xboole_0(k2_xboole_0(X0,X2),X1))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_xboole_1)).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,plain,(
% 0.22/0.44    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.22/0.44    inference(ennf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X1,X0),k3_xboole_0(X0,X2))) )),
% 0.22/0.44    inference(superposition,[],[f18,f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 0.22/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    k3_xboole_0(sK1,k2_xboole_0(sK0,sK2)) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.22/0.44    inference(superposition,[],[f19,f15])).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    k3_xboole_0(k2_xboole_0(sK0,sK2),sK1) != k2_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.22/0.44    inference(backward_demodulation,[],[f13,f15])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    k2_xboole_0(sK0,k3_xboole_0(sK2,sK1)) != k3_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 0.22/0.44    inference(cnf_transformation,[],[f11])).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (19693)------------------------------
% 0.22/0.44  % (19693)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (19693)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (19693)Memory used [KB]: 10746
% 0.22/0.44  % (19693)Time elapsed: 0.031 s
% 0.22/0.44  % (19693)------------------------------
% 0.22/0.44  % (19693)------------------------------
% 0.22/0.44  % (19692)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.44  % (19680)Success in time 0.079 s
%------------------------------------------------------------------------------
