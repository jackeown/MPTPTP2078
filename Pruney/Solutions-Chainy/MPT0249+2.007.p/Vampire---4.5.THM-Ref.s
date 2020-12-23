%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:11 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 181 expanded)
%              Number of leaves         :    5 (  49 expanded)
%              Depth                    :   20
%              Number of atoms          :   97 ( 639 expanded)
%              Number of equality atoms :   66 ( 544 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f71,plain,(
    $false ),
    inference(subsumption_resolution,[],[f70,f14])).

fof(f14,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,
    ( k1_xboole_0 != sK2
    & k1_xboole_0 != sK1
    & sK1 != sK2
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).

fof(f7,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK2
      & k1_xboole_0 != sK1
      & sK1 != sK2
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f6,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f70,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f67,f12])).

fof(f12,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f8])).

fof(f67,plain,
    ( sK1 = sK2
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f65,f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK1)
      | sK1 = X0
      | k1_xboole_0 = X0 ) ),
    inference(superposition,[],[f15,f25])).

fof(f25,plain,(
    sK1 = k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f23,f13])).

fof(f13,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f8])).

fof(f23,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f22,f15])).

fof(f22,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f19,f11])).

fof(f11,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f19,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f15,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f65,plain,(
    r1_tarski(sK2,sK1) ),
    inference(subsumption_resolution,[],[f64,f12])).

fof(f64,plain,
    ( r1_tarski(sK2,sK1)
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f63,f13])).

fof(f63,plain,
    ( r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1
    | sK1 = sK2 ),
    inference(subsumption_resolution,[],[f62,f26])).

fof(f26,plain,(
    r1_tarski(sK1,sK1) ),
    inference(backward_demodulation,[],[f22,f25])).

fof(f62,plain,
    ( ~ r1_tarski(sK1,sK1)
    | r1_tarski(sK2,sK1)
    | k1_xboole_0 = sK1
    | sK1 = sK2 ),
    inference(superposition,[],[f57,f27])).

fof(f27,plain,(
    sK1 = k2_xboole_0(sK1,sK2) ),
    inference(backward_demodulation,[],[f11,f25])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X1,X0),sK1)
      | r1_tarski(X0,sK1)
      | k2_xboole_0(X1,X0) = k1_xboole_0
      | k2_xboole_0(X1,X0) = X0 ) ),
    inference(superposition,[],[f56,f18])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f56,plain,(
    ! [X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),sK1)
      | r1_tarski(X4,sK1)
      | k1_xboole_0 = k2_xboole_0(X4,X5)
      | k2_xboole_0(X4,X5) = X4 ) ),
    inference(superposition,[],[f47,f25])).

fof(f47,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X4,X5),k1_tarski(X6))
      | r1_tarski(X4,sK1)
      | k1_xboole_0 = k2_xboole_0(X4,X5)
      | k2_xboole_0(X4,X5) = X4 ) ),
    inference(resolution,[],[f43,f19])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,X1)
      | X1 = X2
      | r1_tarski(X2,sK1)
      | k1_xboole_0 = X1
      | ~ r1_tarski(X1,k1_tarski(X0)) ) ),
    inference(superposition,[],[f34,f15])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_tarski(X1) = X0
      | r1_tarski(X0,sK1) ) ),
    inference(superposition,[],[f31,f15])).

fof(f31,plain,(
    r1_tarski(k1_xboole_0,sK1) ),
    inference(superposition,[],[f21,f25])).

fof(f21,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,k1_tarski(X1)) ),
    inference(equality_resolution,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:35:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (905)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.46  % (905)Refutation not found, incomplete strategy% (905)------------------------------
% 0.22/0.46  % (905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (905)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (905)Memory used [KB]: 6140
% 0.22/0.46  % (905)Time elapsed: 0.042 s
% 0.22/0.46  % (905)------------------------------
% 0.22/0.46  % (905)------------------------------
% 0.22/0.47  % (921)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.47  % (921)Refutation not found, incomplete strategy% (921)------------------------------
% 0.22/0.47  % (921)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (921)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (921)Memory used [KB]: 6140
% 0.22/0.47  % (921)Time elapsed: 0.060 s
% 0.22/0.47  % (921)------------------------------
% 0.22/0.47  % (921)------------------------------
% 0.22/0.48  % (919)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (919)Refutation not found, incomplete strategy% (919)------------------------------
% 0.22/0.48  % (919)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (919)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (919)Memory used [KB]: 1535
% 0.22/0.48  % (919)Time elapsed: 0.060 s
% 0.22/0.48  % (919)------------------------------
% 0.22/0.48  % (919)------------------------------
% 0.22/0.48  % (926)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (926)Refutation not found, incomplete strategy% (926)------------------------------
% 0.22/0.48  % (926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (926)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (926)Memory used [KB]: 10490
% 0.22/0.48  % (926)Time elapsed: 0.063 s
% 0.22/0.48  % (926)------------------------------
% 0.22/0.48  % (926)------------------------------
% 0.22/0.48  % (925)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (906)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (925)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(subsumption_resolution,[],[f70,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    k1_xboole_0 != sK2),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,plain,(
% 0.22/0.48    k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f6,f7])).
% 0.22/0.48  fof(f7,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK2 & k1_xboole_0 != sK1 & sK1 != sK2 & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f6,plain,(
% 0.22/0.48    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.48    inference(negated_conjecture,[],[f4])).
% 0.22/0.48  fof(f4,conjecture,(
% 0.22/0.48    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    k1_xboole_0 = sK2),
% 0.22/0.48    inference(subsumption_resolution,[],[f67,f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    sK1 != sK2),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f67,plain,(
% 0.22/0.48    sK1 = sK2 | k1_xboole_0 = sK2),
% 0.22/0.48    inference(resolution,[],[f65,f29])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    ( ! [X0] : (~r1_tarski(X0,sK1) | sK1 = X0 | k1_xboole_0 = X0) )),
% 0.22/0.48    inference(superposition,[],[f15,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    sK1 = k1_tarski(sK0)),
% 0.22/0.48    inference(subsumption_resolution,[],[f23,f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    k1_xboole_0 != sK1),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 0.22/0.48    inference(resolution,[],[f22,f15])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    r1_tarski(sK1,k1_tarski(sK0))),
% 0.22/0.48    inference(superposition,[],[f19,f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 0.22/0.48    inference(cnf_transformation,[],[f8])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.48    inference(flattening,[],[f9])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 0.22/0.48    inference(nnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 0.22/0.48  fof(f65,plain,(
% 0.22/0.48    r1_tarski(sK2,sK1)),
% 0.22/0.48    inference(subsumption_resolution,[],[f64,f12])).
% 0.22/0.48  fof(f64,plain,(
% 0.22/0.48    r1_tarski(sK2,sK1) | sK1 = sK2),
% 0.22/0.48    inference(subsumption_resolution,[],[f63,f13])).
% 0.22/0.48  fof(f63,plain,(
% 0.22/0.48    r1_tarski(sK2,sK1) | k1_xboole_0 = sK1 | sK1 = sK2),
% 0.22/0.48    inference(subsumption_resolution,[],[f62,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    r1_tarski(sK1,sK1)),
% 0.22/0.48    inference(backward_demodulation,[],[f22,f25])).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    ~r1_tarski(sK1,sK1) | r1_tarski(sK2,sK1) | k1_xboole_0 = sK1 | sK1 = sK2),
% 0.22/0.48    inference(superposition,[],[f57,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    sK1 = k2_xboole_0(sK1,sK2)),
% 0.22/0.48    inference(backward_demodulation,[],[f11,f25])).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(k2_xboole_0(X1,X0),sK1) | r1_tarski(X0,sK1) | k2_xboole_0(X1,X0) = k1_xboole_0 | k2_xboole_0(X1,X0) = X0) )),
% 0.22/0.48    inference(superposition,[],[f56,f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    ( ! [X4,X5] : (~r1_tarski(k2_xboole_0(X4,X5),sK1) | r1_tarski(X4,sK1) | k1_xboole_0 = k2_xboole_0(X4,X5) | k2_xboole_0(X4,X5) = X4) )),
% 0.22/0.48    inference(superposition,[],[f47,f25])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ( ! [X6,X4,X5] : (~r1_tarski(k2_xboole_0(X4,X5),k1_tarski(X6)) | r1_tarski(X4,sK1) | k1_xboole_0 = k2_xboole_0(X4,X5) | k2_xboole_0(X4,X5) = X4) )),
% 0.22/0.48    inference(resolution,[],[f43,f19])).
% 0.22/0.48  fof(f43,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~r1_tarski(X2,X1) | X1 = X2 | r1_tarski(X2,sK1) | k1_xboole_0 = X1 | ~r1_tarski(X1,k1_tarski(X0))) )),
% 0.22/0.48    inference(superposition,[],[f34,f15])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_tarski(X1) = X0 | r1_tarski(X0,sK1)) )),
% 0.22/0.48    inference(superposition,[],[f31,f15])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    r1_tarski(k1_xboole_0,sK1)),
% 0.22/0.48    inference(superposition,[],[f21,f25])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X1] : (r1_tarski(k1_xboole_0,k1_tarski(X1))) )),
% 0.22/0.48    inference(equality_resolution,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 != X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (925)------------------------------
% 0.22/0.48  % (925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (925)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (925)Memory used [KB]: 6140
% 0.22/0.48  % (925)Time elapsed: 0.066 s
% 0.22/0.48  % (925)------------------------------
% 0.22/0.48  % (925)------------------------------
% 0.22/0.48  % (904)Success in time 0.112 s
%------------------------------------------------------------------------------
