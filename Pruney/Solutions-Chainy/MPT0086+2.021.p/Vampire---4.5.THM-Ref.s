%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:26 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   53 (  79 expanded)
%              Number of leaves         :   12 (  24 expanded)
%              Depth                    :   14
%              Number of atoms          :  111 ( 147 expanded)
%              Number of equality atoms :   25 (  53 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f974,plain,(
    $false ),
    inference(resolution,[],[f924,f24])).

fof(f24,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).

fof(f17,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f924,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X1,X0),X0) ),
    inference(subsumption_resolution,[],[f889,f153])).

fof(f153,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f36,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f81,f25])).

fof(f25,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f81,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(resolution,[],[f40,f62])).

fof(f62,plain,(
    ! [X2] : r1_xboole_0(X2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f58,f25])).

fof(f58,plain,(
    ! [X2] : r1_xboole_0(X2,k4_xboole_0(k1_xboole_0,k1_xboole_0)) ),
    inference(resolution,[],[f55,f49])).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ r1_xboole_0(X2,k1_xboole_0)
      | r1_xboole_0(X3,k4_xboole_0(X2,X2)) ) ),
    inference(resolution,[],[f47,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK3(X0,X1),X1)
          & r2_hidden(sK3(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f21])).

fof(f21,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK3(X0,X1),X1)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k4_xboole_0(X0,X0))
      | ~ r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f37,f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f19])).

fof(f19,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f55,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f54])).

fof(f54,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f53,f25])).

fof(f53,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(X0,X0)
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f39,f25])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f27])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f27])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f889,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0)))
      | r1_xboole_0(k4_xboole_0(X1,X0),X0) ) ),
    inference(superposition,[],[f164,f43])).

fof(f43,plain,(
    ! [X2] : k2_xboole_0(X2,X2) = X2 ),
    inference(resolution,[],[f33,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f26,f25])).

fof(f26,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f164,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4))))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(forward_demodulation,[],[f155,f36])).

fof(f155,plain,(
    ! [X4,X2,X3] :
      ( k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4)))
      | r1_xboole_0(k4_xboole_0(X2,X3),X4) ) ),
    inference(superposition,[],[f39,f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:51:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (6077)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (6075)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (6085)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (6078)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (6084)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (6087)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (6076)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (6086)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (6083)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (6083)Refutation not found, incomplete strategy% (6083)------------------------------
% 0.21/0.49  % (6083)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (6083)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (6083)Memory used [KB]: 10490
% 0.21/0.49  % (6083)Time elapsed: 0.076 s
% 0.21/0.49  % (6083)------------------------------
% 0.21/0.49  % (6083)------------------------------
% 0.21/0.49  % (6073)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (6080)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (6072)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (6074)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (6084)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f974,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(resolution,[],[f924,f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1) => ~r1_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f13,plain,(
% 0.21/0.50    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,negated_conjecture,(
% 0.21/0.50    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.50    inference(negated_conjecture,[],[f9])).
% 0.21/0.50  fof(f9,conjecture,(
% 0.21/0.50    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.21/0.50  fof(f924,plain,(
% 0.21/0.50    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f889,f153])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 0.21/0.50    inference(superposition,[],[f36,f84])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f81,f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.51    inference(resolution,[],[f40,f62])).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    ( ! [X2] : (r1_xboole_0(X2,k1_xboole_0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f58,f25])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X2] : (r1_xboole_0(X2,k4_xboole_0(k1_xboole_0,k1_xboole_0))) )),
% 0.21/0.51    inference(resolution,[],[f55,f49])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    ( ! [X2,X3] : (~r1_xboole_0(X2,k1_xboole_0) | r1_xboole_0(X3,k4_xboole_0(X2,X2))) )),
% 0.21/0.51    inference(resolution,[],[f47,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f15,f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK3(X0,X1),X1) & r2_hidden(sK3(X0,X1),X0)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k4_xboole_0(X0,X0)) | ~r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f37,f25])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f29,f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f14,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(rectify,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.21/0.51    inference(superposition,[],[f53,f25])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,X0) | r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.51    inference(superposition,[],[f39,f25])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(definition_unfolding,[],[f35,f27])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.51    inference(nnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f34,f27])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.51  fof(f889,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X1,k2_xboole_0(X0,k4_xboole_0(X1,X0))) | r1_xboole_0(k4_xboole_0(X1,X0),X0)) )),
% 0.21/0.51    inference(superposition,[],[f164,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X2] : (k2_xboole_0(X2,X2) = X2) )),
% 0.21/0.51    inference(resolution,[],[f33,f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.51    inference(superposition,[],[f26,f25])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.21/0.51  fof(f164,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(X2,k2_xboole_0(X3,k4_xboole_0(X2,k2_xboole_0(X3,X4)))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f155,f36])).
% 0.21/0.51  fof(f155,plain,(
% 0.21/0.51    ( ! [X4,X2,X3] : (k1_xboole_0 != k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k2_xboole_0(X3,X4))) | r1_xboole_0(k4_xboole_0(X2,X3),X4)) )),
% 0.21/0.51    inference(superposition,[],[f39,f36])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (6084)------------------------------
% 0.21/0.51  % (6084)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (6084)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (6084)Memory used [KB]: 2046
% 0.21/0.51  % (6084)Time elapsed: 0.076 s
% 0.21/0.51  % (6084)------------------------------
% 0.21/0.51  % (6084)------------------------------
% 0.21/0.51  % (6071)Success in time 0.146 s
%------------------------------------------------------------------------------
