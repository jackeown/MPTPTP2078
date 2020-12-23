%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:41 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 289 expanded)
%              Number of leaves         :   12 (  89 expanded)
%              Depth                    :   17
%              Number of atoms          :  123 ( 627 expanded)
%              Number of equality atoms :   94 ( 470 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f119,plain,(
    $false ),
    inference(subsumption_resolution,[],[f107,f118])).

fof(f118,plain,(
    ! [X0,X1] : k4_tarski(X0,X1) != X1 ),
    inference(forward_demodulation,[],[f117,f80])).

fof(f80,plain,(
    ! [X0] : sK3(k1_tarski(X0)) = X0 ),
    inference(subsumption_resolution,[],[f78,f68])).

fof(f68,plain,(
    ! [X1] : k1_xboole_0 != k1_tarski(X1) ),
    inference(backward_demodulation,[],[f48,f66])).

fof(f66,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f64,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f64,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f39,f61])).

fof(f61,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f59,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f59,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f38,f29])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X1] : k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1)) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
        | X0 = X1 )
      & ( X0 != X1
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f78,plain,(
    ! [X0] :
      ( sK3(k1_tarski(X0)) = X0
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(resolution,[],[f76,f32])).

fof(f32,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( ! [X2,X3] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).

fof(f23,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X3,X2] :
            ( k4_tarski(X2,X3) != sK3(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK3(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3] :
              ( k4_tarski(X2,X3) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3] :
                  ~ ( k4_tarski(X2,X3) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(trivial_inequality_removal,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) != k1_tarski(X0)
      | ~ r2_hidden(X1,k1_tarski(X0))
      | X0 = X1 ) ),
    inference(superposition,[],[f42,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f117,plain,(
    ! [X0,X1] : k4_tarski(X0,sK3(k1_tarski(X1))) != X1 ),
    inference(subsumption_resolution,[],[f114,f68])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k4_tarski(X0,sK3(k1_tarski(X1))) != X1
      | k1_xboole_0 = k1_tarski(X1) ) ),
    inference(resolution,[],[f113,f32])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k1_tarski(X0))
      | k4_tarski(X1,X2) != X0 ) ),
    inference(subsumption_resolution,[],[f112,f68])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k4_tarski(X1,X2) != X0
      | ~ r2_hidden(X2,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f34,f80])).

fof(f34,plain,(
    ! [X2,X0,X3] :
      ( k4_tarski(X2,X3) != sK3(X0)
      | ~ r2_hidden(X3,X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f107,plain,(
    sK0 = k4_tarski(sK1,sK0) ),
    inference(backward_demodulation,[],[f27,f106])).

fof(f106,plain,(
    sK0 = sK2 ),
    inference(backward_demodulation,[],[f51,f105])).

fof(f105,plain,(
    sK0 = k2_mcart_1(sK0) ),
    inference(subsumption_resolution,[],[f50,f101])).

fof(f101,plain,(
    sK0 != sK1 ),
    inference(superposition,[],[f100,f27])).

fof(f100,plain,(
    ! [X6,X5] : k4_tarski(X5,X6) != X5 ),
    inference(forward_demodulation,[],[f99,f80])).

fof(f99,plain,(
    ! [X6,X5] : k4_tarski(X5,X6) != sK3(k1_tarski(X5)) ),
    inference(subsumption_resolution,[],[f97,f68])).

fof(f97,plain,(
    ! [X6,X5] :
      ( k4_tarski(X5,X6) != sK3(k1_tarski(X5))
      | k1_xboole_0 = k1_tarski(X5) ) ),
    inference(resolution,[],[f33,f82])).

fof(f82,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(subsumption_resolution,[],[f81,f68])).

fof(f81,plain,(
    ! [X0] :
      ( r2_hidden(X0,k1_tarski(X0))
      | k1_xboole_0 = k1_tarski(X0) ) ),
    inference(superposition,[],[f32,f80])).

fof(f33,plain,(
    ! [X2,X0,X3] :
      ( ~ r2_hidden(X2,X0)
      | k4_tarski(X2,X3) != sK3(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f50,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = sK1 ),
    inference(backward_demodulation,[],[f28,f49])).

fof(f49,plain,(
    k1_mcart_1(sK0) = sK1 ),
    inference(superposition,[],[f40,f27])).

fof(f40,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f28,plain,
    ( sK0 = k2_mcart_1(sK0)
    | sK0 = k1_mcart_1(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ( sK0 = k2_mcart_1(sK0)
      | sK0 = k1_mcart_1(sK0) )
    & sK0 = k4_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ( k2_mcart_1(X0) = X0
          | k1_mcart_1(X0) = X0 )
        & ? [X1,X2] : k4_tarski(X1,X2) = X0 )
   => ( ( sK0 = k2_mcart_1(sK0)
        | sK0 = k1_mcart_1(sK0) )
      & ? [X2,X1] : k4_tarski(X1,X2) = sK0 ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X2,X1] : k4_tarski(X1,X2) = sK0
   => sK0 = k4_tarski(sK1,sK2) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( ( k2_mcart_1(X0) = X0
        | k1_mcart_1(X0) = X0 )
      & ? [X1,X2] : k4_tarski(X1,X2) = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ? [X1,X2] : k4_tarski(X1,X2) = X0
       => ( k2_mcart_1(X0) != X0
          & k1_mcart_1(X0) != X0 ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ? [X1,X2] : k4_tarski(X1,X2) = X0
     => ( k2_mcart_1(X0) != X0
        & k1_mcart_1(X0) != X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

fof(f51,plain,(
    k2_mcart_1(sK0) = sK2 ),
    inference(superposition,[],[f41,f27])).

fof(f41,plain,(
    ! [X0,X1] : k2_mcart_1(k4_tarski(X0,X1)) = X1 ),
    inference(cnf_transformation,[],[f13])).

fof(f27,plain,(
    sK0 = k4_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:54:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.48  % (25865)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.49  % (25881)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.50  % (25865)Refutation not found, incomplete strategy% (25865)------------------------------
% 0.22/0.50  % (25865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25865)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25865)Memory used [KB]: 6268
% 0.22/0.50  % (25865)Time elapsed: 0.079 s
% 0.22/0.50  % (25865)------------------------------
% 0.22/0.50  % (25865)------------------------------
% 0.22/0.50  % (25881)Refutation not found, incomplete strategy% (25881)------------------------------
% 0.22/0.50  % (25881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (25881)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (25881)Memory used [KB]: 10746
% 0.22/0.50  % (25881)Time elapsed: 0.092 s
% 0.22/0.50  % (25881)------------------------------
% 0.22/0.50  % (25881)------------------------------
% 0.22/0.51  % (25868)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.22/0.51  % (25869)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.51  % (25868)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f119,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f107,f118])).
% 0.22/0.51  fof(f118,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_tarski(X0,X1) != X1) )),
% 0.22/0.51    inference(forward_demodulation,[],[f117,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    ( ! [X0] : (sK3(k1_tarski(X0)) = X0) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f78,f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X1] : (k1_xboole_0 != k1_tarski(X1)) )),
% 0.22/0.51    inference(backward_demodulation,[],[f48,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f64,f29])).
% 0.22/0.51  fof(f29,plain,(
% 0.22/0.51    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f3])).
% 0.22/0.51  fof(f3,axiom,(
% 0.22/0.51    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.22/0.51    inference(superposition,[],[f39,f61])).
% 0.22/0.51  fof(f61,plain,(
% 0.22/0.51    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(forward_demodulation,[],[f59,f30])).
% 0.22/0.51  fof(f30,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.51  fof(f5,axiom,(
% 0.22/0.51    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.22/0.51  fof(f59,plain,(
% 0.22/0.51    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 0.22/0.51    inference(superposition,[],[f38,f29])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.51  fof(f39,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.51  fof(f48,plain,(
% 0.22/0.51    ( ! [X1] : (k1_tarski(X1) != k4_xboole_0(k1_tarski(X1),k1_tarski(X1))) )),
% 0.22/0.51    inference(equality_resolution,[],[f44])).
% 0.22/0.51  fof(f44,plain,(
% 0.22/0.51    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f26,plain,(
% 0.22/0.51    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) & (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))))),
% 0.22/0.51    inference(nnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    ( ! [X0] : (sK3(k1_tarski(X0)) = X0 | k1_xboole_0 = k1_tarski(X0)) )),
% 0.22/0.51    inference(resolution,[],[f76,f32])).
% 0.22/0.51  fof(f32,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : ((! [X2,X3] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f19,f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X3,X2] : (k4_tarski(X2,X3) != sK3(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK3(X0),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0] : (? [X1] : (! [X2,X3] : (k4_tarski(X2,X3) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f14])).
% 0.22/0.51  fof(f14,axiom,(
% 0.22/0.51    ! [X0] : ~(! [X1] : ~(! [X2,X3] : ~(k4_tarski(X2,X3) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_mcart_1)).
% 0.22/0.51  fof(f76,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_tarski(X0) != k1_tarski(X0) | ~r2_hidden(X1,k1_tarski(X0)) | X0 = X1) )),
% 0.22/0.51    inference(superposition,[],[f42,f45])).
% 0.22/0.51  fof(f45,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f26])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f25])).
% 0.22/0.51  fof(f25,plain,(
% 0.22/0.51    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f11])).
% 0.22/0.51  fof(f11,axiom,(
% 0.22/0.51    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.22/0.51  fof(f117,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_tarski(X0,sK3(k1_tarski(X1))) != X1) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f114,f68])).
% 0.22/0.51  fof(f114,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k4_tarski(X0,sK3(k1_tarski(X1))) != X1 | k1_xboole_0 = k1_tarski(X1)) )),
% 0.22/0.51    inference(resolution,[],[f113,f32])).
% 0.22/0.51  fof(f113,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (~r2_hidden(X2,k1_tarski(X0)) | k4_tarski(X1,X2) != X0) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f112,f68])).
% 0.22/0.51  fof(f112,plain,(
% 0.22/0.51    ( ! [X2,X0,X1] : (k4_tarski(X1,X2) != X0 | ~r2_hidden(X2,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.22/0.51    inference(superposition,[],[f34,f80])).
% 0.22/0.51  fof(f34,plain,(
% 0.22/0.51    ( ! [X2,X0,X3] : (k4_tarski(X2,X3) != sK3(X0) | ~r2_hidden(X3,X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f107,plain,(
% 0.22/0.51    sK0 = k4_tarski(sK1,sK0)),
% 0.22/0.51    inference(backward_demodulation,[],[f27,f106])).
% 0.22/0.51  fof(f106,plain,(
% 0.22/0.51    sK0 = sK2),
% 0.22/0.51    inference(backward_demodulation,[],[f51,f105])).
% 0.22/0.51  fof(f105,plain,(
% 0.22/0.51    sK0 = k2_mcart_1(sK0)),
% 0.22/0.51    inference(subsumption_resolution,[],[f50,f101])).
% 0.22/0.51  fof(f101,plain,(
% 0.22/0.51    sK0 != sK1),
% 0.22/0.51    inference(superposition,[],[f100,f27])).
% 0.22/0.51  fof(f100,plain,(
% 0.22/0.51    ( ! [X6,X5] : (k4_tarski(X5,X6) != X5) )),
% 0.22/0.51    inference(forward_demodulation,[],[f99,f80])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    ( ! [X6,X5] : (k4_tarski(X5,X6) != sK3(k1_tarski(X5))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f97,f68])).
% 0.22/0.51  fof(f97,plain,(
% 0.22/0.51    ( ! [X6,X5] : (k4_tarski(X5,X6) != sK3(k1_tarski(X5)) | k1_xboole_0 = k1_tarski(X5)) )),
% 0.22/0.51    inference(resolution,[],[f33,f82])).
% 0.22/0.51  fof(f82,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0))) )),
% 0.22/0.51    inference(subsumption_resolution,[],[f81,f68])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0] : (r2_hidden(X0,k1_tarski(X0)) | k1_xboole_0 = k1_tarski(X0)) )),
% 0.22/0.51    inference(superposition,[],[f32,f80])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X2,X0,X3] : (~r2_hidden(X2,X0) | k4_tarski(X2,X3) != sK3(X0) | k1_xboole_0 = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f24])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    sK0 = k2_mcart_1(sK0) | sK0 = sK1),
% 0.22/0.51    inference(backward_demodulation,[],[f28,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    k1_mcart_1(sK0) = sK1),
% 0.22/0.51    inference(superposition,[],[f40,f27])).
% 0.22/0.51  fof(f40,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f13,axiom,(
% 0.22/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  fof(f22,plain,(
% 0.22/0.51    (sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & sK0 = k4_tarski(sK1,sK2)),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f21,f20])).
% 0.22/0.51  fof(f20,plain,(
% 0.22/0.51    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0) => ((sK0 = k2_mcart_1(sK0) | sK0 = k1_mcart_1(sK0)) & ? [X2,X1] : k4_tarski(X1,X2) = sK0)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ? [X2,X1] : k4_tarski(X1,X2) = sK0 => sK0 = k4_tarski(sK1,sK2)),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ? [X0] : ((k2_mcart_1(X0) = X0 | k1_mcart_1(X0) = X0) & ? [X1,X2] : k4_tarski(X1,X2) = X0)),
% 0.22/0.51    inference(ennf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,negated_conjecture,(
% 0.22/0.51    ~! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.51    inference(negated_conjecture,[],[f15])).
% 0.22/0.51  fof(f15,conjecture,(
% 0.22/0.51    ! [X0] : (? [X1,X2] : k4_tarski(X1,X2) = X0 => (k2_mcart_1(X0) != X0 & k1_mcart_1(X0) != X0))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).
% 0.22/0.51  fof(f51,plain,(
% 0.22/0.51    k2_mcart_1(sK0) = sK2),
% 0.22/0.51    inference(superposition,[],[f41,f27])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f13])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    sK0 = k4_tarski(sK1,sK2)),
% 0.22/0.51    inference(cnf_transformation,[],[f22])).
% 0.22/0.51  % SZS output end Proof for theBenchmark
% 0.22/0.51  % (25868)------------------------------
% 0.22/0.51  % (25868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (25868)Termination reason: Refutation
% 0.22/0.51  
% 0.22/0.51  % (25868)Memory used [KB]: 6268
% 0.22/0.51  % (25868)Time elapsed: 0.097 s
% 0.22/0.51  % (25868)------------------------------
% 0.22/0.51  % (25868)------------------------------
% 0.22/0.52  % (25867)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (25876)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.52  % (25876)Refutation not found, incomplete strategy% (25876)------------------------------
% 0.22/0.52  % (25876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25876)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25876)Memory used [KB]: 6140
% 0.22/0.52  % (25876)Time elapsed: 0.002 s
% 0.22/0.52  % (25876)------------------------------
% 0.22/0.52  % (25876)------------------------------
% 0.22/0.52  % (25884)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.52  % (25884)Refutation not found, incomplete strategy% (25884)------------------------------
% 0.22/0.52  % (25884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (25884)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (25884)Memory used [KB]: 1663
% 0.22/0.52  % (25884)Time elapsed: 0.106 s
% 0.22/0.52  % (25884)------------------------------
% 0.22/0.52  % (25884)------------------------------
% 0.22/0.52  % (25877)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.52  % (25875)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.53  % (25860)Success in time 0.159 s
%------------------------------------------------------------------------------
