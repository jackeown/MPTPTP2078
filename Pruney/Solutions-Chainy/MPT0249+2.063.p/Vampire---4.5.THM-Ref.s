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
% DateTime   : Thu Dec  3 12:38:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   30 (  84 expanded)
%              Number of leaves         :    4 (  23 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 320 expanded)
%              Number of equality atoms :   82 ( 298 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f37,plain,(
    $false ),
    inference(subsumption_resolution,[],[f29,f36])).

fof(f36,plain,(
    ! [X0] : k1_tarski(X0) != sK3 ),
    inference(subsumption_resolution,[],[f35,f14])).

fof(f14,plain,(
    sK2 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( k1_xboole_0 != sK3
    & k1_xboole_0 != sK2
    & sK2 != sK3
    & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f5,f9])).

fof(f9,plain,
    ( ? [X0,X1,X2] :
        ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( k1_xboole_0 != sK3
      & k1_xboole_0 != sK2
      & sK2 != sK3
      & k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f5,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f35,plain,(
    ! [X0] :
      ( k1_tarski(X0) != sK3
      | sK2 = sK3 ) ),
    inference(inner_rewriting,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k1_tarski(X0) != sK3
      | k1_tarski(X0) = sK2 ) ),
    inference(subsumption_resolution,[],[f33,f15])).

fof(f15,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0] :
      ( k1_tarski(X0) != sK3
      | k1_xboole_0 = sK2
      | k1_tarski(X0) = sK2 ) ),
    inference(superposition,[],[f26,f31])).

fof(f31,plain,(
    sK3 = k2_xboole_0(sK2,sK3) ),
    inference(backward_demodulation,[],[f13,f29])).

fof(f13,plain,(
    k1_tarski(sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f10])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_xboole_0 = X1
      | k1_tarski(X0) = X1 ) ),
    inference(subsumption_resolution,[],[f20,f18])).

fof(f18,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_tarski(X1) = X2 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ( k1_tarski(X1) = X0
        & k1_tarski(X1) = X2 )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f11])).

fof(f11,plain,(
    ! [X2,X0,X1] :
      ( ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | ~ sP0(X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,plain,(
    ! [X2,X0,X1] :
      ( ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | ~ sP0(X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f20,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) = X1
      | k1_xboole_0 = X1
      | sP0(X2,X0,X1)
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | sP0(X2,X0,X1)
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(definition_folding,[],[f6,f7])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 = X2
        & k1_tarski(X0) = X1 )
      | ( k1_tarski(X0) = X2
        & k1_xboole_0 = X1 )
      | ( k1_tarski(X0) = X2
        & k1_tarski(X0) = X1 )
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f29,plain,(
    sK3 = k1_tarski(sK1) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK1)
      | k1_tarski(X0) = sK3 ) ),
    inference(subsumption_resolution,[],[f27,f16])).

fof(f16,plain,(
    k1_xboole_0 != sK3 ),
    inference(cnf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( k1_tarski(X0) != k1_tarski(sK1)
      | k1_tarski(X0) = sK3
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f24,f13])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( k1_tarski(X0) != k2_xboole_0(X1,X2)
      | k1_tarski(X0) = X2
      | k1_xboole_0 = X2 ) ),
    inference(subsumption_resolution,[],[f23,f19])).

fof(f19,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | k1_tarski(X0) = X2
      | sP0(X2,X0,X1)
      | k1_tarski(X0) != k2_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f8])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:17:42 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (5600)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (5592)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (5580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (5592)Refutation not found, incomplete strategy% (5592)------------------------------
% 0.21/0.51  % (5592)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5592)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (5592)Memory used [KB]: 6140
% 0.21/0.51  % (5592)Time elapsed: 0.056 s
% 0.21/0.51  % (5592)------------------------------
% 0.21/0.51  % (5592)------------------------------
% 0.21/0.51  % (5583)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (5583)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(subsumption_resolution,[],[f29,f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) != sK3) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f35,f14])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    sK2 != sK3),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & sK2 != sK3 & k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f5,f9])).
% 0.21/0.51  fof(f9,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2)) => (k1_xboole_0 != sK3 & k1_xboole_0 != sK2 & sK2 != sK3 & k1_tarski(sK1) = k2_xboole_0(sK2,sK3))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f5,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.51    inference(negated_conjecture,[],[f3])).
% 0.21/0.51  fof(f3,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) != sK3 | sK2 = sK3) )),
% 0.21/0.51    inference(inner_rewriting,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) != sK3 | k1_tarski(X0) = sK2) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f33,f15])).
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    k1_xboole_0 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) != sK3 | k1_xboole_0 = sK2 | k1_tarski(X0) = sK2) )),
% 0.21/0.51    inference(superposition,[],[f26,f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    sK3 = k2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(backward_demodulation,[],[f13,f29])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    k1_tarski(sK1) = k2_xboole_0(sK2,sK3)),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_xboole_0 = X1 | k1_tarski(X0) = X1) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f20,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_tarski(X1) = X2) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k1_tarski(X1) = X0 & k1_tarski(X1) = X2) | ~sP0(X0,X1,X2))),
% 0.21/0.51    inference(rectify,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X2,X0,X1] : ((k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | ~sP0(X2,X0,X1))),
% 0.21/0.51    inference(nnf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,plain,(
% 0.21/0.51    ! [X2,X0,X1] : ((k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | ~sP0(X2,X0,X1))),
% 0.21/0.51    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_tarski(X0) = X1 | k1_xboole_0 = X1 | sP0(X2,X0,X1) | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | sP0(X2,X0,X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.21/0.51    inference(definition_folding,[],[f6,f7])).
% 0.21/0.51  fof(f6,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k1_xboole_0 = X2 & k1_tarski(X0) = X1) | (k1_tarski(X0) = X2 & k1_xboole_0 = X1) | (k1_tarski(X0) = X2 & k1_tarski(X0) = X1) | k1_tarski(X0) != k2_xboole_0(X1,X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    sK3 = k1_tarski(sK1)),
% 0.21/0.51    inference(equality_resolution,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK1) | k1_tarski(X0) = sK3) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f27,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    k1_xboole_0 != sK3),
% 0.21/0.51    inference(cnf_transformation,[],[f10])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X0] : (k1_tarski(X0) != k1_tarski(sK1) | k1_tarski(X0) = sK3 | k1_xboole_0 = sK3) )),
% 0.21/0.51    inference(superposition,[],[f24,f13])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_tarski(X0) != k2_xboole_0(X1,X2) | k1_tarski(X0) = X2 | k1_xboole_0 = X2) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f23,f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | k1_tarski(X1) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f12])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | k1_tarski(X0) = X2 | sP0(X2,X0,X1) | k1_tarski(X0) != k2_xboole_0(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f8])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (5583)------------------------------
% 0.21/0.51  % (5583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (5583)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (5583)Memory used [KB]: 6140
% 0.21/0.51  % (5583)Time elapsed: 0.069 s
% 0.21/0.51  % (5583)------------------------------
% 0.21/0.51  % (5583)------------------------------
% 0.21/0.52  % (5573)Success in time 0.155 s
%------------------------------------------------------------------------------
