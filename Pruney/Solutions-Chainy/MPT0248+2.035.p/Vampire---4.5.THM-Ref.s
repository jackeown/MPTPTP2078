%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:54 EST 2020

% Result     : Theorem 1.18s
% Output     : Refutation 1.18s
% Verified   : 
% Statistics : Number of formulae       :   38 ( 314 expanded)
%              Number of leaves         :    7 (  88 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 (1512 expanded)
%              Number of equality atoms :   83 (1374 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(subsumption_resolution,[],[f116,f114])).

fof(f114,plain,(
    k1_xboole_0 != k1_tarski(sK0) ),
    inference(backward_demodulation,[],[f105,f111])).

fof(f111,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f95,f105])).

fof(f95,plain,
    ( k1_xboole_0 = sK2
    | sK2 = k1_tarski(sK0) ),
    inference(resolution,[],[f29,f40])).

fof(f40,plain,(
    r1_tarski(sK2,k1_tarski(sK0)) ),
    inference(superposition,[],[f38,f18])).

fof(f18,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( ( k1_xboole_0 != sK2
      | sK1 != k1_tarski(sK0) )
    & ( sK2 != k1_tarski(sK0)
      | k1_xboole_0 != sK1 )
    & ( sK2 != k1_tarski(sK0)
      | sK1 != k1_tarski(sK0) )
    & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( ( k1_xboole_0 != X2
          | k1_tarski(X0) != X1 )
        & ( k1_tarski(X0) != X2
          | k1_xboole_0 != X1 )
        & ( k1_tarski(X0) != X2
          | k1_tarski(X0) != X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) )
   => ( ( k1_xboole_0 != sK2
        | sK1 != k1_tarski(sK0) )
      & ( sK2 != k1_tarski(sK0)
        | k1_xboole_0 != sK1 )
      & ( sK2 != k1_tarski(sK0)
        | sK1 != k1_tarski(sK0) )
      & k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f38,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f24,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_tarski(X1))
      | k1_xboole_0 = X0
      | k1_tarski(X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f105,plain,(
    sK2 != k1_tarski(sK0) ),
    inference(subsumption_resolution,[],[f20,f104])).

fof(f104,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f19,f94,f95,f103])).

fof(f103,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f97])).

fof(f97,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f21,f94])).

fof(f21,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f15])).

fof(f94,plain,
    ( sK1 = k1_tarski(sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f29,f37])).

fof(f37,plain,(
    r1_tarski(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f24,f18])).

fof(f19,plain,
    ( sK2 != k1_tarski(sK0)
    | sK1 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f20,plain,
    ( sK2 != k1_tarski(sK0)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f116,plain,(
    k1_xboole_0 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f115,f111])).

fof(f115,plain,(
    sK2 = k1_tarski(sK0) ),
    inference(forward_demodulation,[],[f106,f45])).

fof(f45,plain,(
    ! [X4] : k2_xboole_0(k1_xboole_0,X4) = X4 ),
    inference(resolution,[],[f28,f22])).

fof(f22,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f106,plain,(
    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2) ),
    inference(backward_demodulation,[],[f18,f104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n019.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (14891)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.51  % (14883)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.22/0.51  % (14883)Refutation not found, incomplete strategy% (14883)------------------------------
% 0.22/0.51  % (14883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.51  % (14883)Termination reason: Refutation not found, incomplete strategy
% 1.18/0.51  
% 1.18/0.51  % (14883)Memory used [KB]: 6140
% 1.18/0.51  % (14883)Time elapsed: 0.004 s
% 1.18/0.51  % (14883)------------------------------
% 1.18/0.51  % (14883)------------------------------
% 1.18/0.51  % (14875)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.18/0.52  % (14875)Refutation found. Thanks to Tanya!
% 1.18/0.52  % SZS status Theorem for theBenchmark
% 1.18/0.52  % SZS output start Proof for theBenchmark
% 1.18/0.52  fof(f117,plain,(
% 1.18/0.52    $false),
% 1.18/0.52    inference(subsumption_resolution,[],[f116,f114])).
% 1.18/0.52  fof(f114,plain,(
% 1.18/0.52    k1_xboole_0 != k1_tarski(sK0)),
% 1.18/0.52    inference(backward_demodulation,[],[f105,f111])).
% 1.18/0.52  fof(f111,plain,(
% 1.18/0.52    k1_xboole_0 = sK2),
% 1.18/0.52    inference(subsumption_resolution,[],[f95,f105])).
% 1.18/0.52  fof(f95,plain,(
% 1.18/0.52    k1_xboole_0 = sK2 | sK2 = k1_tarski(sK0)),
% 1.18/0.52    inference(resolution,[],[f29,f40])).
% 1.18/0.52  fof(f40,plain,(
% 1.18/0.52    r1_tarski(sK2,k1_tarski(sK0))),
% 1.18/0.52    inference(superposition,[],[f38,f18])).
% 1.18/0.52  fof(f18,plain,(
% 1.18/0.52    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.18/0.52    inference(cnf_transformation,[],[f15])).
% 1.18/0.52  fof(f15,plain,(
% 1.18/0.52    (k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 1.18/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f14])).
% 1.18/0.52  fof(f14,plain,(
% 1.18/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2)) => ((k1_xboole_0 != sK2 | sK1 != k1_tarski(sK0)) & (sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1) & (sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)) & k1_tarski(sK0) = k2_xboole_0(sK1,sK2))),
% 1.18/0.52    introduced(choice_axiom,[])).
% 1.18/0.52  fof(f12,plain,(
% 1.18/0.52    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.18/0.52    inference(ennf_transformation,[],[f11])).
% 1.18/0.52  fof(f11,negated_conjecture,(
% 1.18/0.52    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.18/0.52    inference(negated_conjecture,[],[f10])).
% 1.18/0.52  fof(f10,conjecture,(
% 1.18/0.52    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 1.18/0.52  fof(f38,plain,(
% 1.18/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X0))) )),
% 1.18/0.52    inference(superposition,[],[f24,f25])).
% 1.18/0.52  fof(f25,plain,(
% 1.18/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f1])).
% 1.18/0.52  fof(f1,axiom,(
% 1.18/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.18/0.52  fof(f24,plain,(
% 1.18/0.52    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.18/0.52    inference(cnf_transformation,[],[f4])).
% 1.18/0.52  fof(f4,axiom,(
% 1.18/0.52    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.18/0.52  fof(f29,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~r1_tarski(X0,k1_tarski(X1)) | k1_xboole_0 = X0 | k1_tarski(X1) = X0) )),
% 1.18/0.52    inference(cnf_transformation,[],[f17])).
% 1.18/0.52  fof(f17,plain,(
% 1.18/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.18/0.52    inference(flattening,[],[f16])).
% 1.18/0.52  fof(f16,plain,(
% 1.18/0.52    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 1.18/0.52    inference(nnf_transformation,[],[f9])).
% 1.18/0.52  fof(f9,axiom,(
% 1.18/0.52    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 1.18/0.52  fof(f105,plain,(
% 1.18/0.52    sK2 != k1_tarski(sK0)),
% 1.18/0.52    inference(subsumption_resolution,[],[f20,f104])).
% 1.18/0.52  fof(f104,plain,(
% 1.18/0.52    k1_xboole_0 = sK1),
% 1.18/0.52    inference(global_subsumption,[],[f19,f94,f95,f103])).
% 1.18/0.52  fof(f103,plain,(
% 1.18/0.52    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.18/0.52    inference(trivial_inequality_removal,[],[f97])).
% 1.18/0.52  fof(f97,plain,(
% 1.18/0.52    sK1 != sK1 | k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.18/0.52    inference(superposition,[],[f21,f94])).
% 1.18/0.52  fof(f21,plain,(
% 1.18/0.52    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 1.18/0.52    inference(cnf_transformation,[],[f15])).
% 1.18/0.52  fof(f94,plain,(
% 1.18/0.52    sK1 = k1_tarski(sK0) | k1_xboole_0 = sK1),
% 1.18/0.52    inference(resolution,[],[f29,f37])).
% 1.18/0.52  fof(f37,plain,(
% 1.18/0.52    r1_tarski(sK1,k1_tarski(sK0))),
% 1.18/0.52    inference(superposition,[],[f24,f18])).
% 1.18/0.52  fof(f19,plain,(
% 1.18/0.52    sK2 != k1_tarski(sK0) | sK1 != k1_tarski(sK0)),
% 1.18/0.52    inference(cnf_transformation,[],[f15])).
% 1.18/0.52  fof(f20,plain,(
% 1.18/0.52    sK2 != k1_tarski(sK0) | k1_xboole_0 != sK1),
% 1.18/0.52    inference(cnf_transformation,[],[f15])).
% 1.18/0.52  fof(f116,plain,(
% 1.18/0.52    k1_xboole_0 = k1_tarski(sK0)),
% 1.18/0.52    inference(forward_demodulation,[],[f115,f111])).
% 1.18/0.52  fof(f115,plain,(
% 1.18/0.52    sK2 = k1_tarski(sK0)),
% 1.18/0.52    inference(forward_demodulation,[],[f106,f45])).
% 1.18/0.52  fof(f45,plain,(
% 1.18/0.52    ( ! [X4] : (k2_xboole_0(k1_xboole_0,X4) = X4) )),
% 1.18/0.52    inference(resolution,[],[f28,f22])).
% 1.18/0.52  fof(f22,plain,(
% 1.18/0.52    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 1.18/0.52    inference(cnf_transformation,[],[f3])).
% 1.18/0.52  fof(f3,axiom,(
% 1.18/0.52    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 1.18/0.52  fof(f28,plain,(
% 1.18/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.18/0.52    inference(cnf_transformation,[],[f13])).
% 1.18/0.52  fof(f13,plain,(
% 1.18/0.52    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.18/0.52    inference(ennf_transformation,[],[f2])).
% 1.18/0.52  fof(f2,axiom,(
% 1.18/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.18/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.18/0.52  fof(f106,plain,(
% 1.18/0.52    k1_tarski(sK0) = k2_xboole_0(k1_xboole_0,sK2)),
% 1.18/0.52    inference(backward_demodulation,[],[f18,f104])).
% 1.18/0.52  % SZS output end Proof for theBenchmark
% 1.18/0.52  % (14875)------------------------------
% 1.18/0.52  % (14875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.18/0.52  % (14875)Termination reason: Refutation
% 1.18/0.52  
% 1.18/0.52  % (14875)Memory used [KB]: 6268
% 1.18/0.52  % (14875)Time elapsed: 0.063 s
% 1.18/0.52  % (14875)------------------------------
% 1.18/0.52  % (14875)------------------------------
% 1.18/0.52  % (14872)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.18/0.52  % (14867)Success in time 0.156 s
%------------------------------------------------------------------------------
