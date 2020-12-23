%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:06 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   41 (  55 expanded)
%              Number of leaves         :   10 (  16 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 120 expanded)
%              Number of equality atoms :   35 (  51 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (10319)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
fof(f445,plain,(
    $false ),
    inference(subsumption_resolution,[],[f444,f19])).

fof(f19,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f444,plain,(
    r2_hidden(sK0,sK2) ),
    inference(subsumption_resolution,[],[f443,f20])).

fof(f20,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f443,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(resolution,[],[f415,f89])).

fof(f89,plain,(
    ! [X14,X15,X16] :
      ( r1_xboole_0(k2_tarski(X14,X15),X16)
      | r2_hidden(X15,X16)
      | r2_hidden(X14,X16) ) ),
    inference(superposition,[],[f24,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
        | r2_hidden(X1,X2)
        | r2_hidden(X0,X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f24,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f415,plain,(
    ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(trivial_inequality_removal,[],[f414])).

fof(f414,plain,
    ( sK2 != sK2
    | ~ r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(superposition,[],[f21,f236])).

% (10318)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
fof(f236,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X2,X1) = X2
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f216,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f216,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X2,X1) = k4_xboole_0(X2,k1_xboole_0)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f54,f52])).

fof(f52,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k3_xboole_0(X1,X2)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(forward_demodulation,[],[f46,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f45,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f45,plain,(
    ! [X0] : k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f27,f23])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f46,plain,(
    ! [X2,X1] :
      ( k3_xboole_0(X1,X2) = k4_xboole_0(X1,X1)
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(superposition,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f54,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f28,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f21,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 14:18:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.23/0.45  % (10323)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.47  % (10316)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.48  % (10322)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.48  % (10317)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.49  % (10327)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.49  % (10315)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.49  % (10316)Refutation found. Thanks to Tanya!
% 0.23/0.49  % SZS status Theorem for theBenchmark
% 0.23/0.49  % SZS output start Proof for theBenchmark
% 0.23/0.49  % (10319)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.49  fof(f445,plain,(
% 0.23/0.49    $false),
% 0.23/0.49    inference(subsumption_resolution,[],[f444,f19])).
% 0.23/0.49  fof(f19,plain,(
% 0.23/0.49    ~r2_hidden(sK0,sK2)),
% 0.23/0.49    inference(cnf_transformation,[],[f16])).
% 0.23/0.49  fof(f16,plain,(
% 0.23/0.49    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 0.23/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f15])).
% 0.23/0.49  fof(f15,plain,(
% 0.23/0.49    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 0.23/0.49    introduced(choice_axiom,[])).
% 0.23/0.49  fof(f13,plain,(
% 0.23/0.49    ? [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.23/0.49    inference(ennf_transformation,[],[f11])).
% 0.23/0.49  fof(f11,negated_conjecture,(
% 0.23/0.49    ~! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.23/0.49    inference(negated_conjecture,[],[f10])).
% 0.23/0.49  fof(f10,conjecture,(
% 0.23/0.49    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 0.23/0.49  fof(f444,plain,(
% 0.23/0.49    r2_hidden(sK0,sK2)),
% 0.23/0.49    inference(subsumption_resolution,[],[f443,f20])).
% 0.23/0.49  fof(f20,plain,(
% 0.23/0.49    ~r2_hidden(sK1,sK2)),
% 0.23/0.49    inference(cnf_transformation,[],[f16])).
% 0.23/0.49  fof(f443,plain,(
% 0.23/0.49    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 0.23/0.49    inference(resolution,[],[f415,f89])).
% 0.23/0.49  fof(f89,plain,(
% 0.23/0.49    ( ! [X14,X15,X16] : (r1_xboole_0(k2_tarski(X14,X15),X16) | r2_hidden(X15,X16) | r2_hidden(X14,X16)) )),
% 0.23/0.49    inference(superposition,[],[f24,f32])).
% 0.23/0.49  fof(f32,plain,(
% 0.23/0.49    ( ! [X2,X0,X1] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f18])).
% 0.23/0.49  fof(f18,plain,(
% 0.23/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2) | r2_hidden(X0,X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.23/0.49    inference(flattening,[],[f17])).
% 0.23/0.49  fof(f17,plain,(
% 0.23/0.49    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) | (r2_hidden(X1,X2) | r2_hidden(X0,X2))) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.23/0.49    inference(nnf_transformation,[],[f9])).
% 0.23/0.49  fof(f9,axiom,(
% 0.23/0.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.23/0.49  fof(f24,plain,(
% 0.23/0.49    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f6])).
% 0.23/0.49  fof(f6,axiom,(
% 0.23/0.49    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.23/0.49  fof(f415,plain,(
% 0.23/0.49    ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.23/0.49    inference(trivial_inequality_removal,[],[f414])).
% 0.23/0.49  fof(f414,plain,(
% 0.23/0.49    sK2 != sK2 | ~r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.23/0.49    inference(superposition,[],[f21,f236])).
% 0.23/0.49  % (10318)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.49  fof(f236,plain,(
% 0.23/0.49    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = X2 | ~r1_xboole_0(X1,X2)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f216,f23])).
% 0.23/0.49  fof(f23,plain,(
% 0.23/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.49    inference(cnf_transformation,[],[f3])).
% 0.23/0.49  fof(f3,axiom,(
% 0.23/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.23/0.49  fof(f216,plain,(
% 0.23/0.49    ( ! [X2,X1] : (k4_xboole_0(X2,X1) = k4_xboole_0(X2,k1_xboole_0) | ~r1_xboole_0(X1,X2)) )),
% 0.23/0.49    inference(superposition,[],[f54,f52])).
% 0.23/0.49  fof(f52,plain,(
% 0.23/0.49    ( ! [X2,X1] : (k1_xboole_0 = k3_xboole_0(X1,X2) | ~r1_xboole_0(X1,X2)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f46,f51])).
% 0.23/0.49  fof(f51,plain,(
% 0.23/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.23/0.49    inference(forward_demodulation,[],[f45,f22])).
% 0.23/0.49  fof(f22,plain,(
% 0.23/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f2])).
% 0.23/0.49  fof(f2,axiom,(
% 0.23/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.23/0.49  fof(f45,plain,(
% 0.23/0.49    ( ! [X0] : (k3_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,X0)) )),
% 0.23/0.49    inference(superposition,[],[f27,f23])).
% 0.23/0.49  fof(f27,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.23/0.49    inference(cnf_transformation,[],[f5])).
% 0.23/0.49  fof(f5,axiom,(
% 0.23/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.23/0.49  fof(f46,plain,(
% 0.23/0.49    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X1,X1) | ~r1_xboole_0(X1,X2)) )),
% 0.23/0.49    inference(superposition,[],[f27,f29])).
% 0.23/0.49  fof(f29,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f14])).
% 0.23/0.49  fof(f14,plain,(
% 0.23/0.49    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.23/0.49    inference(ennf_transformation,[],[f12])).
% 0.23/0.49  fof(f12,plain,(
% 0.23/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 0.23/0.49    inference(unused_predicate_definition_removal,[],[f7])).
% 0.23/0.49  fof(f7,axiom,(
% 0.23/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.23/0.49  fof(f54,plain,(
% 0.23/0.49    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 0.23/0.49    inference(superposition,[],[f28,f25])).
% 0.23/0.49  fof(f25,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f1])).
% 0.23/0.49  fof(f1,axiom,(
% 0.23/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.23/0.49  fof(f28,plain,(
% 0.23/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.23/0.49    inference(cnf_transformation,[],[f4])).
% 0.23/0.49  fof(f4,axiom,(
% 0.23/0.49    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.23/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.23/0.49  fof(f21,plain,(
% 0.23/0.49    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 0.23/0.49    inference(cnf_transformation,[],[f16])).
% 0.23/0.49  % SZS output end Proof for theBenchmark
% 0.23/0.49  % (10316)------------------------------
% 0.23/0.49  % (10316)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.49  % (10316)Termination reason: Refutation
% 0.23/0.49  
% 0.23/0.49  % (10316)Memory used [KB]: 1791
% 0.23/0.49  % (10316)Time elapsed: 0.067 s
% 0.23/0.49  % (10316)------------------------------
% 0.23/0.49  % (10316)------------------------------
% 0.23/0.50  % (10312)Success in time 0.128 s
%------------------------------------------------------------------------------
