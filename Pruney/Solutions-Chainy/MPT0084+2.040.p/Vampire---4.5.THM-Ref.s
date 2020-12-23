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
% DateTime   : Thu Dec  3 12:31:19 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 156 expanded)
%              Number of leaves         :   11 (  49 expanded)
%              Depth                    :   19
%              Number of atoms          :   93 ( 244 expanded)
%              Number of equality atoms :   53 ( 133 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5298,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5287,f19])).

fof(f19,plain,(
    ~ r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    & r1_tarski(sK0,sK2)
    & ~ r1_xboole_0(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2] :
        ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) )
   => ( r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))
      & r1_tarski(sK0,sK2)
      & ~ r1_xboole_0(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      & r1_tarski(X0,X2)
      & ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,X2)
          & ~ r1_xboole_0(X0,X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,X2)
        & ~ r1_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

fof(f5287,plain,(
    r1_xboole_0(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f5272])).

fof(f5272,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f38,f5160])).

fof(f5160,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f5117,f480])).

fof(f480,plain,(
    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f431,f37])).

fof(f37,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f26,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f431,plain,(
    ! [X0] : k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(forward_demodulation,[],[f415,f405])).

fof(f405,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(sK0,X0) ),
    inference(superposition,[],[f34,f389])).

fof(f389,plain,(
    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(forward_demodulation,[],[f359,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f359,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(superposition,[],[f37,f90])).

fof(f90,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(resolution,[],[f39,f35])).

fof(f35,plain,(
    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))) ),
    inference(definition_unfolding,[],[f21,f25])).

fof(f21,plain,(
    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f16])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f34,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f415,plain,(
    ! [X0] : k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))) ),
    inference(superposition,[],[f405,f27])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f5117,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X2,sK2))) ),
    inference(superposition,[],[f5017,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f32,f25,f25])).

fof(f32,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f5017,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),sK2) ),
    inference(resolution,[],[f4943,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f4943,plain,(
    ! [X31] : r1_tarski(k4_xboole_0(sK0,X31),sK2) ),
    inference(trivial_inequality_removal,[],[f4885])).

fof(f4885,plain,(
    ! [X31] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(k4_xboole_0(sK0,X31),sK2) ) ),
    inference(superposition,[],[f119,f2293])).

fof(f2293,plain,(
    ! [X14] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X14,sK2)) ),
    inference(superposition,[],[f105,f882])).

fof(f882,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,sK2))) ),
    inference(forward_demodulation,[],[f881,f43])).

fof(f43,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f36,f23])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f22,f25])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f881,plain,(
    ! [X2] : k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,sK2))) ),
    inference(forward_demodulation,[],[f855,f23])).

fof(f855,plain,(
    ! [X2] : k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,sK2))) ),
    inference(superposition,[],[f807,f132])).

fof(f132,plain,(
    ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,X7)) ),
    inference(forward_demodulation,[],[f114,f27])).

fof(f114,plain,(
    ! [X8,X7] : k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8))) ),
    inference(superposition,[],[f34,f43])).

fof(f807,plain,(
    ! [X30] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X30))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X30)) ),
    inference(forward_demodulation,[],[f731,f34])).

fof(f731,plain,(
    ! [X30] : k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X30))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X30) ),
    inference(superposition,[],[f40,f52])).

fof(f52,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f31,f20])).

fof(f20,plain,(
    r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f16])).

fof(f105,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f34,f23])).

fof(f119,plain,(
    ! [X12,X10,X11] :
      ( k1_xboole_0 != k4_xboole_0(X10,k2_xboole_0(X11,X12))
      | r1_tarski(k4_xboole_0(X10,X11),X12) ) ),
    inference(superposition,[],[f30,f34])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f29,f25])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:11:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.41  % (5586)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.46  % (5575)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (5578)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (5574)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (5587)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (5580)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (5588)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (5590)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (5576)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (5581)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (5589)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (5582)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (5591)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (5579)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (5586)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f5298,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f5287,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ~r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f14,f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1)) => (r1_xboole_0(sK0,k3_xboole_0(sK1,sK2)) & r1_tarski(sK0,sK2) & ~r1_xboole_0(sK0,sK1))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.49    inference(negated_conjecture,[],[f12])).
% 0.20/0.49  fof(f12,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : ~(r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,X2) & ~r1_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).
% 0.20/0.49  fof(f5287,plain,(
% 0.20/0.49    r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f5272])).
% 0.20/0.49  fof(f5272,plain,(
% 0.20/0.49    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK1)),
% 0.20/0.49    inference(superposition,[],[f38,f5160])).
% 0.20/0.49  fof(f5160,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.20/0.49    inference(superposition,[],[f5117,f480])).
% 0.20/0.49  fof(f480,plain,(
% 0.20/0.49    k4_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(superposition,[],[f431,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f26,f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.20/0.49  fof(f431,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(sK0,X0) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f415,f405])).
% 0.20/0.49  fof(f405,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(sK0,X0)) )),
% 0.20/0.49    inference(superposition,[],[f34,f389])).
% 0.20/0.49  fof(f389,plain,(
% 0.20/0.49    sK0 = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.49    inference(forward_demodulation,[],[f359,f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.49  fof(f359,plain,(
% 0.20/0.49    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.49    inference(superposition,[],[f37,f90])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))),
% 0.20/0.49    inference(resolution,[],[f39,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)))),
% 0.20/0.49    inference(definition_unfolding,[],[f21,f25])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    r1_xboole_0(sK0,k3_xboole_0(sK1,sK2))),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f25])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.20/0.49  fof(f415,plain,(
% 0.20/0.49    ( ! [X0] : (k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)),X0)) = k4_xboole_0(sK0,k4_xboole_0(X0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))))) )),
% 0.20/0.49    inference(superposition,[],[f405,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.20/0.49  fof(f5117,plain,(
% 0.20/0.49    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(X2,sK2)))) )),
% 0.20/0.49    inference(superposition,[],[f5017,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f32,f25,f25])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.20/0.49  fof(f5017,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,X0),sK2)) )),
% 0.20/0.49    inference(resolution,[],[f4943,f31])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.20/0.49  fof(f4943,plain,(
% 0.20/0.49    ( ! [X31] : (r1_tarski(k4_xboole_0(sK0,X31),sK2)) )),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f4885])).
% 0.20/0.49  fof(f4885,plain,(
% 0.20/0.49    ( ! [X31] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(k4_xboole_0(sK0,X31),sK2)) )),
% 0.20/0.49    inference(superposition,[],[f119,f2293])).
% 0.20/0.49  fof(f2293,plain,(
% 0.20/0.49    ( ! [X14] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(X14,sK2))) )),
% 0.20/0.49    inference(superposition,[],[f105,f882])).
% 0.20/0.49  fof(f882,plain,(
% 0.20/0.49    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,sK2)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f881,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.49    inference(forward_demodulation,[],[f36,f23])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f22,f25])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.49  fof(f881,plain,(
% 0.20/0.49    ( ! [X2] : (k4_xboole_0(sK0,sK0) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,sK2)))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f855,f23])).
% 0.20/0.49  fof(f855,plain,(
% 0.20/0.49    ( ! [X2] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k1_xboole_0)) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,k2_xboole_0(X2,sK2)))) )),
% 0.20/0.49    inference(superposition,[],[f807,f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,X7))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f114,f27])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X8,X7] : (k1_xboole_0 = k4_xboole_0(X7,k2_xboole_0(X8,k4_xboole_0(X7,X8)))) )),
% 0.20/0.49    inference(superposition,[],[f34,f43])).
% 0.20/0.49  fof(f807,plain,(
% 0.20/0.49    ( ! [X30] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X30))) = k4_xboole_0(sK0,k2_xboole_0(k1_xboole_0,X30))) )),
% 0.20/0.49    inference(forward_demodulation,[],[f731,f34])).
% 0.20/0.49  fof(f731,plain,(
% 0.20/0.49    ( ! [X30] : (k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK2,X30))) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),X30)) )),
% 0.20/0.49    inference(superposition,[],[f40,f52])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 0.20/0.49    inference(resolution,[],[f31,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    r1_tarski(sK0,sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k2_xboole_0(k1_xboole_0,X1))) )),
% 0.20/0.49    inference(superposition,[],[f34,f23])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    ( ! [X12,X10,X11] : (k1_xboole_0 != k4_xboole_0(X10,k2_xboole_0(X11,X12)) | r1_tarski(k4_xboole_0(X10,X11),X12)) )),
% 0.20/0.49    inference(superposition,[],[f30,f34])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f29,f25])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (5586)------------------------------
% 0.20/0.49  % (5586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (5586)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (5586)Memory used [KB]: 3837
% 0.20/0.49  % (5586)Time elapsed: 0.085 s
% 0.20/0.49  % (5586)------------------------------
% 0.20/0.49  % (5586)------------------------------
% 0.20/0.50  % (5573)Success in time 0.138 s
%------------------------------------------------------------------------------
