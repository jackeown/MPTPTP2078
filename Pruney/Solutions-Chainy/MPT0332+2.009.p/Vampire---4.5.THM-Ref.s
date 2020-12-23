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
% DateTime   : Thu Dec  3 12:43:09 EST 2020

% Result     : Theorem 2.94s
% Output     : Refutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 241 expanded)
%              Number of leaves         :   13 (  79 expanded)
%              Depth                    :   16
%              Number of atoms          :   87 ( 290 expanded)
%              Number of equality atoms :   59 ( 238 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6903,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5119,f6901])).

fof(f6901,plain,(
    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(resolution,[],[f6322,f26])).

fof(f26,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f6322,plain,(
    ! [X1] :
      ( r2_hidden(X1,sK2)
      | sK2 = k4_xboole_0(sK2,k2_tarski(X1,sK1)) ) ),
    inference(resolution,[],[f42,f27])).

fof(f27,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f5119,plain,(
    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    inference(superposition,[],[f28,f2706])).

fof(f2706,plain,(
    ! [X26,X27] : k4_xboole_0(X27,X26) = k4_xboole_0(k2_xboole_0(X27,X26),X26) ),
    inference(forward_demodulation,[],[f2705,f2179])).

fof(f2179,plain,(
    ! [X28,X27] : k4_xboole_0(X27,X28) = k5_xboole_0(X28,k2_xboole_0(X27,X28)) ),
    inference(forward_demodulation,[],[f2130,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2130,plain,(
    ! [X28,X27] : k5_xboole_0(X28,k2_xboole_0(X27,X28)) = k5_xboole_0(X27,k3_xboole_0(X27,X28)) ),
    inference(superposition,[],[f493,f478])).

fof(f478,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f41,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f493,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f470,f47])).

fof(f47,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f32,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f470,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f41,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f2705,plain,(
    ! [X26,X27] : k5_xboole_0(X26,k2_xboole_0(X27,X26)) = k4_xboole_0(k2_xboole_0(X27,X26),X26) ),
    inference(forward_demodulation,[],[f2676,f32])).

fof(f2676,plain,(
    ! [X26,X27] : k4_xboole_0(k2_xboole_0(X27,X26),X26) = k5_xboole_0(k2_xboole_0(X27,X26),X26) ),
    inference(superposition,[],[f1364,f2371])).

fof(f2371,plain,(
    ! [X19,X20] : k3_xboole_0(X19,k2_xboole_0(X20,X19)) = X19 ),
    inference(forward_demodulation,[],[f2369,f2240])).

fof(f2240,plain,(
    ! [X28,X29] : k5_xboole_0(k2_xboole_0(X29,X28),k4_xboole_0(X29,X28)) = X28 ),
    inference(superposition,[],[f497,f2179])).

fof(f497,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f493,f32])).

fof(f2369,plain,(
    ! [X19,X20] : k3_xboole_0(X19,k2_xboole_0(X20,X19)) = k5_xboole_0(k2_xboole_0(X20,X19),k4_xboole_0(X20,X19)) ),
    inference(backward_demodulation,[],[f2236,f2366])).

fof(f2366,plain,(
    ! [X43,X42] : k2_xboole_0(X43,X42) = k2_xboole_0(X42,k2_xboole_0(X43,X42)) ),
    inference(backward_demodulation,[],[f2247,f2363])).

fof(f2363,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5 ),
    inference(backward_demodulation,[],[f2213,f2317])).

fof(f2317,plain,(
    ! [X35,X36] : k5_xboole_0(k4_xboole_0(X36,X35),k2_xboole_0(X35,X36)) = X35 ),
    inference(superposition,[],[f519,f2211])).

fof(f2211,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X2) ),
    inference(superposition,[],[f2179,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f519,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f497,f493])).

fof(f2213,plain,(
    ! [X6,X5] : k5_xboole_0(k4_xboole_0(X6,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X5,k4_xboole_0(X6,X5)) ),
    inference(superposition,[],[f2179,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2247,plain,(
    ! [X43,X42] : k2_xboole_0(X43,X42) = k2_xboole_0(k4_xboole_0(X42,k4_xboole_0(X43,X42)),k2_xboole_0(X43,X42)) ),
    inference(superposition,[],[f539,f2179])).

fof(f539,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = X1 ),
    inference(resolution,[],[f506,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f506,plain,(
    ! [X4,X5] : r1_tarski(k4_xboole_0(X4,k5_xboole_0(X4,X5)),X5) ),
    inference(superposition,[],[f33,f493])).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f2236,plain,(
    ! [X19,X20] : k3_xboole_0(X19,k2_xboole_0(X20,X19)) = k5_xboole_0(k2_xboole_0(X19,k2_xboole_0(X20,X19)),k4_xboole_0(X20,X19)) ),
    inference(superposition,[],[f382,f2179])).

fof(f382,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3)) ),
    inference(superposition,[],[f38,f32])).

fof(f1364,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f36,f1293])).

fof(f1293,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3) ),
    inference(superposition,[],[f369,f362])).

fof(f362,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f38,f32])).

fof(f369,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f38,f31])).

fof(f28,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:56:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (5544)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (5535)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (5551)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (5540)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (5545)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (5537)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (5539)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (5543)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (5547)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (5538)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.52  % (5541)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (5552)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (5550)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (5536)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.53  % (5546)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.53  % (5549)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.53  % (5542)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.53  % (5553)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 2.94/0.75  % (5552)Refutation found. Thanks to Tanya!
% 2.94/0.75  % SZS status Theorem for theBenchmark
% 2.94/0.75  % SZS output start Proof for theBenchmark
% 2.94/0.75  fof(f6903,plain,(
% 2.94/0.75    $false),
% 2.94/0.75    inference(subsumption_resolution,[],[f5119,f6901])).
% 2.94/0.75  fof(f6901,plain,(
% 2.94/0.75    sK2 = k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.94/0.75    inference(resolution,[],[f6322,f26])).
% 2.94/0.75  fof(f26,plain,(
% 2.94/0.75    ~r2_hidden(sK0,sK2)),
% 2.94/0.75    inference(cnf_transformation,[],[f25])).
% 2.94/0.75  fof(f25,plain,(
% 2.94/0.75    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 2.94/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f24])).
% 2.94/0.75  fof(f24,plain,(
% 2.94/0.75    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 2.94/0.75    introduced(choice_axiom,[])).
% 2.94/0.75  fof(f21,plain,(
% 2.94/0.75    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.94/0.75    inference(ennf_transformation,[],[f20])).
% 2.94/0.75  fof(f20,negated_conjecture,(
% 2.94/0.75    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.94/0.75    inference(negated_conjecture,[],[f19])).
% 2.94/0.75  fof(f19,conjecture,(
% 2.94/0.75    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 2.94/0.75  fof(f6322,plain,(
% 2.94/0.75    ( ! [X1] : (r2_hidden(X1,sK2) | sK2 = k4_xboole_0(sK2,k2_tarski(X1,sK1))) )),
% 2.94/0.75    inference(resolution,[],[f42,f27])).
% 2.94/0.75  fof(f27,plain,(
% 2.94/0.75    ~r2_hidden(sK1,sK2)),
% 2.94/0.75    inference(cnf_transformation,[],[f25])).
% 2.94/0.75  fof(f42,plain,(
% 2.94/0.75    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X0,X2)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f23])).
% 2.94/0.75  fof(f23,plain,(
% 2.94/0.75    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 2.94/0.75    inference(ennf_transformation,[],[f18])).
% 2.94/0.75  fof(f18,axiom,(
% 2.94/0.75    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 2.94/0.75  fof(f5119,plain,(
% 2.94/0.75    sK2 != k4_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.94/0.75    inference(superposition,[],[f28,f2706])).
% 2.94/0.75  fof(f2706,plain,(
% 2.94/0.75    ( ! [X26,X27] : (k4_xboole_0(X27,X26) = k4_xboole_0(k2_xboole_0(X27,X26),X26)) )),
% 2.94/0.75    inference(forward_demodulation,[],[f2705,f2179])).
% 2.94/0.75  fof(f2179,plain,(
% 2.94/0.75    ( ! [X28,X27] : (k4_xboole_0(X27,X28) = k5_xboole_0(X28,k2_xboole_0(X27,X28))) )),
% 2.94/0.75    inference(forward_demodulation,[],[f2130,f36])).
% 2.94/0.75  fof(f36,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.94/0.75    inference(cnf_transformation,[],[f3])).
% 2.94/0.75  fof(f3,axiom,(
% 2.94/0.75    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.94/0.75  fof(f2130,plain,(
% 2.94/0.75    ( ! [X28,X27] : (k5_xboole_0(X28,k2_xboole_0(X27,X28)) = k5_xboole_0(X27,k3_xboole_0(X27,X28))) )),
% 2.94/0.75    inference(superposition,[],[f493,f478])).
% 2.94/0.75  fof(f478,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 2.94/0.75    inference(superposition,[],[f41,f38])).
% 2.94/0.75  fof(f38,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.94/0.75    inference(cnf_transformation,[],[f9])).
% 2.94/0.75  fof(f9,axiom,(
% 2.94/0.75    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.94/0.75  fof(f41,plain,(
% 2.94/0.75    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.94/0.75    inference(cnf_transformation,[],[f7])).
% 2.94/0.75  fof(f7,axiom,(
% 2.94/0.75    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.94/0.75  fof(f493,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.94/0.75    inference(forward_demodulation,[],[f470,f47])).
% 2.94/0.75  fof(f47,plain,(
% 2.94/0.75    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 2.94/0.75    inference(superposition,[],[f32,f30])).
% 2.94/0.75  fof(f30,plain,(
% 2.94/0.75    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.94/0.75    inference(cnf_transformation,[],[f6])).
% 2.94/0.75  fof(f6,axiom,(
% 2.94/0.75    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.94/0.75  fof(f32,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f2])).
% 2.94/0.75  fof(f2,axiom,(
% 2.94/0.75    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.94/0.75  fof(f470,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.94/0.75    inference(superposition,[],[f41,f29])).
% 2.94/0.75  fof(f29,plain,(
% 2.94/0.75    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f8])).
% 2.94/0.75  fof(f8,axiom,(
% 2.94/0.75    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.94/0.75  fof(f2705,plain,(
% 2.94/0.75    ( ! [X26,X27] : (k5_xboole_0(X26,k2_xboole_0(X27,X26)) = k4_xboole_0(k2_xboole_0(X27,X26),X26)) )),
% 2.94/0.75    inference(forward_demodulation,[],[f2676,f32])).
% 2.94/0.75  fof(f2676,plain,(
% 2.94/0.75    ( ! [X26,X27] : (k4_xboole_0(k2_xboole_0(X27,X26),X26) = k5_xboole_0(k2_xboole_0(X27,X26),X26)) )),
% 2.94/0.75    inference(superposition,[],[f1364,f2371])).
% 2.94/0.75  fof(f2371,plain,(
% 2.94/0.75    ( ! [X19,X20] : (k3_xboole_0(X19,k2_xboole_0(X20,X19)) = X19) )),
% 2.94/0.75    inference(forward_demodulation,[],[f2369,f2240])).
% 2.94/0.75  fof(f2240,plain,(
% 2.94/0.75    ( ! [X28,X29] : (k5_xboole_0(k2_xboole_0(X29,X28),k4_xboole_0(X29,X28)) = X28) )),
% 2.94/0.75    inference(superposition,[],[f497,f2179])).
% 2.94/0.75  fof(f497,plain,(
% 2.94/0.75    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.94/0.75    inference(superposition,[],[f493,f32])).
% 2.94/0.75  fof(f2369,plain,(
% 2.94/0.75    ( ! [X19,X20] : (k3_xboole_0(X19,k2_xboole_0(X20,X19)) = k5_xboole_0(k2_xboole_0(X20,X19),k4_xboole_0(X20,X19))) )),
% 2.94/0.75    inference(backward_demodulation,[],[f2236,f2366])).
% 2.94/0.75  fof(f2366,plain,(
% 2.94/0.75    ( ! [X43,X42] : (k2_xboole_0(X43,X42) = k2_xboole_0(X42,k2_xboole_0(X43,X42))) )),
% 2.94/0.75    inference(backward_demodulation,[],[f2247,f2363])).
% 2.94/0.75  fof(f2363,plain,(
% 2.94/0.75    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5) )),
% 2.94/0.75    inference(backward_demodulation,[],[f2213,f2317])).
% 2.94/0.75  fof(f2317,plain,(
% 2.94/0.75    ( ! [X35,X36] : (k5_xboole_0(k4_xboole_0(X36,X35),k2_xboole_0(X35,X36)) = X35) )),
% 2.94/0.75    inference(superposition,[],[f519,f2211])).
% 2.94/0.75  fof(f2211,plain,(
% 2.94/0.75    ( ! [X2,X1] : (k5_xboole_0(X2,k2_xboole_0(X2,X1)) = k4_xboole_0(X1,X2)) )),
% 2.94/0.75    inference(superposition,[],[f2179,f31])).
% 2.94/0.75  fof(f31,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.94/0.75    inference(cnf_transformation,[],[f1])).
% 2.94/0.75  fof(f1,axiom,(
% 2.94/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.94/0.75  fof(f519,plain,(
% 2.94/0.75    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 2.94/0.75    inference(superposition,[],[f497,f493])).
% 2.94/0.75  fof(f2213,plain,(
% 2.94/0.75    ( ! [X6,X5] : (k5_xboole_0(k4_xboole_0(X6,X5),k2_xboole_0(X5,X6)) = k4_xboole_0(X5,k4_xboole_0(X6,X5))) )),
% 2.94/0.75    inference(superposition,[],[f2179,f37])).
% 2.94/0.75  fof(f37,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.94/0.75    inference(cnf_transformation,[],[f5])).
% 2.94/0.75  fof(f5,axiom,(
% 2.94/0.75    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.94/0.75  fof(f2247,plain,(
% 2.94/0.75    ( ! [X43,X42] : (k2_xboole_0(X43,X42) = k2_xboole_0(k4_xboole_0(X42,k4_xboole_0(X43,X42)),k2_xboole_0(X43,X42))) )),
% 2.94/0.75    inference(superposition,[],[f539,f2179])).
% 2.94/0.75  fof(f539,plain,(
% 2.94/0.75    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k5_xboole_0(X0,X1)),X1) = X1) )),
% 2.94/0.75    inference(resolution,[],[f506,f39])).
% 2.94/0.75  fof(f39,plain,(
% 2.94/0.75    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 2.94/0.75    inference(cnf_transformation,[],[f22])).
% 2.94/0.75  fof(f22,plain,(
% 2.94/0.75    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.94/0.75    inference(ennf_transformation,[],[f4])).
% 2.94/0.75  fof(f4,axiom,(
% 2.94/0.75    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.94/0.75  fof(f506,plain,(
% 2.94/0.75    ( ! [X4,X5] : (r1_tarski(k4_xboole_0(X4,k5_xboole_0(X4,X5)),X5)) )),
% 2.94/0.75    inference(superposition,[],[f33,f493])).
% 2.94/0.75  fof(f33,plain,(
% 2.94/0.75    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.94/0.75    inference(cnf_transformation,[],[f10])).
% 2.94/0.75  fof(f10,axiom,(
% 2.94/0.75    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.94/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).
% 2.94/0.75  fof(f2236,plain,(
% 2.94/0.75    ( ! [X19,X20] : (k3_xboole_0(X19,k2_xboole_0(X20,X19)) = k5_xboole_0(k2_xboole_0(X19,k2_xboole_0(X20,X19)),k4_xboole_0(X20,X19))) )),
% 2.94/0.75    inference(superposition,[],[f382,f2179])).
% 2.94/0.75  fof(f382,plain,(
% 2.94/0.75    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k5_xboole_0(k2_xboole_0(X2,X3),k5_xboole_0(X2,X3))) )),
% 2.94/0.75    inference(superposition,[],[f38,f32])).
% 2.94/0.75  fof(f1364,plain,(
% 2.94/0.75    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.94/0.75    inference(superposition,[],[f36,f1293])).
% 2.94/0.75  fof(f1293,plain,(
% 2.94/0.75    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,X3)) )),
% 2.94/0.75    inference(superposition,[],[f369,f362])).
% 2.94/0.75  fof(f362,plain,(
% 2.94/0.75    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X2,X1),k2_xboole_0(X1,X2))) )),
% 2.94/0.75    inference(superposition,[],[f38,f32])).
% 2.94/0.75  fof(f369,plain,(
% 2.94/0.75    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k2_xboole_0(X2,X1))) )),
% 2.94/0.75    inference(superposition,[],[f38,f31])).
% 2.94/0.75  fof(f28,plain,(
% 2.94/0.75    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 2.94/0.75    inference(cnf_transformation,[],[f25])).
% 2.94/0.75  % SZS output end Proof for theBenchmark
% 2.94/0.75  % (5552)------------------------------
% 2.94/0.75  % (5552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.94/0.75  % (5552)Termination reason: Refutation
% 2.94/0.75  
% 2.94/0.75  % (5552)Memory used [KB]: 9338
% 2.94/0.75  % (5552)Time elapsed: 0.296 s
% 2.94/0.75  % (5552)------------------------------
% 2.94/0.75  % (5552)------------------------------
% 3.10/0.75  % (5528)Success in time 0.391 s
%------------------------------------------------------------------------------
