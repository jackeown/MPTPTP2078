%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:42 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 214 expanded)
%              Number of leaves         :   15 (  67 expanded)
%              Depth                    :   20
%              Number of atoms          :  126 ( 325 expanded)
%              Number of equality atoms :   49 ( 185 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f261,plain,(
    $false ),
    inference(subsumption_resolution,[],[f68,f260])).

fof(f260,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f257,f33])).

fof(f33,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f257,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f40,f245])).

fof(f245,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(backward_demodulation,[],[f148,f244])).

fof(f244,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(forward_demodulation,[],[f239,f205])).

fof(f205,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) ),
    inference(forward_demodulation,[],[f197,f66])).

fof(f66,plain,(
    ! [X7] : k2_xboole_0(k1_xboole_0,X7) = X7 ),
    inference(superposition,[],[f64,f33])).

fof(f64,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f56,f38])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f197,plain,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4) ),
    inference(resolution,[],[f193,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f193,plain,(
    ! [X3] : r1_xboole_0(k1_xboole_0,X3) ),
    inference(resolution,[],[f190,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f27])).

fof(f27,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f190,plain,(
    ! [X3] : ~ r2_hidden(X3,k1_xboole_0) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,k1_xboole_0)
      | ~ r2_hidden(X3,k1_xboole_0) ) ),
    inference(superposition,[],[f51,f88])).

fof(f88,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f86,f81])).

fof(f81,plain,(
    ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f39,f75])).

fof(f75,plain,(
    ! [X3] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3) ),
    inference(superposition,[],[f66,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f5])).

% (1107)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f86,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = X6 ),
    inference(forward_demodulation,[],[f83,f66])).

fof(f83,plain,(
    ! [X6] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6) ),
    inference(superposition,[],[f40,f66])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f239,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f39,f233])).

fof(f233,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(superposition,[],[f222,f66])).

fof(f222,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f95,f205])).

fof(f95,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f41,f64])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f148,plain,(
    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0)) ),
    inference(superposition,[],[f39,f142])).

fof(f142,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f60,f31])).

fof(f31,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k1_tarski(X0),X1) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k1_tarski(sK0),sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k1_tarski(X0),X1) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k1_tarski(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1) ) ),
    inference(resolution,[],[f45,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f68,plain,(
    sK1 != k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f32,f64])).

fof(f32,plain,(
    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n006.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:49:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (1098)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.47  % (1102)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (1096)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.47  % (1100)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (1104)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.48  % (1099)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (1103)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (1106)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (1108)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.49  % (1110)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (1101)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (1097)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.50  % (1105)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (1112)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (1113)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (1109)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (1111)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.51  % (1112)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f261,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(subsumption_resolution,[],[f68,f260])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.22/0.51    inference(forward_demodulation,[],[f257,f33])).
% 0.22/0.51  fof(f33,plain,(
% 0.22/0.51    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f4])).
% 0.22/0.51  fof(f4,axiom,(
% 0.22/0.51    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.22/0.51    inference(superposition,[],[f40,f245])).
% 0.22/0.51  fof(f245,plain,(
% 0.22/0.51    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.51    inference(backward_demodulation,[],[f148,f244])).
% 0.22/0.51  fof(f244,plain,(
% 0.22/0.51    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f239,f205])).
% 0.22/0.51  fof(f205,plain,(
% 0.22/0.51    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(X4,X4)) )),
% 0.22/0.51    inference(forward_demodulation,[],[f197,f66])).
% 0.22/0.51  fof(f66,plain,(
% 0.22/0.51    ( ! [X7] : (k2_xboole_0(k1_xboole_0,X7) = X7) )),
% 0.22/0.51    inference(superposition,[],[f64,f33])).
% 0.22/0.51  fof(f64,plain,(
% 0.22/0.51    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 0.22/0.51    inference(superposition,[],[f56,f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.22/0.51    inference(cnf_transformation,[],[f16])).
% 0.22/0.51  fof(f16,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.51  fof(f56,plain,(
% 0.22/0.51    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 0.22/0.51    inference(superposition,[],[f38,f35])).
% 0.22/0.51  fof(f35,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.22/0.51  fof(f197,plain,(
% 0.22/0.51    ( ! [X4] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_xboole_0,X4),X4)) )),
% 0.22/0.51    inference(resolution,[],[f193,f46])).
% 0.22/0.51  fof(f46,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 0.22/0.51    inference(ennf_transformation,[],[f9])).
% 0.22/0.51  fof(f9,axiom,(
% 0.22/0.51    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 0.22/0.51  fof(f193,plain,(
% 0.22/0.51    ( ! [X3] : (r1_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.51    inference(resolution,[],[f190,f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f28])).
% 0.22/0.51  fof(f28,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f21,f27])).
% 0.22/0.51  fof(f27,plain,(
% 0.22/0.51    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.22/0.51    introduced(choice_axiom,[])).
% 0.22/0.51  fof(f21,plain,(
% 0.22/0.51    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(ennf_transformation,[],[f19])).
% 0.22/0.51  fof(f19,plain,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    inference(rectify,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.22/0.51  fof(f190,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0)) )),
% 0.22/0.51    inference(duplicate_literal_removal,[],[f187])).
% 0.22/0.51  fof(f187,plain,(
% 0.22/0.51    ( ! [X3] : (~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,k1_xboole_0)) )),
% 0.22/0.51    inference(superposition,[],[f51,f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 0.22/0.51    inference(superposition,[],[f86,f81])).
% 0.22/0.51  fof(f81,plain,(
% 0.22/0.51    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)) )),
% 0.22/0.51    inference(superposition,[],[f39,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ( ! [X3] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X3)) )),
% 0.22/0.51    inference(superposition,[],[f66,f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.22/0.51    inference(cnf_transformation,[],[f5])).
% 0.22/0.52  % (1107)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.22/0.52    inference(cnf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = X6) )),
% 0.22/0.52    inference(forward_demodulation,[],[f83,f66])).
% 0.22/0.52  fof(f83,plain,(
% 0.22/0.52    ( ! [X6] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(k1_xboole_0,X6)) )),
% 0.22/0.52    inference(superposition,[],[f40,f66])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 0.22/0.52    inference(nnf_transformation,[],[f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 0.22/0.52    inference(ennf_transformation,[],[f1])).
% 0.22/0.52  fof(f1,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) )),
% 0.22/0.52    inference(superposition,[],[f39,f233])).
% 0.22/0.52  fof(f233,plain,(
% 0.22/0.52    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 0.22/0.52    inference(superposition,[],[f222,f66])).
% 0.22/0.52  fof(f222,plain,(
% 0.22/0.52    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,X0)) = X0) )),
% 0.22/0.52    inference(superposition,[],[f95,f205])).
% 0.22/0.52  fof(f95,plain,(
% 0.22/0.52    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2) )),
% 0.22/0.52    inference(superposition,[],[f41,f64])).
% 0.22/0.52  fof(f41,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f8])).
% 0.22/0.52  fof(f8,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.52  fof(f148,plain,(
% 0.22/0.52    k4_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k1_tarski(sK0),k1_tarski(sK0))),
% 0.22/0.52    inference(superposition,[],[f39,f142])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.52    inference(resolution,[],[f60,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k1_tarski(sK0),sK1) & r2_hidden(sK0,sK1))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ? [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != X1 & r2_hidden(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f18])).
% 0.22/0.52  fof(f18,negated_conjecture,(
% 0.22/0.52    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.22/0.52    inference(negated_conjecture,[],[f17])).
% 0.22/0.52  fof(f17,conjecture,(
% 0.22/0.52    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k1_tarski(X0),X1) = X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) = k3_xboole_0(k1_tarski(X0),X1)) )),
% 0.22/0.52    inference(resolution,[],[f45,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.22/0.52    inference(nnf_transformation,[],[f15])).
% 0.22/0.52  fof(f15,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.52  fof(f68,plain,(
% 0.22/0.52    sK1 != k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.22/0.52    inference(superposition,[],[f32,f64])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    sK1 != k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (1112)------------------------------
% 0.22/0.52  % (1112)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1112)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (1112)Memory used [KB]: 6268
% 0.22/0.52  % (1112)Time elapsed: 0.098 s
% 0.22/0.52  % (1112)------------------------------
% 0.22/0.52  % (1112)------------------------------
% 0.22/0.52  % (1093)Success in time 0.159 s
%------------------------------------------------------------------------------
