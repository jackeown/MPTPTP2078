%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:27 EST 2020

% Result     : Theorem 1.35s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 119 expanded)
%              Number of leaves         :   14 (  35 expanded)
%              Depth                    :   19
%              Number of atoms          :  108 ( 203 expanded)
%              Number of equality atoms :   42 (  77 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2781,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2778,f28])).

fof(f28,plain,(
    ~ r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    & r1_xboole_0(sK1,sK2)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ~ r1_xboole_0(X0,X2)
        & r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
   => ( ~ r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK1,sK2)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X2)
      & r1_xboole_0(X1,X2)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r1_xboole_0(X1,X2)
          & r1_tarski(X0,X1) )
       => r1_xboole_0(X0,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f2778,plain,(
    r1_xboole_0(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f2772])).

fof(f2772,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f49,f2751])).

fof(f2751,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f2748,f31])).

fof(f31,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f2748,plain,(
    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0) ),
    inference(resolution,[],[f2742,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f2742,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2741,f46])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f32,f34,f34])).

fof(f34,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

% (10141)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2741,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2731,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f45,f31])).

fof(f45,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f29,f34])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f2731,plain,(
    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f2591,f1950])).

fof(f1950,plain,(
    sK1 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f1949,f745])).

fof(f745,plain,(
    ! [X6,X5] : k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5 ),
    inference(resolution,[],[f683,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f683,plain,(
    ! [X57,X58] : r1_tarski(k4_xboole_0(X57,X58),X57) ),
    inference(forward_demodulation,[],[f682,f31])).

fof(f682,plain,(
    ! [X57,X58] : r1_tarski(k4_xboole_0(X57,X58),k4_xboole_0(X57,k1_xboole_0)) ),
    inference(resolution,[],[f43,f86])).

fof(f86,plain,(
    ! [X6] : r1_tarski(k1_xboole_0,X6) ),
    inference(superposition,[],[f70,f52])).

fof(f52,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f33,f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f70,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(resolution,[],[f44,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(trivial_inequality_removal,[],[f62])).

fof(f62,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X1,X1) ) ),
    inference(superposition,[],[f41,f51])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(k2_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X1),X2)
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).

fof(f1949,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f1943,f30])).

fof(f1943,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0) ),
    inference(superposition,[],[f35,f1936])).

fof(f1936,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(resolution,[],[f50,f27])).

fof(f27,plain,(
    r1_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f39,f34])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f2591,plain,(
    ! [X3] : r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X3))) ),
    inference(superposition,[],[f684,f46])).

fof(f684,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,sK0)),k4_xboole_0(X0,k4_xboole_0(X1,sK1))) ),
    inference(resolution,[],[f664,f43])).

fof(f664,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0)) ),
    inference(resolution,[],[f43,f26])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f40,f34])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:24:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (10130)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (10137)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (10139)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (10128)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (10135)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (10131)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (10127)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (10138)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (10126)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.53  % (10136)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (10129)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.53  % (10132)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (10134)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 1.35/0.54  % (10139)Refutation found. Thanks to Tanya!
% 1.35/0.54  % SZS status Theorem for theBenchmark
% 1.35/0.54  % SZS output start Proof for theBenchmark
% 1.35/0.54  fof(f2781,plain,(
% 1.35/0.54    $false),
% 1.35/0.54    inference(subsumption_resolution,[],[f2778,f28])).
% 1.35/0.54  fof(f28,plain,(
% 1.35/0.54    ~r1_xboole_0(sK0,sK2)),
% 1.35/0.54    inference(cnf_transformation,[],[f23])).
% 1.35/0.54  fof(f23,plain,(
% 1.35/0.54    ~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1)),
% 1.35/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => (~r1_xboole_0(sK0,sK2) & r1_xboole_0(sK1,sK2) & r1_tarski(sK0,sK1))),
% 1.35/0.54    introduced(choice_axiom,[])).
% 1.35/0.54  fof(f18,plain,(
% 1.35/0.54    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & r1_xboole_0(X1,X2) & r1_tarski(X0,X1))),
% 1.35/0.54    inference(flattening,[],[f17])).
% 1.35/0.54  fof(f17,plain,(
% 1.35/0.54    ? [X0,X1,X2] : (~r1_xboole_0(X0,X2) & (r1_xboole_0(X1,X2) & r1_tarski(X0,X1)))),
% 1.35/0.54    inference(ennf_transformation,[],[f16])).
% 1.35/0.54  fof(f16,negated_conjecture,(
% 1.35/0.54    ~! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.35/0.54    inference(negated_conjecture,[],[f15])).
% 1.35/0.54  fof(f15,conjecture,(
% 1.35/0.54    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.35/0.54  fof(f2778,plain,(
% 1.35/0.54    r1_xboole_0(sK0,sK2)),
% 1.35/0.54    inference(trivial_inequality_removal,[],[f2772])).
% 1.35/0.54  fof(f2772,plain,(
% 1.35/0.54    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK0,sK2)),
% 1.35/0.54    inference(superposition,[],[f49,f2751])).
% 1.35/0.54  fof(f2751,plain,(
% 1.35/0.54    k1_xboole_0 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 1.35/0.54    inference(superposition,[],[f2748,f31])).
% 1.35/0.54  fof(f31,plain,(
% 1.35/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.54    inference(cnf_transformation,[],[f11])).
% 1.35/0.54  fof(f11,axiom,(
% 1.35/0.54    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.35/0.54  fof(f2748,plain,(
% 1.35/0.54    k1_xboole_0 = k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0)),
% 1.35/0.54    inference(resolution,[],[f2742,f42])).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f25])).
% 1.35/0.54  fof(f25,plain,(
% 1.35/0.54    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.35/0.54    inference(nnf_transformation,[],[f9])).
% 1.35/0.54  fof(f9,axiom,(
% 1.35/0.54    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_xboole_1)).
% 1.35/0.54  fof(f2742,plain,(
% 1.35/0.54    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k1_xboole_0)),
% 1.35/0.54    inference(forward_demodulation,[],[f2741,f46])).
% 1.35/0.54  fof(f46,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f32,f34,f34])).
% 1.35/0.54  fof(f34,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f13])).
% 1.35/0.54  % (10141)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.35/0.54  fof(f13,axiom,(
% 1.35/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.35/0.54  fof(f32,plain,(
% 1.35/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f2])).
% 1.35/0.54  fof(f2,axiom,(
% 1.35/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.35/0.54  fof(f2741,plain,(
% 1.35/0.54    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k1_xboole_0)),
% 1.35/0.54    inference(forward_demodulation,[],[f2731,f51])).
% 1.35/0.54  fof(f51,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.35/0.54    inference(backward_demodulation,[],[f45,f31])).
% 1.35/0.54  fof(f45,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.35/0.54    inference(definition_unfolding,[],[f29,f34])).
% 1.35/0.54  fof(f29,plain,(
% 1.35/0.54    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f7])).
% 1.35/0.54  fof(f7,axiom,(
% 1.35/0.54    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.35/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.35/0.54  fof(f2731,plain,(
% 1.35/0.54    r1_tarski(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),k4_xboole_0(sK1,sK1))),
% 1.35/0.54    inference(superposition,[],[f2591,f1950])).
% 1.35/0.54  fof(f1950,plain,(
% 1.35/0.54    sK1 = k4_xboole_0(sK1,sK2)),
% 1.35/0.54    inference(forward_demodulation,[],[f1949,f745])).
% 1.35/0.54  fof(f745,plain,(
% 1.35/0.54    ( ! [X6,X5] : (k2_xboole_0(k4_xboole_0(X5,X6),X5) = X5) )),
% 1.35/0.54    inference(resolution,[],[f683,f38])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 1.35/0.54    inference(cnf_transformation,[],[f19])).
% 1.35/0.54  fof(f19,plain,(
% 1.35/0.54    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.35/0.54    inference(ennf_transformation,[],[f5])).
% 1.35/0.55  fof(f5,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.35/0.55  fof(f683,plain,(
% 1.35/0.55    ( ! [X57,X58] : (r1_tarski(k4_xboole_0(X57,X58),X57)) )),
% 1.35/0.55    inference(forward_demodulation,[],[f682,f31])).
% 1.35/0.55  fof(f682,plain,(
% 1.35/0.55    ( ! [X57,X58] : (r1_tarski(k4_xboole_0(X57,X58),k4_xboole_0(X57,k1_xboole_0))) )),
% 1.35/0.55    inference(resolution,[],[f43,f86])).
% 1.35/0.55  fof(f86,plain,(
% 1.35/0.55    ( ! [X6] : (r1_tarski(k1_xboole_0,X6)) )),
% 1.35/0.55    inference(superposition,[],[f70,f52])).
% 1.35/0.55  fof(f52,plain,(
% 1.35/0.55    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.35/0.55    inference(superposition,[],[f33,f30])).
% 1.35/0.55  fof(f30,plain,(
% 1.35/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f6])).
% 1.35/0.55  fof(f6,axiom,(
% 1.35/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.35/0.55  fof(f33,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f1])).
% 1.35/0.55  fof(f1,axiom,(
% 1.35/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.35/0.55  fof(f70,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(resolution,[],[f44,f63])).
% 1.35/0.55  fof(f63,plain,(
% 1.35/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.35/0.55    inference(trivial_inequality_removal,[],[f62])).
% 1.35/0.55  fof(f62,plain,(
% 1.35/0.55    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X1,X1)) )),
% 1.35/0.55    inference(superposition,[],[f41,f51])).
% 1.35/0.55  fof(f41,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f25])).
% 1.35/0.55  fof(f44,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k2_xboole_0(X0,X1),X2) | r1_tarski(X0,X2)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f21])).
% 1.35/0.55  fof(f21,plain,(
% 1.35/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(k2_xboole_0(X0,X1),X2))),
% 1.35/0.55    inference(ennf_transformation,[],[f4])).
% 1.35/0.55  fof(f4,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X1),X2) => r1_tarski(X0,X2))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).
% 1.35/0.55  fof(f43,plain,(
% 1.35/0.55    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f20])).
% 1.35/0.55  fof(f20,plain,(
% 1.35/0.55    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))),
% 1.35/0.55    inference(ennf_transformation,[],[f8])).
% 1.35/0.55  fof(f8,axiom,(
% 1.35/0.55    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X2,X1),k4_xboole_0(X2,X0)))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_xboole_1)).
% 1.35/0.55  fof(f1949,plain,(
% 1.35/0.55    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 1.35/0.55    inference(forward_demodulation,[],[f1943,f30])).
% 1.35/0.55  fof(f1943,plain,(
% 1.35/0.55    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),k1_xboole_0)),
% 1.35/0.55    inference(superposition,[],[f35,f1936])).
% 1.35/0.55  fof(f1936,plain,(
% 1.35/0.55    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.35/0.55    inference(resolution,[],[f50,f27])).
% 1.35/0.55  fof(f27,plain,(
% 1.35/0.55    r1_xboole_0(sK1,sK2)),
% 1.35/0.55    inference(cnf_transformation,[],[f23])).
% 1.35/0.55  fof(f50,plain,(
% 1.35/0.55    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.35/0.55    inference(definition_unfolding,[],[f39,f34])).
% 1.35/0.55  fof(f39,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.35/0.55    inference(cnf_transformation,[],[f24])).
% 1.35/0.55  fof(f24,plain,(
% 1.35/0.55    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.35/0.55    inference(nnf_transformation,[],[f3])).
% 1.35/0.55  fof(f3,axiom,(
% 1.35/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.35/0.55  fof(f35,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.35/0.55    inference(cnf_transformation,[],[f10])).
% 1.35/0.55  fof(f10,axiom,(
% 1.35/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.35/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.35/0.55  fof(f2591,plain,(
% 1.35/0.55    ( ! [X3] : (r1_tarski(k4_xboole_0(X3,k4_xboole_0(X3,sK0)),k4_xboole_0(sK1,k4_xboole_0(sK1,X3)))) )),
% 1.35/0.55    inference(superposition,[],[f684,f46])).
% 1.35/0.55  fof(f684,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,k4_xboole_0(X1,sK0)),k4_xboole_0(X0,k4_xboole_0(X1,sK1)))) )),
% 1.35/0.55    inference(resolution,[],[f664,f43])).
% 1.35/0.55  fof(f664,plain,(
% 1.35/0.55    ( ! [X0] : (r1_tarski(k4_xboole_0(X0,sK1),k4_xboole_0(X0,sK0))) )),
% 1.35/0.55    inference(resolution,[],[f43,f26])).
% 1.35/0.55  fof(f26,plain,(
% 1.35/0.55    r1_tarski(sK0,sK1)),
% 1.35/0.55    inference(cnf_transformation,[],[f23])).
% 1.35/0.55  fof(f49,plain,(
% 1.35/0.55    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.35/0.55    inference(definition_unfolding,[],[f40,f34])).
% 1.35/0.55  fof(f40,plain,(
% 1.35/0.55    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.35/0.55    inference(cnf_transformation,[],[f24])).
% 1.35/0.55  % SZS output end Proof for theBenchmark
% 1.35/0.55  % (10139)------------------------------
% 1.35/0.55  % (10139)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.55  % (10139)Termination reason: Refutation
% 1.35/0.55  
% 1.35/0.55  % (10139)Memory used [KB]: 3070
% 1.35/0.55  % (10139)Time elapsed: 0.114 s
% 1.35/0.55  % (10139)------------------------------
% 1.35/0.55  % (10139)------------------------------
% 1.35/0.55  % (10125)Success in time 0.185 s
%------------------------------------------------------------------------------
