%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:54 EST 2020

% Result     : Theorem 1.49s
% Output     : Refutation 1.49s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 152 expanded)
%              Number of leaves         :   12 (  50 expanded)
%              Depth                    :   22
%              Number of atoms          :   79 ( 174 expanded)
%              Number of equality atoms :   52 ( 143 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2860,plain,(
    $false ),
    inference(resolution,[],[f2859,f102])).

fof(f102,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f30,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(superposition,[],[f38,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(X0,X1) = X0 ) ),
    inference(unused_predicate_definition_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f38,plain,(
    ! [X6,X8,X7] : r1_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X8)),X8) ),
    inference(superposition,[],[f19,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f30,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f21,f22,f25])).

fof(f25,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f22,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f2859,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f2858])).

fof(f2858,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2857,f506])).

fof(f506,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f28,f480])).

fof(f480,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f451,f23])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f451,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f424,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f424,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f80,f23])).

fof(f80,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f31,f20])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f24,f22])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f2857,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2856,f55])).

fof(f55,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f28,f20])).

fof(f2856,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2855,f23])).

fof(f2855,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2854,f20])).

fof(f2854,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2853,f1726])).

fof(f1726,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X9,k2_xboole_0(X10,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,X9))) ),
    inference(forward_demodulation,[],[f66,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f23,f27])).

fof(f66,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X9,k2_xboole_0(X10,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X9,X10)))) ),
    inference(forward_demodulation,[],[f57,f28])).

fof(f57,plain,(
    ! [X10,X11,X9] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X9,X10)))) ),
    inference(superposition,[],[f28,f23])).

fof(f2853,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2852,f55])).

fof(f2852,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2851,f1726])).

fof(f2851,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2850,f55])).

fof(f2850,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2849,f55])).

fof(f2849,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f2842,f23])).

fof(f2842,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f697,f35])).

fof(f35,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,X5))
      | ~ r1_xboole_0(k4_xboole_0(X3,X4),X5) ) ),
    inference(superposition,[],[f27,f26])).

fof(f697,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(superposition,[],[f638,f20])).

fof(f638,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f128,f506])).

fof(f128,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(forward_demodulation,[],[f29,f27])).

fof(f29,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f18,f25,f25,f22])).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:05:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (29613)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (29628)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (29627)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.46  % (29625)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (29617)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (29616)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (29619)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (29618)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (29614)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (29621)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (29612)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.48  % (29626)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (29615)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (29630)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (29623)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.50  % (29624)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.50  % (29629)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (29620)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.52  % (29624)Refutation not found, incomplete strategy% (29624)------------------------------
% 0.20/0.52  % (29624)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (29624)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (29624)Memory used [KB]: 10490
% 0.20/0.52  % (29624)Time elapsed: 0.114 s
% 0.20/0.52  % (29624)------------------------------
% 0.20/0.52  % (29624)------------------------------
% 1.49/0.55  % (29616)Refutation found. Thanks to Tanya!
% 1.49/0.55  % SZS status Theorem for theBenchmark
% 1.49/0.55  % SZS output start Proof for theBenchmark
% 1.49/0.55  fof(f2860,plain,(
% 1.49/0.55    $false),
% 1.49/0.55    inference(resolution,[],[f2859,f102])).
% 1.49/0.55  fof(f102,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X1,X0))) )),
% 1.49/0.55    inference(resolution,[],[f30,f44])).
% 1.49/0.55  fof(f44,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.49/0.55    inference(superposition,[],[f38,f26])).
% 1.49/0.55  fof(f26,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f15])).
% 1.49/0.55  fof(f15,plain,(
% 1.49/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f13])).
% 1.49/0.55  fof(f13,plain,(
% 1.49/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(X0,X1) = X0)),
% 1.49/0.55    inference(unused_predicate_definition_removal,[],[f10])).
% 1.49/0.55  fof(f10,axiom,(
% 1.49/0.55    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.49/0.55  fof(f38,plain,(
% 1.49/0.55    ( ! [X6,X8,X7] : (r1_xboole_0(k4_xboole_0(X6,k2_xboole_0(X7,X8)),X8)) )),
% 1.49/0.55    inference(superposition,[],[f19,f27])).
% 1.49/0.55  fof(f27,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f5])).
% 1.49/0.55  fof(f5,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.49/0.55  fof(f19,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f9])).
% 1.49/0.55  fof(f9,axiom,(
% 1.49/0.55    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.49/0.55  fof(f30,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 1.49/0.55    inference(definition_unfolding,[],[f21,f22,f25])).
% 1.49/0.55  fof(f25,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f2])).
% 1.49/0.55  fof(f2,axiom,(
% 1.49/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.49/0.55  fof(f22,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f6])).
% 1.49/0.55  fof(f6,axiom,(
% 1.49/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.49/0.55  fof(f21,plain,(
% 1.49/0.55    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f3])).
% 1.49/0.55  fof(f3,axiom,(
% 1.49/0.55    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 1.49/0.55  fof(f2859,plain,(
% 1.49/0.55    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(trivial_inequality_removal,[],[f2858])).
% 1.49/0.55  fof(f2858,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2857,f506])).
% 1.49/0.55  fof(f506,plain,(
% 1.49/0.55    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.49/0.55    inference(superposition,[],[f28,f480])).
% 1.49/0.55  fof(f480,plain,(
% 1.49/0.55    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.49/0.55    inference(superposition,[],[f451,f23])).
% 1.49/0.55  fof(f23,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f4])).
% 1.49/0.55  fof(f4,axiom,(
% 1.49/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.49/0.55  fof(f451,plain,(
% 1.49/0.55    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 1.49/0.55    inference(superposition,[],[f424,f20])).
% 1.49/0.55  fof(f20,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.49/0.55    inference(cnf_transformation,[],[f1])).
% 1.49/0.55  fof(f1,axiom,(
% 1.49/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.49/0.55  fof(f424,plain,(
% 1.49/0.55    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 1.49/0.55    inference(superposition,[],[f80,f23])).
% 1.49/0.55  fof(f80,plain,(
% 1.49/0.55    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 1.49/0.55    inference(superposition,[],[f31,f20])).
% 1.49/0.55  fof(f31,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.49/0.55    inference(definition_unfolding,[],[f24,f22])).
% 1.49/0.55  fof(f24,plain,(
% 1.49/0.55    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.49/0.55    inference(cnf_transformation,[],[f8])).
% 1.49/0.55  fof(f8,axiom,(
% 1.49/0.55    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.49/0.55  fof(f28,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.49/0.55    inference(cnf_transformation,[],[f7])).
% 1.49/0.55  fof(f7,axiom,(
% 1.49/0.55    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.49/0.55  fof(f2857,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2856,f55])).
% 1.49/0.55  fof(f55,plain,(
% 1.49/0.55    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 1.49/0.55    inference(superposition,[],[f28,f20])).
% 1.49/0.55  fof(f2856,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2855,f23])).
% 1.49/0.55  fof(f2855,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2854,f20])).
% 1.49/0.55  fof(f2854,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2853,f1726])).
% 1.49/0.55  fof(f1726,plain,(
% 1.49/0.55    ( ! [X10,X11,X9] : (k2_xboole_0(X9,k2_xboole_0(X10,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,X9)))) )),
% 1.49/0.55    inference(forward_demodulation,[],[f66,f36])).
% 1.49/0.55  fof(f36,plain,(
% 1.49/0.55    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 1.49/0.55    inference(superposition,[],[f23,f27])).
% 1.49/0.55  fof(f66,plain,(
% 1.49/0.55    ( ! [X10,X11,X9] : (k2_xboole_0(X9,k2_xboole_0(X10,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X9,X10))))) )),
% 1.49/0.55    inference(forward_demodulation,[],[f57,f28])).
% 1.49/0.55  fof(f57,plain,(
% 1.49/0.55    ( ! [X10,X11,X9] : (k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X9,X10))))) )),
% 1.49/0.55    inference(superposition,[],[f28,f23])).
% 1.49/0.55  fof(f2853,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2852,f55])).
% 1.49/0.55  fof(f2852,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2851,f1726])).
% 1.49/0.55  fof(f2851,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2850,f55])).
% 1.49/0.55  fof(f2850,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2849,f55])).
% 1.49/0.55  fof(f2849,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(forward_demodulation,[],[f2842,f23])).
% 1.49/0.55  fof(f2842,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 1.49/0.55    inference(superposition,[],[f697,f35])).
% 1.49/0.55  fof(f35,plain,(
% 1.49/0.55    ( ! [X4,X5,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,X5)) | ~r1_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 1.49/0.55    inference(superposition,[],[f27,f26])).
% 1.49/0.55  fof(f697,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 1.49/0.55    inference(superposition,[],[f638,f20])).
% 1.49/0.55  fof(f638,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 1.49/0.55    inference(backward_demodulation,[],[f128,f506])).
% 1.49/0.55  fof(f128,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 1.49/0.55    inference(forward_demodulation,[],[f29,f27])).
% 1.49/0.55  fof(f29,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 1.49/0.55    inference(definition_unfolding,[],[f18,f25,f25,f22])).
% 1.49/0.55  fof(f18,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.49/0.55    inference(cnf_transformation,[],[f17])).
% 1.49/0.55  fof(f17,plain,(
% 1.49/0.55    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.49/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 1.49/0.55  fof(f16,plain,(
% 1.49/0.55    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.49/0.55    introduced(choice_axiom,[])).
% 1.49/0.55  fof(f14,plain,(
% 1.49/0.55    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.49/0.55    inference(ennf_transformation,[],[f12])).
% 1.49/0.55  fof(f12,negated_conjecture,(
% 1.49/0.55    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.49/0.55    inference(negated_conjecture,[],[f11])).
% 1.49/0.55  fof(f11,conjecture,(
% 1.49/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.49/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.49/0.55  % SZS output end Proof for theBenchmark
% 1.49/0.55  % (29616)------------------------------
% 1.49/0.55  % (29616)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.55  % (29616)Termination reason: Refutation
% 1.49/0.55  
% 1.49/0.55  % (29616)Memory used [KB]: 7803
% 1.49/0.55  % (29616)Time elapsed: 0.139 s
% 1.49/0.55  % (29616)------------------------------
% 1.49/0.55  % (29616)------------------------------
% 1.49/0.55  % (29611)Success in time 0.198 s
%------------------------------------------------------------------------------
