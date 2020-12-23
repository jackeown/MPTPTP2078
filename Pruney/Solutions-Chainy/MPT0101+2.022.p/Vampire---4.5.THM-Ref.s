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
% DateTime   : Thu Dec  3 12:31:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 155 expanded)
%              Number of leaves         :   12 (  51 expanded)
%              Depth                    :   24
%              Number of atoms          :   87 ( 184 expanded)
%              Number of equality atoms :   53 ( 144 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1272,plain,(
    $false ),
    inference(resolution,[],[f1270,f19])).

fof(f19,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1270,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK1,sK0),sK0) ),
    inference(resolution,[],[f1239,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1239,plain,(
    ~ r1_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(resolution,[],[f1230,f473])).

fof(f473,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(k4_xboole_0(X3,X5),X4)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(superposition,[],[f58,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f28,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f58,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X1,X0)),X1) ),
    inference(superposition,[],[f40,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f40,plain,(
    ! [X10,X11,X9] : r1_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X11) ),
    inference(superposition,[],[f19,f28])).

fof(f1230,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(trivial_inequality_removal,[],[f1229])).

fof(f1229,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1228,f441])).

fof(f441,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f29,f418])).

fof(f418,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f393,f21])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f393,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f372,f20])).

fof(f372,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f74,f21])).

fof(f74,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f31,f20])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1228,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1227,f47])).

fof(f47,plain,(
    ! [X4,X5,X3] : k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4)) ),
    inference(superposition,[],[f29,f20])).

fof(f1227,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK0))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1226,f21])).

fof(f1226,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1225,f20])).

fof(f1225,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1224,f826])).

fof(f826,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X9,k2_xboole_0(X10,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,X9))) ),
    inference(forward_demodulation,[],[f56,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2))) ),
    inference(superposition,[],[f21,f28])).

fof(f56,plain,(
    ! [X10,X11,X9] : k2_xboole_0(X9,k2_xboole_0(X10,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X9,X10)))) ),
    inference(forward_demodulation,[],[f49,f29])).

fof(f49,plain,(
    ! [X10,X11,X9] : k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X9,X10)))) ),
    inference(superposition,[],[f29,f21])).

fof(f1224,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1223,f47])).

fof(f1223,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1222,f826])).

fof(f1222,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1221,f47])).

fof(f1221,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1220,f47])).

fof(f1220,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1219,f21])).

fof(f1219,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(forward_demodulation,[],[f1214,f20])).

fof(f1214,plain,
    ( k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | ~ r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0)) ),
    inference(superposition,[],[f1129,f36])).

fof(f36,plain,(
    ! [X4,X5,X3] :
      ( k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,X5))
      | ~ r1_xboole_0(k4_xboole_0(X3,X4),X5) ) ),
    inference(superposition,[],[f28,f26])).

fof(f1129,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f89,f441])).

fof(f89,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))) ),
    inference(forward_demodulation,[],[f30,f28])).

fof(f30,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))) ),
    inference(definition_unfolding,[],[f18,f24,f24,f22])).

fof(f24,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f18,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).

fof(f15,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:16:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.44  % (32559)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (32555)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (32566)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (32571)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (32560)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (32565)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (32562)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (32569)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (32557)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (32559)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f1272,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(resolution,[],[f1270,f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 0.22/0.48  fof(f1270,plain,(
% 0.22/0.48    ~r1_xboole_0(k4_xboole_0(sK1,sK0),sK0)),
% 0.22/0.48    inference(resolution,[],[f1239,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.22/0.48  fof(f1239,plain,(
% 0.22/0.48    ~r1_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.22/0.48    inference(resolution,[],[f1230,f473])).
% 0.22/0.48  fof(f473,plain,(
% 0.22/0.48    ( ! [X4,X5,X3] : (r1_xboole_0(k4_xboole_0(X3,X5),X4) | ~r1_xboole_0(X3,X4)) )),
% 0.22/0.48    inference(superposition,[],[f58,f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(superposition,[],[f28,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.22/0.48    inference(nnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.22/0.48  fof(f58,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(X2,k2_xboole_0(X1,X0)),X1)) )),
% 0.22/0.48    inference(superposition,[],[f40,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X10,X11,X9] : (r1_xboole_0(k4_xboole_0(X9,k2_xboole_0(X10,X11)),X11)) )),
% 0.22/0.48    inference(superposition,[],[f19,f28])).
% 0.22/0.48  fof(f1230,plain,(
% 0.22/0.48    ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.48    inference(trivial_inequality_removal,[],[f1229])).
% 0.22/0.48  fof(f1229,plain,(
% 0.22/0.48    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,sK1) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.48    inference(forward_demodulation,[],[f1228,f441])).
% 0.22/0.48  fof(f441,plain,(
% 0.22/0.48    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 0.22/0.48    inference(superposition,[],[f29,f418])).
% 0.22/0.48  fof(f418,plain,(
% 0.22/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.22/0.48    inference(superposition,[],[f393,f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.22/0.49  fof(f393,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) )),
% 0.22/0.49    inference(superposition,[],[f372,f20])).
% 0.22/0.49  fof(f372,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 0.22/0.49    inference(superposition,[],[f74,f21])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 0.22/0.49    inference(superposition,[],[f31,f20])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.49    inference(definition_unfolding,[],[f23,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.22/0.49  fof(f1228,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK0,sK1)) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1227,f47])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k2_xboole_0(X3,k2_xboole_0(X4,X5)) = k2_xboole_0(X5,k2_xboole_0(X3,X4))) )),
% 0.22/0.49    inference(superposition,[],[f29,f20])).
% 0.22/0.49  fof(f1227,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK1,sK0)) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1226,f21])).
% 0.22/0.49  fof(f1226,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(sK0,sK1))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1225,f20])).
% 0.22/0.49  fof(f1225,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK1)) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1224,f826])).
% 0.22/0.49  fof(f826,plain,(
% 0.22/0.49    ( ! [X10,X11,X9] : (k2_xboole_0(X9,k2_xboole_0(X10,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,X9)))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f56,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (k2_xboole_0(X2,k4_xboole_0(X0,X1)) = k2_xboole_0(X2,k4_xboole_0(X0,k2_xboole_0(X1,X2)))) )),
% 0.22/0.49    inference(superposition,[],[f21,f28])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ( ! [X10,X11,X9] : (k2_xboole_0(X9,k2_xboole_0(X10,X11)) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X9,X10))))) )),
% 0.22/0.49    inference(forward_demodulation,[],[f49,f29])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X10,X11,X9] : (k2_xboole_0(k2_xboole_0(X9,X10),X11) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(X11,k2_xboole_0(X9,X10))))) )),
% 0.22/0.49    inference(superposition,[],[f29,f21])).
% 0.22/0.49  fof(f1224,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1223,f47])).
% 0.22/0.49  fof(f1223,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),sK0)) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1222,f826])).
% 0.22/0.49  fof(f1222,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK1,sK0),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1221,f47])).
% 0.22/0.49  fof(f1221,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK1,sK0),k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK0,sK1))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1220,f47])).
% 0.22/0.49  fof(f1220,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1219,f21])).
% 0.22/0.49  fof(f1219,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(forward_demodulation,[],[f1214,f20])).
% 0.22/0.49  fof(f1214,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | ~r1_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k4_xboole_0(sK1,sK0))),
% 0.22/0.49    inference(superposition,[],[f1129,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X4,X5,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k2_xboole_0(X4,X5)) | ~r1_xboole_0(k4_xboole_0(X3,X4),X5)) )),
% 0.22/0.49    inference(superposition,[],[f28,f26])).
% 0.22/0.49  fof(f1129,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.22/0.49    inference(backward_demodulation,[],[f89,f441])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)))))),
% 0.22/0.49    inference(forward_demodulation,[],[f30,f28])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))))),
% 0.22/0.49    inference(definition_unfolding,[],[f18,f24,f24,f22])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.22/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 0.22/0.49    introduced(choice_axiom,[])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,negated_conjecture,(
% 0.22/0.49    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.49    inference(negated_conjecture,[],[f11])).
% 0.22/0.49  fof(f11,conjecture,(
% 0.22/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (32559)------------------------------
% 0.22/0.49  % (32559)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (32559)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (32559)Memory used [KB]: 7036
% 0.22/0.49  % (32559)Time elapsed: 0.047 s
% 0.22/0.49  % (32559)------------------------------
% 0.22/0.49  % (32559)------------------------------
% 0.22/0.49  % (32552)Success in time 0.125 s
%------------------------------------------------------------------------------
