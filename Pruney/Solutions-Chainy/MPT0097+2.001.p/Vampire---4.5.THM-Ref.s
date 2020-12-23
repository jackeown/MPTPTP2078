%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:47 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 338 expanded)
%              Number of leaves         :    9 ( 103 expanded)
%              Depth                    :   15
%              Number of atoms          :   58 ( 479 expanded)
%              Number of equality atoms :   43 ( 305 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1700,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1682])).

fof(f1682,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f609,f1606])).

fof(f1606,plain,(
    ! [X87,X86] : k4_xboole_0(X86,X87) = k4_xboole_0(k4_xboole_0(X86,X87),X87) ),
    inference(forward_demodulation,[],[f1605,f364])).

fof(f364,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X0,X1),X0),X1) ),
    inference(superposition,[],[f358,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f358,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 ),
    inference(superposition,[],[f284,f270])).

fof(f270,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f252,f19])).

fof(f19,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f252,plain,(
    ! [X4,X3] : k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3 ),
    inference(forward_demodulation,[],[f251,f27])).

fof(f27,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(resolution,[],[f21,f17])).

fof(f17,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f251,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f225,f40])).

fof(f40,plain,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f34,f27])).

fof(f34,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f19,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f225,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k3_xboole_0(k1_xboole_0,X4)) = k2_xboole_0(X3,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f26,f27])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f284,plain,(
    ! [X7] : k2_xboole_0(k3_xboole_0(X7,X7),k1_xboole_0) = X7 ),
    inference(superposition,[],[f32,f252])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0 ),
    inference(superposition,[],[f20,f19])).

fof(f1605,plain,(
    ! [X87,X86] : k4_xboole_0(X86,X87) = k4_xboole_0(k4_xboole_0(k3_xboole_0(k4_xboole_0(X86,X87),X86),X87),X87) ),
    inference(forward_demodulation,[],[f1604,f25])).

fof(f1604,plain,(
    ! [X87,X86] : k4_xboole_0(X86,X87) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X86,X87),k4_xboole_0(X86,X87)),X87) ),
    inference(forward_demodulation,[],[f1542,f415])).

fof(f415,plain,(
    ! [X8,X7] : k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7) ),
    inference(superposition,[],[f288,f264])).

fof(f264,plain,(
    ! [X4,X3] : k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3 ),
    inference(forward_demodulation,[],[f263,f27])).

fof(f263,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(forward_demodulation,[],[f236,f18])).

fof(f18,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f236,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k3_xboole_0(X4,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X3,X4),X3) ),
    inference(superposition,[],[f26,f27])).

fof(f288,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 ),
    inference(superposition,[],[f270,f32])).

fof(f1542,plain,(
    ! [X87,X86] : k4_xboole_0(X86,X87) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X86,X87),k3_xboole_0(k4_xboole_0(X86,X87),X86)),X87) ),
    inference(superposition,[],[f364,f364])).

fof(f609,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK1) ),
    inference(superposition,[],[f28,f313])).

fof(f313,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f305,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f31,f27])).

fof(f31,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0 ),
    inference(superposition,[],[f20,f18])).

fof(f305,plain,(
    ! [X4,X3] : k4_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f26,f285])).

fof(f285,plain,(
    ! [X9] : k1_xboole_0 = k4_xboole_0(X9,X9) ),
    inference(superposition,[],[f19,f252])).

fof(f28,plain,(
    k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    inference(resolution,[],[f22,f16])).

fof(f16,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)
   => ~ r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : ~ r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:33:59 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.44  % (21115)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.21/0.45  % (21117)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.21/0.45  % (21116)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.21/0.47  % (21114)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.21/0.47  % (21122)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 0.21/0.48  % (21115)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f1700,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(trivial_inequality_removal,[],[f1682])).
% 0.21/0.48  fof(f1682,plain,(
% 0.21/0.48    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 0.21/0.48    inference(superposition,[],[f609,f1606])).
% 0.21/0.48  fof(f1606,plain,(
% 0.21/0.48    ( ! [X87,X86] : (k4_xboole_0(X86,X87) = k4_xboole_0(k4_xboole_0(X86,X87),X87)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f1605,f364])).
% 0.21/0.48  fof(f364,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X0,X1),X0),X1)) )),
% 0.21/0.48    inference(superposition,[],[f358,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    ( ! [X1] : (k3_xboole_0(X1,X1) = X1) )),
% 0.21/0.48    inference(superposition,[],[f284,f270])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(superposition,[],[f252,f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 0.21/0.48  fof(f252,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k2_xboole_0(X3,k4_xboole_0(X3,X4)) = X3) )),
% 0.21/0.48    inference(forward_demodulation,[],[f251,f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(resolution,[],[f21,f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.21/0.48    inference(nnf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f225,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2)) )),
% 0.21/0.48    inference(superposition,[],[f34,f27])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0)) )),
% 0.21/0.48    inference(superposition,[],[f19,f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k4_xboole_0(X3,k3_xboole_0(k1_xboole_0,X4)) = k2_xboole_0(X3,k4_xboole_0(X3,X4))) )),
% 0.21/0.48    inference(superposition,[],[f26,f27])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    ( ! [X7] : (k2_xboole_0(k3_xboole_0(X7,X7),k1_xboole_0) = X7) )),
% 0.21/0.48    inference(superposition,[],[f32,f252])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0) )),
% 0.21/0.48    inference(superposition,[],[f20,f19])).
% 0.21/0.48  fof(f1605,plain,(
% 0.21/0.48    ( ! [X87,X86] : (k4_xboole_0(X86,X87) = k4_xboole_0(k4_xboole_0(k3_xboole_0(k4_xboole_0(X86,X87),X86),X87),X87)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f1604,f25])).
% 0.21/0.48  fof(f1604,plain,(
% 0.21/0.48    ( ! [X87,X86] : (k4_xboole_0(X86,X87) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X86,X87),k4_xboole_0(X86,X87)),X87)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f1542,f415])).
% 0.21/0.48  fof(f415,plain,(
% 0.21/0.48    ( ! [X8,X7] : (k4_xboole_0(X7,X8) = k3_xboole_0(k4_xboole_0(X7,X8),X7)) )),
% 0.21/0.48    inference(superposition,[],[f288,f264])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X3,X4),X3) = X3) )),
% 0.21/0.48    inference(forward_demodulation,[],[f263,f27])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k4_xboole_0(X3,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 0.21/0.48    inference(forward_demodulation,[],[f236,f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f236,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k4_xboole_0(X3,k3_xboole_0(X4,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X3,X4),X3)) )),
% 0.21/0.48    inference(superposition,[],[f26,f27])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2) )),
% 0.21/0.48    inference(superposition,[],[f270,f32])).
% 0.21/0.48  fof(f1542,plain,(
% 0.21/0.48    ( ! [X87,X86] : (k4_xboole_0(X86,X87) = k4_xboole_0(k3_xboole_0(k4_xboole_0(X86,X87),k3_xboole_0(k4_xboole_0(X86,X87),X86)),X87)) )),
% 0.21/0.48    inference(superposition,[],[f364,f364])).
% 0.21/0.48  fof(f609,plain,(
% 0.21/0.48    k4_xboole_0(sK0,sK1) != k4_xboole_0(k4_xboole_0(sK0,sK1),sK1)),
% 0.21/0.48    inference(superposition,[],[f28,f313])).
% 0.21/0.48  fof(f313,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 0.21/0.48    inference(forward_demodulation,[],[f305,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f31,f27])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(k1_xboole_0,k4_xboole_0(X0,k1_xboole_0)) = X0) )),
% 0.21/0.48    inference(superposition,[],[f20,f18])).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    ( ! [X4,X3] : (k4_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X4))) )),
% 0.21/0.48    inference(superposition,[],[f26,f285])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ( ! [X9] : (k1_xboole_0 = k4_xboole_0(X9,X9)) )),
% 0.21/0.48    inference(superposition,[],[f19,f252])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)) != k4_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.48    inference(resolution,[],[f22,f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ~r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ~r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1) => ~r1_xboole_0(k4_xboole_0(sK0,k3_xboole_0(sK0,sK1)),sK1)),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0,X1] : ~r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,k3_xboole_0(X0,X1)),X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21115)------------------------------
% 0.21/0.48  % (21115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21115)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21115)Memory used [KB]: 7164
% 0.21/0.48  % (21115)Time elapsed: 0.067 s
% 0.21/0.48  % (21115)------------------------------
% 0.21/0.48  % (21115)------------------------------
% 0.21/0.48  % (21110)Success in time 0.12 s
%------------------------------------------------------------------------------
