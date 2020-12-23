%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:16 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :   36 (  51 expanded)
%              Number of leaves         :   10 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   37 (  52 expanded)
%              Number of equality atoms :   36 (  51 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f393,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f392])).

fof(f392,plain,(
    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1) ),
    inference(superposition,[],[f352,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f352,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f351,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f24,f22])).

fof(f24,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f351,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK0)) ),
    inference(backward_demodulation,[],[f41,f350])).

fof(f350,plain,(
    ! [X28,X27] : k2_xboole_0(k4_xboole_0(X27,X28),X27) = X27 ),
    inference(forward_demodulation,[],[f349,f23])).

fof(f23,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f349,plain,(
    ! [X28,X27] : k4_xboole_0(X27,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X27,X28),X27) ),
    inference(forward_demodulation,[],[f348,f42])).

fof(f348,plain,(
    ! [X28,X27] : k2_xboole_0(k4_xboole_0(X27,X28),X27) = k4_xboole_0(X27,k4_xboole_0(X28,X28)) ),
    inference(forward_demodulation,[],[f284,f23])).

fof(f284,plain,(
    ! [X28,X27] : k4_xboole_0(X27,k4_xboole_0(X28,k4_xboole_0(X28,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X27,X28),X27) ),
    inference(superposition,[],[f38,f23])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(definition_unfolding,[],[f33,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

fof(f41,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0))) ),
    inference(backward_demodulation,[],[f39,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f39,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(backward_demodulation,[],[f35,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f27,f25])).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f35,plain,(
    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0)) ),
    inference(definition_unfolding,[],[f20,f29,f25])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f20,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:52:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.52  % (13607)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (13621)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (13613)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (13596)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (13599)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.41/0.56  % (13595)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.41/0.56  % (13607)Refutation found. Thanks to Tanya!
% 1.41/0.56  % SZS status Theorem for theBenchmark
% 1.41/0.56  % (13595)Refutation not found, incomplete strategy% (13595)------------------------------
% 1.41/0.56  % (13595)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (13595)Termination reason: Refutation not found, incomplete strategy
% 1.41/0.56  
% 1.41/0.56  % (13595)Memory used [KB]: 1663
% 1.41/0.56  % (13595)Time elapsed: 0.125 s
% 1.41/0.56  % (13595)------------------------------
% 1.41/0.56  % (13595)------------------------------
% 1.41/0.56  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f393,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(trivial_inequality_removal,[],[f392])).
% 1.41/0.56  fof(f392,plain,(
% 1.41/0.56    k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)),
% 1.41/0.56    inference(superposition,[],[f352,f22])).
% 1.41/0.56  fof(f22,plain,(
% 1.41/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f3])).
% 1.41/0.56  fof(f3,axiom,(
% 1.41/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.41/0.56  fof(f352,plain,(
% 1.41/0.56    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k1_xboole_0)),
% 1.41/0.56    inference(forward_demodulation,[],[f351,f42])).
% 1.41/0.56  fof(f42,plain,(
% 1.41/0.56    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.41/0.56    inference(superposition,[],[f24,f22])).
% 1.41/0.56  fof(f24,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f8])).
% 1.41/0.56  fof(f8,axiom,(
% 1.41/0.56    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 1.41/0.56  fof(f351,plain,(
% 1.41/0.56    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,sK0))),
% 1.41/0.56    inference(backward_demodulation,[],[f41,f350])).
% 1.41/0.56  fof(f350,plain,(
% 1.41/0.56    ( ! [X28,X27] : (k2_xboole_0(k4_xboole_0(X27,X28),X27) = X27) )),
% 1.41/0.56    inference(forward_demodulation,[],[f349,f23])).
% 1.41/0.56  fof(f23,plain,(
% 1.41/0.56    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.41/0.56    inference(cnf_transformation,[],[f5])).
% 1.41/0.56  fof(f5,axiom,(
% 1.41/0.56    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 1.41/0.56  fof(f349,plain,(
% 1.41/0.56    ( ! [X28,X27] : (k4_xboole_0(X27,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X27,X28),X27)) )),
% 1.41/0.56    inference(forward_demodulation,[],[f348,f42])).
% 1.41/0.56  fof(f348,plain,(
% 1.41/0.56    ( ! [X28,X27] : (k2_xboole_0(k4_xboole_0(X27,X28),X27) = k4_xboole_0(X27,k4_xboole_0(X28,X28))) )),
% 1.41/0.56    inference(forward_demodulation,[],[f284,f23])).
% 1.41/0.56  fof(f284,plain,(
% 1.41/0.56    ( ! [X28,X27] : (k4_xboole_0(X27,k4_xboole_0(X28,k4_xboole_0(X28,k1_xboole_0))) = k2_xboole_0(k4_xboole_0(X27,X28),X27)) )),
% 1.41/0.56    inference(superposition,[],[f38,f23])).
% 1.41/0.56  fof(f38,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 1.41/0.56    inference(definition_unfolding,[],[f33,f25])).
% 1.41/0.56  fof(f25,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f10])).
% 1.41/0.56  fof(f10,axiom,(
% 1.41/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.41/0.56  fof(f33,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f2])).
% 1.41/0.56  fof(f2,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).
% 1.41/0.56  fof(f41,plain,(
% 1.41/0.56    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k2_xboole_0(k4_xboole_0(sK0,sK1),sK0)))),
% 1.41/0.56    inference(backward_demodulation,[],[f39,f32])).
% 1.41/0.56  fof(f32,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f7])).
% 1.41/0.56  fof(f7,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.41/0.56  fof(f39,plain,(
% 1.41/0.56    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 1.41/0.56    inference(backward_demodulation,[],[f35,f36])).
% 1.41/0.56  fof(f36,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.41/0.56    inference(definition_unfolding,[],[f27,f25])).
% 1.41/0.56  fof(f27,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f9])).
% 1.41/0.56  fof(f9,axiom,(
% 1.41/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.41/0.56  fof(f35,plain,(
% 1.41/0.56    k4_xboole_0(sK0,sK1) != k2_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)),sK0))),
% 1.41/0.56    inference(definition_unfolding,[],[f20,f29,f25])).
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).
% 1.41/0.56  fof(f20,plain,(
% 1.41/0.56    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.41/0.56    inference(cnf_transformation,[],[f19])).
% 1.41/0.56  fof(f19,plain,(
% 1.41/0.56    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 1.41/0.56  fof(f18,plain,(
% 1.41/0.56    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f16,plain,(
% 1.41/0.56    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.56    inference(ennf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,negated_conjecture,(
% 1.41/0.56    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.56    inference(negated_conjecture,[],[f14])).
% 1.41/0.56  fof(f14,conjecture,(
% 1.41/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.41/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (13607)------------------------------
% 1.41/0.56  % (13607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (13607)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (13607)Memory used [KB]: 6524
% 1.41/0.56  % (13607)Time elapsed: 0.141 s
% 1.41/0.56  % (13607)------------------------------
% 1.41/0.56  % (13607)------------------------------
% 1.41/0.56  % (13594)Success in time 0.197 s
%------------------------------------------------------------------------------
