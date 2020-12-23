%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:38 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 195 expanded)
%              Number of leaves         :   19 (  65 expanded)
%              Depth                    :   13
%              Number of atoms          :   89 ( 215 expanded)
%              Number of equality atoms :   70 ( 193 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f714,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f713])).

fof(f713,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) ),
    inference(superposition,[],[f153,f314])).

fof(f314,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f238,f299])).

fof(f299,plain,(
    ! [X10] : k5_xboole_0(X10,k1_xboole_0) = X10 ),
    inference(backward_demodulation,[],[f128,f297])).

fof(f297,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = X1 ),
    inference(forward_demodulation,[],[f252,f32])).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f252,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) = X1 ),
    inference(superposition,[],[f70,f62])).

fof(f62,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = X0 ),
    inference(superposition,[],[f54,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0 ),
    inference(definition_unfolding,[],[f27,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f35,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f70,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f41,f32])).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f128,plain,(
    ! [X10] : k5_xboole_0(k1_xboole_0,k5_xboole_0(X10,k3_xboole_0(X10,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X10,k3_xboole_0(X10,k1_xboole_0))),k1_xboole_0) ),
    inference(superposition,[],[f54,f56])).

fof(f56,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ),
    inference(definition_unfolding,[],[f30,f34,f46])).

fof(f30,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f238,plain,(
    ! [X0,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f70,f132])).

fof(f132,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f120,f60])).

fof(f60,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(resolution,[],[f36,f57])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f120,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0)) ),
    inference(superposition,[],[f56,f54])).

fof(f153,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(forward_demodulation,[],[f152,f32])).

fof(f152,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f59,f151])).

fof(f151,plain,(
    ! [X2,X3] : k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) ),
    inference(resolution,[],[f55,f36])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f52,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f48])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f47])).

fof(f47,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f44,f45])).

fof(f45,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f52,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f28,f51])).

fof(f28,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

fof(f59,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(backward_demodulation,[],[f53,f31])).

fof(f53,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(definition_unfolding,[],[f26,f51,f46,f52,f51])).

fof(f26,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).

fof(f22,plain,
    ( ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))
   => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:26:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.52  % (20745)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (20761)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.54  % (20753)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (20740)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.56  % (20742)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.56  % (20759)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (20751)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (20753)Refutation not found, incomplete strategy% (20753)------------------------------
% 0.21/0.57  % (20753)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20753)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20753)Memory used [KB]: 10618
% 0.21/0.57  % (20753)Time elapsed: 0.144 s
% 0.21/0.57  % (20753)------------------------------
% 0.21/0.57  % (20753)------------------------------
% 0.21/0.57  % (20751)Refutation not found, incomplete strategy% (20751)------------------------------
% 0.21/0.57  % (20751)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20751)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20751)Memory used [KB]: 1663
% 0.21/0.57  % (20751)Time elapsed: 0.083 s
% 0.21/0.57  % (20751)------------------------------
% 0.21/0.57  % (20751)------------------------------
% 0.21/0.57  % (20761)Refutation not found, incomplete strategy% (20761)------------------------------
% 0.21/0.57  % (20761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (20761)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (20761)Memory used [KB]: 10618
% 0.21/0.57  % (20761)Time elapsed: 0.151 s
% 0.21/0.57  % (20761)------------------------------
% 0.21/0.57  % (20761)------------------------------
% 0.21/0.57  % (20739)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.57  % (20741)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.57  % (20744)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.58  % (20743)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.66/0.58  % (20756)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.66/0.59  % (20763)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.84/0.59  % (20738)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.84/0.59  % (20764)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.84/0.59  % (20763)Refutation not found, incomplete strategy% (20763)------------------------------
% 1.84/0.59  % (20763)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.59  % (20763)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.59  
% 1.84/0.59  % (20763)Memory used [KB]: 6140
% 1.84/0.59  % (20763)Time elapsed: 0.172 s
% 1.84/0.59  % (20763)------------------------------
% 1.84/0.59  % (20763)------------------------------
% 1.84/0.59  % (20748)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.84/0.59  % (20738)Refutation not found, incomplete strategy% (20738)------------------------------
% 1.84/0.59  % (20738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.59  % (20738)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.59  
% 1.84/0.59  % (20738)Memory used [KB]: 1663
% 1.84/0.59  % (20738)Time elapsed: 0.168 s
% 1.84/0.59  % (20738)------------------------------
% 1.84/0.59  % (20738)------------------------------
% 1.84/0.60  % (20764)Refutation not found, incomplete strategy% (20764)------------------------------
% 1.84/0.60  % (20764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (20764)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.60  
% 1.84/0.60  % (20764)Memory used [KB]: 6140
% 1.84/0.60  % (20764)Time elapsed: 0.171 s
% 1.84/0.60  % (20764)------------------------------
% 1.84/0.60  % (20764)------------------------------
% 1.84/0.60  % (20766)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.84/0.60  % (20748)Refutation not found, incomplete strategy% (20748)------------------------------
% 1.84/0.60  % (20748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (20766)Refutation not found, incomplete strategy% (20766)------------------------------
% 1.84/0.60  % (20766)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.60  % (20766)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.60  
% 1.84/0.60  % (20766)Memory used [KB]: 1663
% 1.84/0.60  % (20766)Time elapsed: 0.176 s
% 1.84/0.60  % (20766)------------------------------
% 1.84/0.60  % (20766)------------------------------
% 1.84/0.60  % (20758)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.84/0.60  % (20737)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.84/0.61  % (20748)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (20748)Memory used [KB]: 6140
% 1.84/0.61  % (20748)Time elapsed: 0.170 s
% 1.84/0.61  % (20748)------------------------------
% 1.84/0.61  % (20748)------------------------------
% 1.84/0.61  % (20750)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.84/0.61  % (20757)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.84/0.61  % (20755)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.84/0.61  % (20760)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.84/0.61  % (20755)Refutation not found, incomplete strategy% (20755)------------------------------
% 1.84/0.61  % (20755)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (20755)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (20755)Memory used [KB]: 1663
% 1.84/0.61  % (20755)Time elapsed: 0.189 s
% 1.84/0.61  % (20755)------------------------------
% 1.84/0.61  % (20755)------------------------------
% 1.84/0.61  % (20749)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.84/0.61  % (20752)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.84/0.61  % (20747)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.84/0.61  % (20749)Refutation not found, incomplete strategy% (20749)------------------------------
% 1.84/0.61  % (20749)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.61  % (20749)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.61  
% 1.84/0.61  % (20749)Memory used [KB]: 10618
% 1.84/0.61  % (20749)Time elapsed: 0.191 s
% 1.84/0.61  % (20749)------------------------------
% 1.84/0.61  % (20749)------------------------------
% 1.84/0.62  % (20747)Refutation not found, incomplete strategy% (20747)------------------------------
% 1.84/0.62  % (20747)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.62  % (20747)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.62  
% 1.84/0.62  % (20747)Memory used [KB]: 10746
% 1.84/0.62  % (20747)Time elapsed: 0.190 s
% 1.84/0.62  % (20747)------------------------------
% 1.84/0.62  % (20747)------------------------------
% 1.84/0.62  % (20762)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.84/0.64  % (20754)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.15/0.64  % (20765)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 2.17/0.64  % (20762)Refutation not found, incomplete strategy% (20762)------------------------------
% 2.17/0.64  % (20762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.64  % (20762)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.64  
% 2.17/0.64  % (20762)Memory used [KB]: 6140
% 2.17/0.64  % (20762)Time elapsed: 0.221 s
% 2.17/0.64  % (20762)------------------------------
% 2.17/0.64  % (20762)------------------------------
% 2.17/0.65  % (20746)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 2.17/0.66  % (20754)Refutation not found, incomplete strategy% (20754)------------------------------
% 2.17/0.66  % (20754)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.66  % (20754)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.66  
% 2.17/0.66  % (20754)Memory used [KB]: 1663
% 2.17/0.66  % (20754)Time elapsed: 0.209 s
% 2.17/0.66  % (20754)------------------------------
% 2.17/0.66  % (20754)------------------------------
% 2.17/0.66  % (20765)Refutation not found, incomplete strategy% (20765)------------------------------
% 2.17/0.66  % (20765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.66  % (20765)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.66  
% 2.17/0.66  % (20765)Memory used [KB]: 10746
% 2.17/0.66  % (20765)Time elapsed: 0.239 s
% 2.17/0.66  % (20765)------------------------------
% 2.17/0.66  % (20765)------------------------------
% 2.17/0.69  % (20759)Refutation found. Thanks to Tanya!
% 2.17/0.69  % SZS status Theorem for theBenchmark
% 2.17/0.69  % SZS output start Proof for theBenchmark
% 2.17/0.69  fof(f714,plain,(
% 2.17/0.69    $false),
% 2.17/0.69    inference(trivial_inequality_removal,[],[f713])).
% 2.17/0.69  fof(f713,plain,(
% 2.17/0.69    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),
% 2.17/0.69    inference(superposition,[],[f153,f314])).
% 2.17/0.69  fof(f314,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.17/0.69    inference(backward_demodulation,[],[f238,f299])).
% 2.17/0.69  fof(f299,plain,(
% 2.17/0.69    ( ! [X10] : (k5_xboole_0(X10,k1_xboole_0) = X10) )),
% 2.17/0.69    inference(backward_demodulation,[],[f128,f297])).
% 2.17/0.69  fof(f297,plain,(
% 2.17/0.69    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_xboole_0(X1,k1_xboole_0))) = X1) )),
% 2.17/0.69    inference(forward_demodulation,[],[f252,f32])).
% 2.17/0.69  fof(f32,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f2])).
% 2.17/0.69  fof(f2,axiom,(
% 2.17/0.69    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.17/0.69  fof(f252,plain,(
% 2.17/0.69    ( ! [X1] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(k3_xboole_0(X1,k1_xboole_0),X1)) = X1) )),
% 2.17/0.69    inference(superposition,[],[f70,f62])).
% 2.17/0.69  fof(f62,plain,(
% 2.17/0.69    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(X0,k1_xboole_0))) = X0) )),
% 2.17/0.69    inference(superposition,[],[f54,f31])).
% 2.17/0.69  fof(f31,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f1])).
% 2.17/0.69  fof(f1,axiom,(
% 2.17/0.69    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.17/0.69  fof(f54,plain,(
% 2.17/0.69    ( ! [X0] : (k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X0))) = X0) )),
% 2.17/0.69    inference(definition_unfolding,[],[f27,f46])).
% 2.17/0.69  fof(f46,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.17/0.69    inference(definition_unfolding,[],[f35,f34])).
% 2.17/0.69  fof(f34,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.17/0.69    inference(cnf_transformation,[],[f4])).
% 2.17/0.69  fof(f4,axiom,(
% 2.17/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.17/0.69  fof(f35,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.17/0.69    inference(cnf_transformation,[],[f9])).
% 2.17/0.69  fof(f9,axiom,(
% 2.17/0.69    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.17/0.69  fof(f27,plain,(
% 2.17/0.69    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.17/0.69    inference(cnf_transformation,[],[f5])).
% 2.17/0.69  fof(f5,axiom,(
% 2.17/0.69    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.17/0.69  fof(f70,plain,(
% 2.17/0.69    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 2.17/0.69    inference(superposition,[],[f41,f32])).
% 2.17/0.69  fof(f41,plain,(
% 2.17/0.69    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.17/0.69    inference(cnf_transformation,[],[f8])).
% 2.17/0.69  fof(f8,axiom,(
% 2.17/0.69    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.17/0.69  fof(f128,plain,(
% 2.17/0.69    ( ! [X10] : (k5_xboole_0(k1_xboole_0,k5_xboole_0(X10,k3_xboole_0(X10,k1_xboole_0))) = k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(X10,k3_xboole_0(X10,k1_xboole_0))),k1_xboole_0)) )),
% 2.17/0.69    inference(superposition,[],[f54,f56])).
% 2.17/0.69  fof(f56,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))))) )),
% 2.17/0.69    inference(definition_unfolding,[],[f30,f34,f46])).
% 2.17/0.69  fof(f30,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.17/0.69    inference(cnf_transformation,[],[f7])).
% 2.17/0.69  fof(f7,axiom,(
% 2.17/0.69    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.17/0.69  fof(f238,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.17/0.69    inference(superposition,[],[f70,f132])).
% 2.17/0.69  fof(f132,plain,(
% 2.17/0.69    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.17/0.69    inference(forward_demodulation,[],[f120,f60])).
% 2.17/0.69  fof(f60,plain,(
% 2.17/0.69    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.17/0.69    inference(resolution,[],[f36,f57])).
% 2.17/0.69  fof(f57,plain,(
% 2.17/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.17/0.69    inference(equality_resolution,[],[f38])).
% 2.17/0.69  fof(f38,plain,(
% 2.17/0.69    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.17/0.69    inference(cnf_transformation,[],[f25])).
% 2.17/0.69  fof(f25,plain,(
% 2.17/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.69    inference(flattening,[],[f24])).
% 2.17/0.69  fof(f24,plain,(
% 2.17/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.69    inference(nnf_transformation,[],[f3])).
% 2.17/0.69  fof(f3,axiom,(
% 2.17/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.17/0.69  fof(f36,plain,(
% 2.17/0.69    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.17/0.69    inference(cnf_transformation,[],[f21])).
% 2.17/0.69  fof(f21,plain,(
% 2.17/0.69    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.17/0.69    inference(ennf_transformation,[],[f6])).
% 2.17/0.69  fof(f6,axiom,(
% 2.17/0.69    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.17/0.69  fof(f120,plain,(
% 2.17/0.69    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X0))) )),
% 2.17/0.69    inference(superposition,[],[f56,f54])).
% 2.17/0.69  fof(f153,plain,(
% 2.17/0.69    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.17/0.69    inference(forward_demodulation,[],[f152,f32])).
% 2.17/0.69  fof(f152,plain,(
% 2.17/0.69    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.17/0.69    inference(backward_demodulation,[],[f59,f151])).
% 2.17/0.69  fof(f151,plain,(
% 2.17/0.69    ( ! [X2,X3] : (k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = k3_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3))) )),
% 2.17/0.69    inference(resolution,[],[f55,f36])).
% 2.17/0.69  fof(f55,plain,(
% 2.17/0.69    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.17/0.69    inference(definition_unfolding,[],[f29,f52,f51])).
% 2.17/0.69  fof(f51,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.17/0.69    inference(definition_unfolding,[],[f33,f50])).
% 2.17/0.69  fof(f50,plain,(
% 2.17/0.69    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.17/0.69    inference(definition_unfolding,[],[f40,f49])).
% 2.17/0.69  fof(f49,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.17/0.69    inference(definition_unfolding,[],[f42,f48])).
% 2.17/0.69  fof(f48,plain,(
% 2.17/0.69    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.17/0.69    inference(definition_unfolding,[],[f43,f47])).
% 2.17/0.69  fof(f47,plain,(
% 2.17/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.17/0.69    inference(definition_unfolding,[],[f44,f45])).
% 2.17/0.69  fof(f45,plain,(
% 2.17/0.69    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f16])).
% 2.17/0.69  fof(f16,axiom,(
% 2.17/0.69    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.17/0.69  fof(f44,plain,(
% 2.17/0.69    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f15])).
% 2.17/0.69  fof(f15,axiom,(
% 2.17/0.69    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.17/0.69  fof(f43,plain,(
% 2.17/0.69    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f14])).
% 2.17/0.69  fof(f14,axiom,(
% 2.17/0.69    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.17/0.69  fof(f42,plain,(
% 2.17/0.69    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f13])).
% 2.17/0.69  fof(f13,axiom,(
% 2.17/0.69    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.17/0.69  fof(f40,plain,(
% 2.17/0.69    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f12])).
% 2.17/0.69  fof(f12,axiom,(
% 2.17/0.69    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.17/0.69  fof(f33,plain,(
% 2.17/0.69    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f11])).
% 2.17/0.69  fof(f11,axiom,(
% 2.17/0.69    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.17/0.69  fof(f52,plain,(
% 2.17/0.69    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.17/0.69    inference(definition_unfolding,[],[f28,f51])).
% 2.17/0.69  fof(f28,plain,(
% 2.17/0.69    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f10])).
% 2.17/0.69  fof(f10,axiom,(
% 2.17/0.69    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.17/0.69  fof(f29,plain,(
% 2.17/0.69    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))) )),
% 2.17/0.69    inference(cnf_transformation,[],[f17])).
% 2.17/0.69  fof(f17,axiom,(
% 2.17/0.69    ! [X0,X1] : r1_tarski(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).
% 2.17/0.69  fof(f59,plain,(
% 2.17/0.69    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 2.17/0.69    inference(backward_demodulation,[],[f53,f31])).
% 2.17/0.69  fof(f53,plain,(
% 2.17/0.69    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 2.17/0.69    inference(definition_unfolding,[],[f26,f51,f46,f52,f51])).
% 2.17/0.69  fof(f26,plain,(
% 2.17/0.69    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 2.17/0.69    inference(cnf_transformation,[],[f23])).
% 2.17/0.69  fof(f23,plain,(
% 2.17/0.69    k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 2.17/0.69    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f22])).
% 2.17/0.70  fof(f22,plain,(
% 2.17/0.70    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1)) => k2_tarski(sK0,sK1) != k2_xboole_0(k1_tarski(sK0),k2_tarski(sK0,sK1))),
% 2.17/0.70    introduced(choice_axiom,[])).
% 2.17/0.70  fof(f20,plain,(
% 2.17/0.70    ? [X0,X1] : k2_tarski(X0,X1) != k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.17/0.70    inference(ennf_transformation,[],[f19])).
% 2.17/0.70  fof(f19,negated_conjecture,(
% 2.17/0.70    ~! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.17/0.70    inference(negated_conjecture,[],[f18])).
% 2.17/0.70  fof(f18,conjecture,(
% 2.17/0.70    ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k2_tarski(X0,X1))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_zfmisc_1)).
% 2.17/0.70  % SZS output end Proof for theBenchmark
% 2.17/0.70  % (20759)------------------------------
% 2.17/0.70  % (20759)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.70  % (20759)Termination reason: Refutation
% 2.17/0.70  
% 2.17/0.70  % (20759)Memory used [KB]: 7291
% 2.17/0.70  % (20759)Time elapsed: 0.183 s
% 2.17/0.70  % (20759)------------------------------
% 2.17/0.70  % (20759)------------------------------
% 2.42/0.70  % (20736)Success in time 0.335 s
%------------------------------------------------------------------------------
