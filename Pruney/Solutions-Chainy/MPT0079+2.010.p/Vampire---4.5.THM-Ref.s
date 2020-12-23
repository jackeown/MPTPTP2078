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
% DateTime   : Thu Dec  3 12:30:52 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 366 expanded)
%              Number of leaves         :   14 ( 114 expanded)
%              Depth                    :   28
%              Number of atoms          :  113 ( 637 expanded)
%              Number of equality atoms :   82 ( 439 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1134,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f1132])).

fof(f1132,plain,(
    sK1 != sK1 ),
    inference(superposition,[],[f24,f987])).

fof(f987,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f972,f26])).

fof(f26,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f972,plain,(
    sK2 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f584,f971])).

fof(f971,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f970,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f970,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(sK1,sK2) ),
    inference(forward_demodulation,[],[f969,f44])).

fof(f44,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f39,f26])).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f25,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f25,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f969,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK3,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f968,f206])).

fof(f206,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5)) ),
    inference(forward_demodulation,[],[f196,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f196,plain,(
    ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6))) ),
    inference(superposition,[],[f38,f44])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f968,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,k2_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f967,f21])).

fof(f21,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f967,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,k2_xboole_0(sK2,sK3))) ),
    inference(forward_demodulation,[],[f898,f38])).

fof(f898,plain,(
    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3)) ),
    inference(superposition,[],[f339,f768])).

fof(f768,plain,(
    sK3 = k4_xboole_0(sK3,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f749,f412])).

fof(f412,plain,(
    sK3 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f346,f47])).

fof(f47,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f30,f27])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f346,plain,(
    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f41,f153])).

fof(f153,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)) ),
    inference(resolution,[],[f43,f23])).

fof(f23,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f34,f31])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f33,f31])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f749,plain,(
    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f429,f634])).

fof(f634,plain,(
    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f633,f610])).

fof(f610,plain,(
    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f41,f584])).

fof(f633,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f632,f30])).

fof(f632,plain,(
    k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) ),
    inference(forward_demodulation,[],[f611,f30])).

fof(f611,plain,(
    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2) ),
    inference(superposition,[],[f32,f584])).

fof(f429,plain,(
    ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0) ),
    inference(superposition,[],[f38,f412])).

fof(f339,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0 ),
    inference(superposition,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f29,f31,f31])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f584,plain,(
    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(forward_demodulation,[],[f577,f26])).

fof(f577,plain,(
    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2)) ),
    inference(superposition,[],[f40,f557])).

fof(f557,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f400,f464])).

fof(f464,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f206,f118])).

fof(f118,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2) ),
    inference(resolution,[],[f72,f45])).

fof(f45,plain,(
    r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    inference(superposition,[],[f28,f21])).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f72,plain,(
    ! [X2,X3] :
      ( ~ r1_tarski(X2,X3)
      | k2_xboole_0(X3,X2) = X3 ) ),
    inference(forward_demodulation,[],[f66,f27])).

fof(f66,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,X2) = k2_xboole_0(X3,k1_xboole_0)
      | ~ r1_tarski(X2,X3) ) ),
    inference(superposition,[],[f32,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f400,plain,(
    ! [X0] : k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0) ),
    inference(superposition,[],[f38,f381])).

fof(f381,plain,(
    sK2 = k4_xboole_0(sK2,sK0) ),
    inference(superposition,[],[f345,f47])).

fof(f345,plain,(
    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0)) ),
    inference(superposition,[],[f41,f152])).

fof(f152,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f43,f22])).

fof(f22,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f24,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:47:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.47  % (14342)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.47  % (14335)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.51  % (14339)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.24/0.53  % (14349)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.24/0.53  % (14337)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.24/0.53  % (14355)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.24/0.53  % (14340)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.24/0.53  % (14365)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.24/0.54  % (14336)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.24/0.54  % (14346)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.24/0.54  % (14358)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.24/0.54  % (14350)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.24/0.54  % (14338)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.24/0.54  % (14351)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.24/0.54  % (14361)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.24/0.54  % (14359)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.24/0.54  % (14351)Refutation not found, incomplete strategy% (14351)------------------------------
% 1.24/0.54  % (14351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (14351)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (14351)Memory used [KB]: 6140
% 1.24/0.54  % (14351)Time elapsed: 0.002 s
% 1.24/0.54  % (14351)------------------------------
% 1.24/0.54  % (14351)------------------------------
% 1.24/0.54  % (14363)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.24/0.54  % (14358)Refutation not found, incomplete strategy% (14358)------------------------------
% 1.24/0.54  % (14358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.24/0.54  % (14358)Termination reason: Refutation not found, incomplete strategy
% 1.24/0.54  
% 1.24/0.54  % (14358)Memory used [KB]: 10618
% 1.24/0.54  % (14358)Time elapsed: 0.099 s
% 1.24/0.54  % (14358)------------------------------
% 1.24/0.54  % (14358)------------------------------
% 1.24/0.54  % (14364)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.45/0.54  % (14353)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.54  % (14352)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.54  % (14353)Refutation not found, incomplete strategy% (14353)------------------------------
% 1.45/0.54  % (14353)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.54  % (14353)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.54  
% 1.45/0.54  % (14353)Memory used [KB]: 10618
% 1.45/0.54  % (14353)Time elapsed: 0.138 s
% 1.45/0.54  % (14353)------------------------------
% 1.45/0.54  % (14353)------------------------------
% 1.45/0.54  % (14341)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.45/0.55  % (14357)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.45/0.55  % (14345)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.45/0.55  % (14362)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.55  % (14347)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.55  % (14356)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.55  % (14347)Refutation not found, incomplete strategy% (14347)------------------------------
% 1.45/0.55  % (14347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (14347)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (14347)Memory used [KB]: 10618
% 1.45/0.55  % (14347)Time elapsed: 0.142 s
% 1.45/0.55  % (14347)------------------------------
% 1.45/0.55  % (14347)------------------------------
% 1.45/0.55  % (14344)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.45/0.55  % (14360)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.55  % (14354)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.45/0.56  % (14348)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.56  % (14346)Refutation not found, incomplete strategy% (14346)------------------------------
% 1.45/0.56  % (14346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (14346)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (14346)Memory used [KB]: 10618
% 1.45/0.57  % (14346)Time elapsed: 0.158 s
% 1.45/0.57  % (14346)------------------------------
% 1.45/0.57  % (14346)------------------------------
% 1.45/0.59  % (14348)Refutation found. Thanks to Tanya!
% 1.45/0.59  % SZS status Theorem for theBenchmark
% 1.45/0.60  % SZS output start Proof for theBenchmark
% 1.45/0.60  fof(f1134,plain,(
% 1.45/0.60    $false),
% 1.45/0.60    inference(trivial_inequality_removal,[],[f1132])).
% 1.45/0.60  fof(f1132,plain,(
% 1.45/0.60    sK1 != sK1),
% 1.45/0.60    inference(superposition,[],[f24,f987])).
% 1.45/0.60  fof(f987,plain,(
% 1.45/0.60    sK1 = sK2),
% 1.45/0.60    inference(forward_demodulation,[],[f972,f26])).
% 1.45/0.60  fof(f26,plain,(
% 1.45/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.60    inference(cnf_transformation,[],[f8])).
% 1.45/0.60  fof(f8,axiom,(
% 1.45/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.45/0.60  fof(f972,plain,(
% 1.45/0.60    sK2 = k4_xboole_0(sK1,k1_xboole_0)),
% 1.45/0.60    inference(backward_demodulation,[],[f584,f971])).
% 1.45/0.60  fof(f971,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f970,f27])).
% 1.45/0.60  fof(f27,plain,(
% 1.45/0.60    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.45/0.60    inference(cnf_transformation,[],[f5])).
% 1.45/0.60  fof(f5,axiom,(
% 1.45/0.60    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.45/0.60  fof(f970,plain,(
% 1.45/0.60    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(sK1,sK2)),
% 1.45/0.60    inference(forward_demodulation,[],[f969,f44])).
% 1.45/0.60  fof(f44,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.45/0.60    inference(backward_demodulation,[],[f39,f26])).
% 1.45/0.60  fof(f39,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.45/0.60    inference(definition_unfolding,[],[f25,f31])).
% 1.45/0.60  fof(f31,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f10])).
% 1.45/0.60  fof(f10,axiom,(
% 1.45/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.45/0.60  fof(f25,plain,(
% 1.45/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f6])).
% 1.45/0.60  fof(f6,axiom,(
% 1.45/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.45/0.60  fof(f969,plain,(
% 1.45/0.60    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK3,sK3),k1_xboole_0)),
% 1.45/0.60    inference(forward_demodulation,[],[f968,f206])).
% 1.45/0.60  fof(f206,plain,(
% 1.45/0.60    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,X5))) )),
% 1.45/0.60    inference(forward_demodulation,[],[f196,f32])).
% 1.45/0.60  fof(f32,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f7])).
% 1.45/0.60  fof(f7,axiom,(
% 1.45/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.45/0.60  fof(f196,plain,(
% 1.45/0.60    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X6,k4_xboole_0(X5,X6)))) )),
% 1.45/0.60    inference(superposition,[],[f38,f44])).
% 1.45/0.60  fof(f38,plain,(
% 1.45/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.45/0.60    inference(cnf_transformation,[],[f9])).
% 1.45/0.60  fof(f9,axiom,(
% 1.45/0.60    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.45/0.60  fof(f968,plain,(
% 1.45/0.60    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,k2_xboole_0(sK0,sK1)))),
% 1.45/0.60    inference(forward_demodulation,[],[f967,f21])).
% 1.45/0.60  fof(f21,plain,(
% 1.45/0.60    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.45/0.60    inference(cnf_transformation,[],[f18])).
% 1.45/0.60  fof(f18,plain,(
% 1.45/0.60    sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)),
% 1.45/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f17])).
% 1.45/0.60  fof(f17,plain,(
% 1.45/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => (sK1 != sK2 & r1_xboole_0(sK3,sK1) & r1_xboole_0(sK2,sK0) & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3))),
% 1.45/0.60    introduced(choice_axiom,[])).
% 1.45/0.60  fof(f16,plain,(
% 1.45/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3))),
% 1.45/0.60    inference(flattening,[],[f15])).
% 1.45/0.60  fof(f15,plain,(
% 1.45/0.60    ? [X0,X1,X2,X3] : (X1 != X2 & (r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)))),
% 1.45/0.60    inference(ennf_transformation,[],[f14])).
% 1.45/0.60  fof(f14,negated_conjecture,(
% 1.45/0.60    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.45/0.60    inference(negated_conjecture,[],[f13])).
% 1.45/0.60  fof(f13,conjecture,(
% 1.45/0.60    ! [X0,X1,X2,X3] : ((r1_xboole_0(X3,X1) & r1_xboole_0(X2,X0) & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3)) => X1 = X2)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_xboole_1)).
% 1.45/0.60  fof(f967,plain,(
% 1.45/0.60    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(sK1,k2_xboole_0(sK2,sK3)))),
% 1.45/0.60    inference(forward_demodulation,[],[f898,f38])).
% 1.45/0.60  fof(f898,plain,(
% 1.45/0.60    k4_xboole_0(sK1,sK2) = k2_xboole_0(k4_xboole_0(sK3,sK3),k4_xboole_0(k4_xboole_0(sK1,sK2),sK3))),
% 1.45/0.60    inference(superposition,[],[f339,f768])).
% 1.45/0.60  fof(f768,plain,(
% 1.45/0.60    sK3 = k4_xboole_0(sK3,k4_xboole_0(sK1,sK2))),
% 1.45/0.60    inference(forward_demodulation,[],[f749,f412])).
% 1.45/0.60  fof(f412,plain,(
% 1.45/0.60    sK3 = k4_xboole_0(sK3,sK1)),
% 1.45/0.60    inference(superposition,[],[f346,f47])).
% 1.45/0.60  fof(f47,plain,(
% 1.45/0.60    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.45/0.60    inference(superposition,[],[f30,f27])).
% 1.45/0.60  fof(f30,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f1])).
% 1.45/0.60  fof(f1,axiom,(
% 1.45/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.45/0.60  fof(f346,plain,(
% 1.45/0.60    sK3 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK3,sK1))),
% 1.45/0.60    inference(superposition,[],[f41,f153])).
% 1.45/0.60  fof(f153,plain,(
% 1.45/0.60    k1_xboole_0 = k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))),
% 1.45/0.60    inference(resolution,[],[f43,f23])).
% 1.45/0.60  fof(f23,plain,(
% 1.45/0.60    r1_xboole_0(sK3,sK1)),
% 1.45/0.60    inference(cnf_transformation,[],[f18])).
% 1.45/0.60  fof(f43,plain,(
% 1.45/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.45/0.60    inference(definition_unfolding,[],[f34,f31])).
% 1.45/0.60  fof(f34,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.45/0.60    inference(cnf_transformation,[],[f19])).
% 1.45/0.60  fof(f19,plain,(
% 1.45/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.45/0.60    inference(nnf_transformation,[],[f3])).
% 1.45/0.60  fof(f3,axiom,(
% 1.45/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.45/0.60  fof(f41,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.45/0.60    inference(definition_unfolding,[],[f33,f31])).
% 1.45/0.60  fof(f33,plain,(
% 1.45/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.45/0.60    inference(cnf_transformation,[],[f11])).
% 1.45/0.60  fof(f11,axiom,(
% 1.45/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.45/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.45/0.60  fof(f749,plain,(
% 1.45/0.60    k4_xboole_0(sK3,sK1) = k4_xboole_0(sK3,k4_xboole_0(sK1,sK2))),
% 1.45/0.60    inference(superposition,[],[f429,f634])).
% 1.45/0.60  fof(f634,plain,(
% 1.45/0.60    sK1 = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.45/0.60    inference(forward_demodulation,[],[f633,f610])).
% 1.45/0.60  fof(f610,plain,(
% 1.45/0.60    sK1 = k2_xboole_0(sK2,k4_xboole_0(sK1,sK2))),
% 1.45/0.60    inference(superposition,[],[f41,f584])).
% 1.45/0.60  fof(f633,plain,(
% 1.45/0.60    k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.45/0.60    inference(forward_demodulation,[],[f632,f30])).
% 1.45/0.61  fof(f632,plain,(
% 1.45/0.61    k2_xboole_0(sK2,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK1)),
% 1.45/0.61    inference(forward_demodulation,[],[f611,f30])).
% 1.45/0.61  fof(f611,plain,(
% 1.45/0.61    k2_xboole_0(k4_xboole_0(sK1,sK2),sK1) = k2_xboole_0(k4_xboole_0(sK1,sK2),sK2)),
% 1.45/0.61    inference(superposition,[],[f32,f584])).
% 1.45/0.61  fof(f429,plain,(
% 1.45/0.61    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK1,X0)) = k4_xboole_0(sK3,X0)) )),
% 1.45/0.61    inference(superposition,[],[f38,f412])).
% 1.45/0.61  fof(f339,plain,(
% 1.45/0.61    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = X0) )),
% 1.45/0.61    inference(superposition,[],[f41,f40])).
% 1.45/0.61  fof(f40,plain,(
% 1.45/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.45/0.61    inference(definition_unfolding,[],[f29,f31,f31])).
% 1.45/0.61  fof(f29,plain,(
% 1.45/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.45/0.61    inference(cnf_transformation,[],[f2])).
% 1.45/0.61  fof(f2,axiom,(
% 1.45/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.45/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.45/0.61  fof(f584,plain,(
% 1.45/0.61    sK2 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.45/0.61    inference(forward_demodulation,[],[f577,f26])).
% 1.45/0.61  fof(f577,plain,(
% 1.45/0.61    k4_xboole_0(sK2,k1_xboole_0) = k4_xboole_0(sK1,k4_xboole_0(sK1,sK2))),
% 1.45/0.61    inference(superposition,[],[f40,f557])).
% 1.45/0.61  fof(f557,plain,(
% 1.45/0.61    k1_xboole_0 = k4_xboole_0(sK2,sK1)),
% 1.45/0.61    inference(superposition,[],[f400,f464])).
% 1.45/0.61  fof(f464,plain,(
% 1.45/0.61    k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(sK0,sK1))),
% 1.45/0.61    inference(superposition,[],[f206,f118])).
% 1.45/0.61  fof(f118,plain,(
% 1.45/0.61    k2_xboole_0(sK0,sK1) = k2_xboole_0(k2_xboole_0(sK0,sK1),sK2)),
% 1.45/0.61    inference(resolution,[],[f72,f45])).
% 1.45/0.61  fof(f45,plain,(
% 1.45/0.61    r1_tarski(sK2,k2_xboole_0(sK0,sK1))),
% 1.45/0.61    inference(superposition,[],[f28,f21])).
% 1.45/0.61  fof(f28,plain,(
% 1.45/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.45/0.61    inference(cnf_transformation,[],[f12])).
% 1.45/0.61  fof(f12,axiom,(
% 1.45/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.45/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.45/0.61  fof(f72,plain,(
% 1.45/0.61    ( ! [X2,X3] : (~r1_tarski(X2,X3) | k2_xboole_0(X3,X2) = X3) )),
% 1.45/0.61    inference(forward_demodulation,[],[f66,f27])).
% 1.45/0.61  fof(f66,plain,(
% 1.45/0.61    ( ! [X2,X3] : (k2_xboole_0(X3,X2) = k2_xboole_0(X3,k1_xboole_0) | ~r1_tarski(X2,X3)) )),
% 1.45/0.61    inference(superposition,[],[f32,f37])).
% 1.45/0.61  fof(f37,plain,(
% 1.45/0.61    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 1.45/0.61    inference(cnf_transformation,[],[f20])).
% 1.45/0.61  fof(f20,plain,(
% 1.45/0.61    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 1.45/0.61    inference(nnf_transformation,[],[f4])).
% 1.45/0.61  fof(f4,axiom,(
% 1.45/0.61    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 1.45/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.45/0.61  fof(f400,plain,(
% 1.45/0.61    ( ! [X0] : (k4_xboole_0(sK2,k2_xboole_0(sK0,X0)) = k4_xboole_0(sK2,X0)) )),
% 1.45/0.61    inference(superposition,[],[f38,f381])).
% 1.45/0.61  fof(f381,plain,(
% 1.45/0.61    sK2 = k4_xboole_0(sK2,sK0)),
% 1.45/0.61    inference(superposition,[],[f345,f47])).
% 1.45/0.61  fof(f345,plain,(
% 1.45/0.61    sK2 = k2_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK0))),
% 1.45/0.61    inference(superposition,[],[f41,f152])).
% 1.45/0.61  fof(f152,plain,(
% 1.45/0.61    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.45/0.61    inference(resolution,[],[f43,f22])).
% 1.45/0.61  fof(f22,plain,(
% 1.45/0.61    r1_xboole_0(sK2,sK0)),
% 1.45/0.61    inference(cnf_transformation,[],[f18])).
% 1.45/0.61  fof(f24,plain,(
% 1.45/0.61    sK1 != sK2),
% 1.45/0.61    inference(cnf_transformation,[],[f18])).
% 1.45/0.61  % SZS output end Proof for theBenchmark
% 1.45/0.61  % (14348)------------------------------
% 1.45/0.61  % (14348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.61  % (14348)Termination reason: Refutation
% 1.45/0.61  
% 1.45/0.61  % (14348)Memory used [KB]: 6652
% 1.45/0.61  % (14348)Time elapsed: 0.190 s
% 1.45/0.61  % (14348)------------------------------
% 1.45/0.61  % (14348)------------------------------
% 1.45/0.61  % (14334)Success in time 0.252 s
%------------------------------------------------------------------------------
