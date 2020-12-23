%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:27 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 903 expanded)
%              Number of leaves         :   14 ( 300 expanded)
%              Depth                    :   28
%              Number of atoms          :   99 ( 923 expanded)
%              Number of equality atoms :   78 ( 890 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4215,plain,(
    $false ),
    inference(subsumption_resolution,[],[f111,f4181])).

fof(f4181,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f4161,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f4161,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(forward_demodulation,[],[f4138,f73])).

fof(f73,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f72,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f72,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f71,f64])).

fof(f64,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f40,f34])).

fof(f34,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f40,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f41,f33])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f4138,plain,(
    k3_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0) ),
    inference(superposition,[],[f42,f4085])).

fof(f4085,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f4057,f3787])).

fof(f3787,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5 ),
    inference(forward_demodulation,[],[f3736,f2646])).

fof(f2646,plain,(
    ! [X10,X9] : k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9 ),
    inference(forward_demodulation,[],[f2614,f74])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f64,f73])).

fof(f2614,plain,(
    ! [X10,X9] : k5_xboole_0(X9,k1_xboole_0) = k4_xboole_0(X9,k4_xboole_0(X10,X9)) ),
    inference(superposition,[],[f40,f2472])).

fof(f2472,plain,(
    ! [X4,X5] : k1_xboole_0 = k3_xboole_0(X5,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f2471,f183])).

fof(f183,plain,(
    ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f180,f37])).

fof(f180,plain,(
    ! [X12,X11] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X11,X12),X11) ),
    inference(forward_demodulation,[],[f171,f91])).

fof(f91,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f90,f85])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(forward_demodulation,[],[f79,f34])).

fof(f79,plain,(
    ! [X1] : k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f42,f73])).

fof(f90,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f40,f88])).

fof(f88,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(forward_demodulation,[],[f86,f73])).

fof(f86,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0) ),
    inference(superposition,[],[f42,f85])).

fof(f171,plain,(
    ! [X12,X11] : k4_xboole_0(k3_xboole_0(X11,X12),X11) = k5_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12)) ),
    inference(superposition,[],[f65,f139])).

fof(f139,plain,(
    ! [X8,X9] : k3_xboole_0(X8,X9) = k3_xboole_0(X8,k3_xboole_0(X8,X9)) ),
    inference(superposition,[],[f48,f88])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f65,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(superposition,[],[f40,f37])).

fof(f2471,plain,(
    ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),X5) = k3_xboole_0(X5,k4_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f2470,f37])).

fof(f2470,plain,(
    ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),X5) = k3_xboole_0(k4_xboole_0(X4,X5),X5) ),
    inference(forward_demodulation,[],[f2439,f40])).

fof(f2439,plain,(
    ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),X5) = k3_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X5) ),
    inference(superposition,[],[f49,f40])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f3736,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k3_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f2446,f41])).

fof(f2446,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2445,f65])).

fof(f2445,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f2410,f37])).

fof(f2410,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f49,f88])).

fof(f4057,plain,(
    ! [X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,k2_xboole_0(k1_tarski(sK0),sK1)),sK1) ),
    inference(superposition,[],[f202,f3830])).

fof(f3830,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f3807,f73])).

fof(f3807,plain,(
    k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) ),
    inference(superposition,[],[f42,f3791])).

fof(f3791,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f3741,f2472])).

fof(f3741,plain,(
    k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(superposition,[],[f2446,f2548])).

fof(f2548,plain,(
    k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f2547,f235])).

fof(f235,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f234,f65])).

fof(f234,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,k3_xboole_0(X2,X1)) ),
    inference(forward_demodulation,[],[f231,f176])).

fof(f176,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k4_xboole_0(X4,X5) ),
    inference(forward_demodulation,[],[f168,f40])).

fof(f168,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k5_xboole_0(X4,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f40,f139])).

fof(f231,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(superposition,[],[f43,f208])).

fof(f208,plain,(
    ! [X4,X3] : k2_xboole_0(X4,k3_xboole_0(X3,X4)) = X4 ),
    inference(forward_demodulation,[],[f205,f74])).

fof(f205,plain,(
    ! [X4,X3] : k2_xboole_0(X4,k3_xboole_0(X3,X4)) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f41,f183])).

fof(f43,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f2547,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) = k4_xboole_0(sK1,k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)) ),
    inference(superposition,[],[f43,f2474])).

fof(f2474,plain,(
    sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f2473,f73])).

fof(f2473,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f128,f2472])).

fof(f128,plain,(
    k4_xboole_0(sK1,k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)))) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(forward_demodulation,[],[f115,f41])).

fof(f115,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))) = k4_xboole_0(sK1,k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)))) ),
    inference(superposition,[],[f43,f110])).

fof(f110,plain,(
    sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))) ),
    inference(resolution,[],[f44,f31])).

fof(f31,plain,(
    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ r2_hidden(sK0,sK1)
    & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) )
   => ( ~ r2_hidden(sK0,sK1)
      & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
       => r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)
     => r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f202,plain,(
    ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X9,k3_xboole_0(X10,X11)),X11) ),
    inference(superposition,[],[f183,f48])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f111,plain,(
    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:16:18 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.45  % (18023)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.46  % (18038)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.46  % (18024)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.47  % (18025)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (18026)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.47  % (18036)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (18027)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (18028)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (18033)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (18031)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.48  % (18034)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.48  % (18021)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.48  % (18022)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (18035)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (18037)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.49  % (18030)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.51  % (18029)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (18032)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 2.14/0.64  % (18037)Refutation found. Thanks to Tanya!
% 2.14/0.64  % SZS status Theorem for theBenchmark
% 2.14/0.64  % SZS output start Proof for theBenchmark
% 2.14/0.64  fof(f4215,plain,(
% 2.14/0.64    $false),
% 2.14/0.64    inference(subsumption_resolution,[],[f111,f4181])).
% 2.14/0.64  fof(f4181,plain,(
% 2.14/0.64    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 2.14/0.64    inference(superposition,[],[f4161,f37])).
% 2.14/0.64  fof(f37,plain,(
% 2.14/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f1])).
% 2.14/0.64  fof(f1,axiom,(
% 2.14/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.14/0.64  fof(f4161,plain,(
% 2.14/0.64    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 2.14/0.64    inference(forward_demodulation,[],[f4138,f73])).
% 2.14/0.64  fof(f73,plain,(
% 2.14/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.14/0.64    inference(forward_demodulation,[],[f72,f35])).
% 2.14/0.64  fof(f35,plain,(
% 2.14/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.14/0.64    inference(cnf_transformation,[],[f6])).
% 2.14/0.64  fof(f6,axiom,(
% 2.14/0.64    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.14/0.64  fof(f72,plain,(
% 2.14/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k4_xboole_0(X0,k1_xboole_0)) )),
% 2.14/0.64    inference(forward_demodulation,[],[f71,f64])).
% 2.14/0.64  fof(f64,plain,(
% 2.14/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.14/0.64    inference(superposition,[],[f40,f34])).
% 2.14/0.64  fof(f34,plain,(
% 2.14/0.64    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f7])).
% 2.14/0.64  fof(f7,axiom,(
% 2.14/0.64    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.14/0.64  fof(f40,plain,(
% 2.14/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.14/0.64    inference(cnf_transformation,[],[f2])).
% 2.14/0.64  fof(f2,axiom,(
% 2.14/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.14/0.64  fof(f71,plain,(
% 2.14/0.64    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) )),
% 2.14/0.64    inference(superposition,[],[f41,f33])).
% 2.14/0.64  fof(f33,plain,(
% 2.14/0.64    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f10])).
% 2.14/0.64  fof(f10,axiom,(
% 2.14/0.64    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 2.14/0.64  fof(f41,plain,(
% 2.14/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.14/0.64    inference(cnf_transformation,[],[f11])).
% 2.14/0.64  fof(f11,axiom,(
% 2.14/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 2.14/0.64  fof(f4138,plain,(
% 2.14/0.64    k3_xboole_0(k1_tarski(sK0),sK1) = k4_xboole_0(k1_tarski(sK0),k1_xboole_0)),
% 2.14/0.64    inference(superposition,[],[f42,f4085])).
% 2.14/0.64  fof(f4085,plain,(
% 2.14/0.64    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 2.14/0.64    inference(superposition,[],[f4057,f3787])).
% 2.14/0.64  fof(f3787,plain,(
% 2.14/0.64    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5) )),
% 2.14/0.64    inference(forward_demodulation,[],[f3736,f2646])).
% 2.14/0.64  fof(f2646,plain,(
% 2.14/0.64    ( ! [X10,X9] : (k4_xboole_0(X9,k4_xboole_0(X10,X9)) = X9) )),
% 2.14/0.64    inference(forward_demodulation,[],[f2614,f74])).
% 2.14/0.64  fof(f74,plain,(
% 2.14/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.14/0.64    inference(backward_demodulation,[],[f64,f73])).
% 2.14/0.64  fof(f2614,plain,(
% 2.14/0.64    ( ! [X10,X9] : (k5_xboole_0(X9,k1_xboole_0) = k4_xboole_0(X9,k4_xboole_0(X10,X9))) )),
% 2.14/0.64    inference(superposition,[],[f40,f2472])).
% 2.14/0.64  fof(f2472,plain,(
% 2.14/0.64    ( ! [X4,X5] : (k1_xboole_0 = k3_xboole_0(X5,k4_xboole_0(X4,X5))) )),
% 2.14/0.64    inference(forward_demodulation,[],[f2471,f183])).
% 2.14/0.64  fof(f183,plain,(
% 2.14/0.64    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X2,X1),X1)) )),
% 2.14/0.64    inference(superposition,[],[f180,f37])).
% 2.14/0.64  fof(f180,plain,(
% 2.14/0.64    ( ! [X12,X11] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X11,X12),X11)) )),
% 2.14/0.64    inference(forward_demodulation,[],[f171,f91])).
% 2.14/0.64  fof(f91,plain,(
% 2.14/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.14/0.64    inference(forward_demodulation,[],[f90,f85])).
% 2.14/0.64  fof(f85,plain,(
% 2.14/0.64    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 2.14/0.64    inference(forward_demodulation,[],[f79,f34])).
% 2.14/0.64  fof(f79,plain,(
% 2.14/0.64    ( ! [X1] : (k3_xboole_0(X1,k1_xboole_0) = k4_xboole_0(X1,X1)) )),
% 2.14/0.64    inference(superposition,[],[f42,f73])).
% 2.14/0.64  fof(f90,plain,(
% 2.14/0.64    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 2.14/0.64    inference(superposition,[],[f40,f88])).
% 2.14/0.64  fof(f88,plain,(
% 2.14/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.14/0.64    inference(forward_demodulation,[],[f86,f73])).
% 2.14/0.64  fof(f86,plain,(
% 2.14/0.64    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k3_xboole_0(X0,X0)) )),
% 2.14/0.64    inference(superposition,[],[f42,f85])).
% 2.14/0.64  fof(f171,plain,(
% 2.14/0.64    ( ! [X12,X11] : (k4_xboole_0(k3_xboole_0(X11,X12),X11) = k5_xboole_0(k3_xboole_0(X11,X12),k3_xboole_0(X11,X12))) )),
% 2.14/0.64    inference(superposition,[],[f65,f139])).
% 2.14/0.64  fof(f139,plain,(
% 2.14/0.64    ( ! [X8,X9] : (k3_xboole_0(X8,X9) = k3_xboole_0(X8,k3_xboole_0(X8,X9))) )),
% 2.14/0.64    inference(superposition,[],[f48,f88])).
% 2.14/0.64  fof(f48,plain,(
% 2.14/0.64    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 2.14/0.64    inference(cnf_transformation,[],[f5])).
% 2.14/0.64  fof(f5,axiom,(
% 2.14/0.64    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).
% 2.14/0.64  fof(f65,plain,(
% 2.14/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.14/0.64    inference(superposition,[],[f40,f37])).
% 2.14/0.64  fof(f2471,plain,(
% 2.14/0.64    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),X5) = k3_xboole_0(X5,k4_xboole_0(X4,X5))) )),
% 2.14/0.64    inference(forward_demodulation,[],[f2470,f37])).
% 2.14/0.64  fof(f2470,plain,(
% 2.14/0.64    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),X5) = k3_xboole_0(k4_xboole_0(X4,X5),X5)) )),
% 2.14/0.64    inference(forward_demodulation,[],[f2439,f40])).
% 2.14/0.64  fof(f2439,plain,(
% 2.14/0.64    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),X5) = k3_xboole_0(k5_xboole_0(X4,k3_xboole_0(X4,X5)),X5)) )),
% 2.14/0.64    inference(superposition,[],[f49,f40])).
% 2.14/0.64  fof(f49,plain,(
% 2.14/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f4])).
% 2.14/0.64  fof(f4,axiom,(
% 2.14/0.64    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.14/0.64  fof(f3736,plain,(
% 2.14/0.64    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = k3_xboole_0(X5,k2_xboole_0(X5,X6))) )),
% 2.14/0.64    inference(superposition,[],[f2446,f41])).
% 2.14/0.64  fof(f2446,plain,(
% 2.14/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.14/0.64    inference(forward_demodulation,[],[f2445,f65])).
% 2.14/0.64  fof(f2445,plain,(
% 2.14/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.14/0.64    inference(forward_demodulation,[],[f2410,f37])).
% 2.14/0.64  fof(f2410,plain,(
% 2.14/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(k5_xboole_0(X0,X1),X0)) )),
% 2.14/0.64    inference(superposition,[],[f49,f88])).
% 2.14/0.64  fof(f4057,plain,(
% 2.14/0.64    ( ! [X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,k2_xboole_0(k1_tarski(sK0),sK1)),sK1)) )),
% 2.14/0.64    inference(superposition,[],[f202,f3830])).
% 2.14/0.64  fof(f3830,plain,(
% 2.14/0.64    k2_xboole_0(k1_tarski(sK0),sK1) = k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.14/0.64    inference(forward_demodulation,[],[f3807,f73])).
% 2.14/0.64  fof(f3807,plain,(
% 2.14/0.64    k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0)),
% 2.14/0.64    inference(superposition,[],[f42,f3791])).
% 2.14/0.64  fof(f3791,plain,(
% 2.14/0.64    k1_xboole_0 = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.14/0.64    inference(forward_demodulation,[],[f3741,f2472])).
% 2.14/0.64  fof(f3741,plain,(
% 2.14/0.64    k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))) = k4_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.14/0.64    inference(superposition,[],[f2446,f2548])).
% 2.14/0.64  fof(f2548,plain,(
% 2.14/0.64    k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.14/0.64    inference(forward_demodulation,[],[f2547,f235])).
% 2.14/0.64  fof(f235,plain,(
% 2.14/0.64    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.14/0.64    inference(forward_demodulation,[],[f234,f65])).
% 2.14/0.64  fof(f234,plain,(
% 2.14/0.64    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,k3_xboole_0(X2,X1))) )),
% 2.14/0.64    inference(forward_demodulation,[],[f231,f176])).
% 2.14/0.64  fof(f176,plain,(
% 2.14/0.64    ( ! [X4,X5] : (k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k4_xboole_0(X4,X5)) )),
% 2.14/0.64    inference(forward_demodulation,[],[f168,f40])).
% 2.14/0.64  fof(f168,plain,(
% 2.14/0.64    ( ! [X4,X5] : (k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k5_xboole_0(X4,k3_xboole_0(X4,X5))) )),
% 2.14/0.64    inference(superposition,[],[f40,f139])).
% 2.14/0.64  fof(f231,plain,(
% 2.14/0.64    ( ! [X2,X1] : (k5_xboole_0(X1,k3_xboole_0(X2,X1)) = k4_xboole_0(X1,k3_xboole_0(X1,k3_xboole_0(X2,X1)))) )),
% 2.14/0.64    inference(superposition,[],[f43,f208])).
% 2.14/0.64  fof(f208,plain,(
% 2.14/0.64    ( ! [X4,X3] : (k2_xboole_0(X4,k3_xboole_0(X3,X4)) = X4) )),
% 2.14/0.64    inference(forward_demodulation,[],[f205,f74])).
% 2.14/0.64  fof(f205,plain,(
% 2.14/0.64    ( ! [X4,X3] : (k2_xboole_0(X4,k3_xboole_0(X3,X4)) = k5_xboole_0(X4,k1_xboole_0)) )),
% 2.14/0.64    inference(superposition,[],[f41,f183])).
% 2.14/0.64  fof(f43,plain,(
% 2.14/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.14/0.64    inference(cnf_transformation,[],[f3])).
% 2.14/0.64  fof(f3,axiom,(
% 2.14/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 2.14/0.64  fof(f2547,plain,(
% 2.14/0.64    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) = k4_xboole_0(sK1,k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 2.14/0.64    inference(superposition,[],[f43,f2474])).
% 2.14/0.64  fof(f2474,plain,(
% 2.14/0.64    sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.14/0.64    inference(forward_demodulation,[],[f2473,f73])).
% 2.14/0.64  fof(f2473,plain,(
% 2.14/0.64    k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) = k4_xboole_0(sK1,k1_xboole_0)),
% 2.14/0.64    inference(backward_demodulation,[],[f128,f2472])).
% 2.14/0.64  fof(f128,plain,(
% 2.14/0.64    k4_xboole_0(sK1,k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)))) = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.14/0.64    inference(forward_demodulation,[],[f115,f41])).
% 2.14/0.64  fof(f115,plain,(
% 2.14/0.64    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))) = k4_xboole_0(sK1,k3_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))))),
% 2.14/0.64    inference(superposition,[],[f43,f110])).
% 2.14/0.64  fof(f110,plain,(
% 2.14/0.64    sK1 = k2_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k4_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)))),
% 2.14/0.64    inference(resolution,[],[f44,f31])).
% 2.14/0.64  fof(f31,plain,(
% 2.14/0.64    r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.14/0.64    inference(cnf_transformation,[],[f30])).
% 2.14/0.64  fof(f30,plain,(
% 2.14/0.64    ~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 2.14/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f26,f29])).
% 2.14/0.64  fof(f29,plain,(
% 2.14/0.64    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1)) => (~r2_hidden(sK0,sK1) & r1_tarski(k2_xboole_0(k1_tarski(sK0),sK1),sK1))),
% 2.14/0.64    introduced(choice_axiom,[])).
% 2.14/0.64  fof(f26,plain,(
% 2.14/0.64    ? [X0,X1] : (~r2_hidden(X0,X1) & r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1))),
% 2.14/0.64    inference(ennf_transformation,[],[f25])).
% 2.14/0.64  fof(f25,negated_conjecture,(
% 2.14/0.64    ~! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.14/0.64    inference(negated_conjecture,[],[f24])).
% 2.14/0.64  fof(f24,conjecture,(
% 2.14/0.64    ! [X0,X1] : (r1_tarski(k2_xboole_0(k1_tarski(X0),X1),X1) => r2_hidden(X0,X1))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).
% 2.14/0.64  fof(f44,plain,(
% 2.14/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 2.14/0.64    inference(cnf_transformation,[],[f27])).
% 2.14/0.64  fof(f27,plain,(
% 2.14/0.64    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 2.14/0.64    inference(ennf_transformation,[],[f8])).
% 2.14/0.64  fof(f8,axiom,(
% 2.14/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).
% 2.14/0.64  fof(f202,plain,(
% 2.14/0.64    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X9,k3_xboole_0(X10,X11)),X11)) )),
% 2.14/0.64    inference(superposition,[],[f183,f48])).
% 2.14/0.64  fof(f42,plain,(
% 2.14/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.14/0.64    inference(cnf_transformation,[],[f9])).
% 2.14/0.64  fof(f9,axiom,(
% 2.14/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.14/0.64  fof(f111,plain,(
% 2.14/0.64    k1_tarski(sK0) != k3_xboole_0(sK1,k1_tarski(sK0))),
% 2.14/0.64    inference(resolution,[],[f45,f32])).
% 2.14/0.64  fof(f32,plain,(
% 2.14/0.64    ~r2_hidden(sK0,sK1)),
% 2.14/0.64    inference(cnf_transformation,[],[f30])).
% 2.14/0.64  fof(f45,plain,(
% 2.14/0.64    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 2.14/0.64    inference(cnf_transformation,[],[f28])).
% 2.14/0.64  fof(f28,plain,(
% 2.14/0.64    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 2.14/0.64    inference(ennf_transformation,[],[f22])).
% 2.14/0.64  fof(f22,axiom,(
% 2.14/0.64    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 2.14/0.64    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 2.14/0.64  % SZS output end Proof for theBenchmark
% 2.14/0.64  % (18037)------------------------------
% 2.14/0.64  % (18037)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.64  % (18037)Termination reason: Refutation
% 2.14/0.64  
% 2.14/0.64  % (18037)Memory used [KB]: 8955
% 2.14/0.64  % (18037)Time elapsed: 0.211 s
% 2.14/0.64  % (18037)------------------------------
% 2.14/0.64  % (18037)------------------------------
% 2.14/0.64  % (18017)Success in time 0.282 s
%------------------------------------------------------------------------------
