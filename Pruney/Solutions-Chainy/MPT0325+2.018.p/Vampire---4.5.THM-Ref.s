%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:40 EST 2020

% Result     : Theorem 3.20s
% Output     : Refutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 210 expanded)
%              Number of leaves         :   12 (  54 expanded)
%              Depth                    :   25
%              Number of atoms          :  145 ( 454 expanded)
%              Number of equality atoms :   91 ( 250 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5751,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5567,f41])).

fof(f41,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f5567,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f24,f5565])).

fof(f5565,plain,(
    k1_xboole_0 = sK0 ),
    inference(subsumption_resolution,[],[f5505,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f5505,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f24,f5500])).

fof(f5500,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f5499,f5122])).

fof(f5122,plain,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f5121,f25])).

fof(f25,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r1_tarski(sK0,sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,
    ( ( ~ r1_tarski(sK1,sK3)
      | ~ r1_tarski(sK0,sK2) )
    & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( ~ r1_tarski(X1,X3)
          | ~ r1_tarski(X0,X2) )
        & k1_xboole_0 != k2_zfmisc_1(X0,X1)
        & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) )
   => ( ( ~ r1_tarski(sK1,sK3)
        | ~ r1_tarski(sK0,sK2) )
      & k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
      & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ( ~ r1_tarski(X1,X3)
        | ~ r1_tarski(X0,X2) )
      & k1_xboole_0 != k2_zfmisc_1(X0,X1)
      & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
       => ( ( r1_tarski(X1,X3)
            & r1_tarski(X0,X2) )
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))
     => ( ( r1_tarski(X1,X3)
          & r1_tarski(X0,X2) )
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).

fof(f5121,plain,
    ( r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f5120])).

fof(f5120,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f34,f5086])).

fof(f5086,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,sK3)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f5051])).

fof(f5051,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f31,f5045])).

fof(f5045,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f5028,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f5028,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(resolution,[],[f5004,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f5004,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3)) ),
    inference(superposition,[],[f4188,f42])).

fof(f42,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(resolution,[],[f30,f23])).

fof(f23,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f4188,plain,(
    ! [X6,X4,X7,X5] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X7,X6)),k2_zfmisc_1(X4,X6)) ),
    inference(forward_demodulation,[],[f4172,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f4172,plain,(
    ! [X6,X4,X7,X5] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X4,X7),k3_xboole_0(X5,X6)),k2_zfmisc_1(X4,X6)) ),
    inference(superposition,[],[f2079,f1314])).

fof(f1314,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0) ),
    inference(superposition,[],[f39,f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f2079,plain,(
    ! [X78,X76,X77,X75] : r1_tarski(k3_xboole_0(k2_zfmisc_1(X75,k3_xboole_0(X76,X77)),X78),k2_zfmisc_1(X75,X77)) ),
    inference(superposition,[],[f60,f1304])).

fof(f1304,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2)) ),
    inference(superposition,[],[f39,f27])).

fof(f60,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),X1) ),
    inference(resolution,[],[f58,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f58,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f51,f28])).

fof(f28,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f50,f38])).

fof(f50,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(trivial_inequality_removal,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,X0) ) ),
    inference(superposition,[],[f34,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f45,f26])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f45,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5499,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f5498])).

fof(f5498,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f34,f5464])).

fof(f5464,plain,
    ( k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(trivial_inequality_removal,[],[f5429])).

fof(f5429,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f31,f5423])).

fof(f5423,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f5031,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f5031,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(resolution,[],[f5007,f35])).

fof(f5007,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1)) ),
    inference(superposition,[],[f4188,f562])).

fof(f562,plain,(
    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f162,f42])).

fof(f162,plain,(
    ! [X4,X3] : k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f62,f28])).

fof(f62,plain,(
    ! [X6,X5] : k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X6) ),
    inference(resolution,[],[f58,f30])).

fof(f24,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:29:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.51  % (12627)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (12631)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (12633)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.52  % (12637)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.53  % (12634)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (12642)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (12650)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.53  % (12649)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (12656)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (12641)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (12630)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (12655)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (12640)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (12645)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (12629)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.54  % (12636)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.54  % (12638)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (12649)Refutation not found, incomplete strategy% (12649)------------------------------
% 0.20/0.54  % (12649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (12649)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (12649)Memory used [KB]: 10618
% 0.20/0.54  % (12649)Time elapsed: 0.100 s
% 0.20/0.54  % (12649)------------------------------
% 0.20/0.54  % (12649)------------------------------
% 0.20/0.54  % (12646)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (12632)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.55  % (12654)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (12648)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (12639)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (12653)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (12644)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (12635)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.55  % (12647)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.56  % (12644)Refutation not found, incomplete strategy% (12644)------------------------------
% 0.20/0.56  % (12644)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.57  % (12644)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.57  
% 0.20/0.57  % (12644)Memory used [KB]: 10618
% 0.20/0.57  % (12644)Time elapsed: 0.161 s
% 0.20/0.57  % (12644)------------------------------
% 0.20/0.57  % (12644)------------------------------
% 0.20/0.57  % (12628)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.57  % (12651)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.58  % (12643)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.59  % (12652)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.77/0.72  % (12657)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.77/0.73  % (12658)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.20/0.85  % (12632)Time limit reached!
% 3.20/0.85  % (12632)------------------------------
% 3.20/0.85  % (12632)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.85  % (12632)Termination reason: Time limit
% 3.20/0.85  
% 3.20/0.85  % (12632)Memory used [KB]: 9083
% 3.20/0.85  % (12632)Time elapsed: 0.414 s
% 3.20/0.85  % (12632)------------------------------
% 3.20/0.85  % (12632)------------------------------
% 3.20/0.86  % (12634)Refutation found. Thanks to Tanya!
% 3.20/0.86  % SZS status Theorem for theBenchmark
% 3.89/0.86  % SZS output start Proof for theBenchmark
% 3.89/0.86  fof(f5751,plain,(
% 3.89/0.86    $false),
% 3.89/0.86    inference(subsumption_resolution,[],[f5567,f41])).
% 3.89/0.86  fof(f41,plain,(
% 3.89/0.86    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.89/0.86    inference(equality_resolution,[],[f32])).
% 3.89/0.86  fof(f32,plain,(
% 3.89/0.86    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.89/0.86    inference(cnf_transformation,[],[f21])).
% 3.89/0.86  fof(f21,plain,(
% 3.89/0.86    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.89/0.86    inference(flattening,[],[f20])).
% 3.89/0.86  fof(f20,plain,(
% 3.89/0.86    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.89/0.86    inference(nnf_transformation,[],[f8])).
% 3.89/0.86  fof(f8,axiom,(
% 3.89/0.86    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.89/0.86    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 3.89/0.86  fof(f5567,plain,(
% 3.89/0.86    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 3.89/0.86    inference(backward_demodulation,[],[f24,f5565])).
% 3.89/0.86  fof(f5565,plain,(
% 3.89/0.86    k1_xboole_0 = sK0),
% 3.89/0.86    inference(subsumption_resolution,[],[f5505,f40])).
% 3.89/0.86  fof(f40,plain,(
% 3.89/0.86    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.89/0.86    inference(equality_resolution,[],[f33])).
% 3.89/0.86  fof(f33,plain,(
% 3.89/0.86    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.89/0.86    inference(cnf_transformation,[],[f21])).
% 3.89/0.86  fof(f5505,plain,(
% 3.89/0.86    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 3.89/0.86    inference(superposition,[],[f24,f5500])).
% 3.89/0.86  fof(f5500,plain,(
% 3.89/0.86    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 3.89/0.86    inference(resolution,[],[f5499,f5122])).
% 3.89/0.86  fof(f5122,plain,(
% 3.89/0.86    ~r1_tarski(sK0,sK2) | k1_xboole_0 = sK0),
% 3.89/0.86    inference(resolution,[],[f5121,f25])).
% 3.89/0.86  fof(f25,plain,(
% 3.89/0.86    ~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)),
% 3.89/0.86    inference(cnf_transformation,[],[f19])).
% 3.89/0.86  fof(f19,plain,(
% 3.89/0.86    (~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.89/0.86    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f15,f18])).
% 3.89/0.87  fof(f18,plain,(
% 3.89/0.87    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3))) => ((~r1_tarski(sK1,sK3) | ~r1_tarski(sK0,sK2)) & k1_xboole_0 != k2_zfmisc_1(sK0,sK1) & r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)))),
% 3.89/0.87    introduced(choice_axiom,[])).
% 3.89/0.87  fof(f15,plain,(
% 3.89/0.87    ? [X0,X1,X2,X3] : ((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.89/0.87    inference(flattening,[],[f14])).
% 3.89/0.87  fof(f14,plain,(
% 3.89/0.87    ? [X0,X1,X2,X3] : (((~r1_tarski(X1,X3) | ~r1_tarski(X0,X2)) & k1_xboole_0 != k2_zfmisc_1(X0,X1)) & r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)))),
% 3.89/0.87    inference(ennf_transformation,[],[f12])).
% 3.89/0.87  fof(f12,negated_conjecture,(
% 3.89/0.87    ~! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.89/0.87    inference(negated_conjecture,[],[f11])).
% 3.89/0.87  fof(f11,conjecture,(
% 3.89/0.87    ! [X0,X1,X2,X3] : (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X2,X3)) => ((r1_tarski(X1,X3) & r1_tarski(X0,X2)) | k1_xboole_0 = k2_zfmisc_1(X0,X1)))),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_zfmisc_1)).
% 3.89/0.87  fof(f5121,plain,(
% 3.89/0.87    r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 3.89/0.87    inference(trivial_inequality_removal,[],[f5120])).
% 3.89/0.87  fof(f5120,plain,(
% 3.89/0.87    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3) | k1_xboole_0 = sK0),
% 3.89/0.87    inference(superposition,[],[f34,f5086])).
% 3.89/0.87  fof(f5086,plain,(
% 3.89/0.87    k1_xboole_0 = k4_xboole_0(sK1,sK3) | k1_xboole_0 = sK0),
% 3.89/0.87    inference(trivial_inequality_removal,[],[f5051])).
% 3.89/0.87  fof(f5051,plain,(
% 3.89/0.87    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 3.89/0.87    inference(superposition,[],[f31,f5045])).
% 3.89/0.87  fof(f5045,plain,(
% 3.89/0.87    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 3.89/0.87    inference(superposition,[],[f5028,f37])).
% 3.89/0.87  fof(f37,plain,(
% 3.89/0.87    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 3.89/0.87    inference(cnf_transformation,[],[f10])).
% 3.89/0.87  fof(f10,axiom,(
% 3.89/0.87    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 3.89/0.87  fof(f5028,plain,(
% 3.89/0.87    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 3.89/0.87    inference(resolution,[],[f5004,f35])).
% 3.89/0.87  fof(f35,plain,(
% 3.89/0.87    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 3.89/0.87    inference(cnf_transformation,[],[f22])).
% 3.89/0.87  fof(f22,plain,(
% 3.89/0.87    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 3.89/0.87    inference(nnf_transformation,[],[f3])).
% 3.89/0.87  fof(f3,axiom,(
% 3.89/0.87    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 3.89/0.87  fof(f5004,plain,(
% 3.89/0.87    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK3))),
% 3.89/0.87    inference(superposition,[],[f4188,f42])).
% 3.89/0.87  fof(f42,plain,(
% 3.89/0.87    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.89/0.87    inference(resolution,[],[f30,f23])).
% 3.89/0.87  fof(f23,plain,(
% 3.89/0.87    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3))),
% 3.89/0.87    inference(cnf_transformation,[],[f19])).
% 3.89/0.87  fof(f30,plain,(
% 3.89/0.87    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.89/0.87    inference(cnf_transformation,[],[f16])).
% 3.89/0.87  fof(f16,plain,(
% 3.89/0.87    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.89/0.87    inference(ennf_transformation,[],[f6])).
% 3.89/0.87  fof(f6,axiom,(
% 3.89/0.87    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.89/0.87  fof(f4188,plain,(
% 3.89/0.87    ( ! [X6,X4,X7,X5] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X7,X6)),k2_zfmisc_1(X4,X6))) )),
% 3.89/0.87    inference(forward_demodulation,[],[f4172,f39])).
% 3.89/0.87  fof(f39,plain,(
% 3.89/0.87    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 3.89/0.87    inference(cnf_transformation,[],[f9])).
% 3.89/0.87  fof(f9,axiom,(
% 3.89/0.87    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 3.89/0.87  fof(f4172,plain,(
% 3.89/0.87    ( ! [X6,X4,X7,X5] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X4,X7),k3_xboole_0(X5,X6)),k2_zfmisc_1(X4,X6))) )),
% 3.89/0.87    inference(superposition,[],[f2079,f1314])).
% 3.89/0.87  fof(f1314,plain,(
% 3.89/0.87    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) = k2_zfmisc_1(k3_xboole_0(X1,X2),X0)) )),
% 3.89/0.87    inference(superposition,[],[f39,f27])).
% 3.89/0.87  fof(f27,plain,(
% 3.89/0.87    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 3.89/0.87    inference(cnf_transformation,[],[f13])).
% 3.89/0.87  fof(f13,plain,(
% 3.89/0.87    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 3.89/0.87    inference(rectify,[],[f2])).
% 3.89/0.87  fof(f2,axiom,(
% 3.89/0.87    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 3.89/0.87  fof(f2079,plain,(
% 3.89/0.87    ( ! [X78,X76,X77,X75] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(X75,k3_xboole_0(X76,X77)),X78),k2_zfmisc_1(X75,X77))) )),
% 3.89/0.87    inference(superposition,[],[f60,f1304])).
% 3.89/0.87  fof(f1304,plain,(
% 3.89/0.87    ( ! [X2,X0,X1] : (k3_xboole_0(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) = k2_zfmisc_1(X0,k3_xboole_0(X1,X2))) )),
% 3.89/0.87    inference(superposition,[],[f39,f27])).
% 3.89/0.87  fof(f60,plain,(
% 3.89/0.87    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),X2),X1)) )),
% 3.89/0.87    inference(resolution,[],[f58,f38])).
% 3.89/0.87  fof(f38,plain,(
% 3.89/0.87    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k3_xboole_0(X0,X2),X1)) )),
% 3.89/0.87    inference(cnf_transformation,[],[f17])).
% 3.89/0.87  fof(f17,plain,(
% 3.89/0.87    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.89/0.87    inference(ennf_transformation,[],[f5])).
% 3.89/0.87  fof(f5,axiom,(
% 3.89/0.87    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 3.89/0.87  fof(f58,plain,(
% 3.89/0.87    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 3.89/0.87    inference(superposition,[],[f51,f28])).
% 3.89/0.87  fof(f28,plain,(
% 3.89/0.87    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.89/0.87    inference(cnf_transformation,[],[f1])).
% 3.89/0.87  fof(f1,axiom,(
% 3.89/0.87    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.89/0.87  fof(f51,plain,(
% 3.89/0.87    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 3.89/0.87    inference(resolution,[],[f50,f38])).
% 3.89/0.87  fof(f50,plain,(
% 3.89/0.87    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 3.89/0.87    inference(trivial_inequality_removal,[],[f49])).
% 3.89/0.87  fof(f49,plain,(
% 3.89/0.87    ( ! [X0] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,X0)) )),
% 3.89/0.87    inference(superposition,[],[f34,f48])).
% 3.89/0.87  fof(f48,plain,(
% 3.89/0.87    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.89/0.87    inference(forward_demodulation,[],[f45,f26])).
% 3.89/0.87  fof(f26,plain,(
% 3.89/0.87    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.89/0.87    inference(cnf_transformation,[],[f7])).
% 3.89/0.87  fof(f7,axiom,(
% 3.89/0.87    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 3.89/0.87  fof(f45,plain,(
% 3.89/0.87    ( ! [X0] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,X0)) )),
% 3.89/0.87    inference(superposition,[],[f29,f27])).
% 3.89/0.87  fof(f29,plain,(
% 3.89/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.89/0.87    inference(cnf_transformation,[],[f4])).
% 3.89/0.87  fof(f4,axiom,(
% 3.89/0.87    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.89/0.87    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.89/0.87  fof(f31,plain,(
% 3.89/0.87    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 3.89/0.87    inference(cnf_transformation,[],[f21])).
% 3.89/0.87  fof(f34,plain,(
% 3.89/0.87    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 3.89/0.87    inference(cnf_transformation,[],[f22])).
% 3.89/0.87  fof(f5499,plain,(
% 3.89/0.87    r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 3.89/0.87    inference(trivial_inequality_removal,[],[f5498])).
% 3.89/0.87  fof(f5498,plain,(
% 3.89/0.87    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 3.89/0.87    inference(superposition,[],[f34,f5464])).
% 3.89/0.87  fof(f5464,plain,(
% 3.89/0.87    k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 3.89/0.87    inference(trivial_inequality_removal,[],[f5429])).
% 3.89/0.87  fof(f5429,plain,(
% 3.89/0.87    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 3.89/0.87    inference(superposition,[],[f31,f5423])).
% 3.89/0.87  fof(f5423,plain,(
% 3.89/0.87    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 3.89/0.87    inference(superposition,[],[f5031,f36])).
% 3.89/0.87  fof(f36,plain,(
% 3.89/0.87    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 3.89/0.87    inference(cnf_transformation,[],[f10])).
% 3.89/0.87  fof(f5031,plain,(
% 3.89/0.87    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 3.89/0.87    inference(resolution,[],[f5007,f35])).
% 3.89/0.87  fof(f5007,plain,(
% 3.89/0.87    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK1))),
% 3.89/0.87    inference(superposition,[],[f4188,f562])).
% 3.89/0.87  fof(f562,plain,(
% 3.89/0.87    k2_zfmisc_1(sK0,sK1) = k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),
% 3.89/0.87    inference(superposition,[],[f162,f42])).
% 3.89/0.87  fof(f162,plain,(
% 3.89/0.87    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k3_xboole_0(X4,k3_xboole_0(X3,X4))) )),
% 3.89/0.87    inference(superposition,[],[f62,f28])).
% 3.89/0.87  fof(f62,plain,(
% 3.89/0.87    ( ! [X6,X5] : (k3_xboole_0(X5,X6) = k3_xboole_0(k3_xboole_0(X5,X6),X6)) )),
% 3.89/0.87    inference(resolution,[],[f58,f30])).
% 3.89/0.87  fof(f24,plain,(
% 3.89/0.87    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 3.89/0.87    inference(cnf_transformation,[],[f19])).
% 3.89/0.87  % SZS output end Proof for theBenchmark
% 3.89/0.87  % (12634)------------------------------
% 3.89/0.87  % (12634)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.87  % (12634)Termination reason: Refutation
% 3.89/0.87  
% 3.89/0.87  % (12634)Memory used [KB]: 9978
% 3.89/0.87  % (12634)Time elapsed: 0.442 s
% 3.89/0.87  % (12634)------------------------------
% 3.89/0.87  % (12634)------------------------------
% 3.89/0.87  % (12626)Success in time 0.512 s
%------------------------------------------------------------------------------
