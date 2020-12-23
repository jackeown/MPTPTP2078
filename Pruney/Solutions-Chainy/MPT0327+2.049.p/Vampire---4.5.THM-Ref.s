%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 533 expanded)
%              Number of leaves         :   13 ( 161 expanded)
%              Depth                    :   24
%              Number of atoms          :  106 ( 757 expanded)
%              Number of equality atoms :   77 ( 463 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f941,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f940])).

fof(f940,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f257,f939])).

fof(f939,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f938,f826])).

fof(f826,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f767,f401])).

fof(f401,plain,(
    sK1 = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f400,f76])).

fof(f76,plain,(
    ! [X4] : k5_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f73,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f73,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f34,f50])).

fof(f50,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f47,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f37,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f400,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f399,f47])).

fof(f399,plain,(
    k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))) ),
    inference(superposition,[],[f36,f393])).

fof(f393,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f389,f76])).

fof(f389,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(superposition,[],[f385,f77])).

fof(f77,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f74,f61])).

fof(f61,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f74,plain,(
    ! [X5] : k4_xboole_0(X5,k1_zfmisc_1(k3_tarski(X5))) = k5_xboole_0(X5,X5) ),
    inference(superposition,[],[f34,f48])).

fof(f48,plain,(
    ! [X1] : k3_xboole_0(X1,k1_zfmisc_1(k3_tarski(X1))) = X1 ),
    inference(resolution,[],[f37,f29])).

fof(f385,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0)) ),
    inference(superposition,[],[f43,f378])).

fof(f378,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f368,f253])).

fof(f253,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f240,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f34,f31])).

fof(f240,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f43,f36])).

fof(f368,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(superposition,[],[f237,f77])).

fof(f237,plain,(
    ! [X10] : k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X10)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X10) ),
    inference(superposition,[],[f43,f109])).

fof(f109,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f71,f105])).

fof(f105,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f49,f25])).

fof(f25,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).

fof(f21,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f49,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),X3) ) ),
    inference(resolution,[],[f37,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f767,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,X6) = X6 ),
    inference(backward_demodulation,[],[f199,f766])).

fof(f766,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f727,f76])).

fof(f727,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f235,f77])).

fof(f235,plain,(
    ! [X6,X7] : k5_xboole_0(X6,k5_xboole_0(X6,X7)) = k5_xboole_0(k1_xboole_0,X7) ),
    inference(superposition,[],[f43,f77])).

fof(f199,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k1_xboole_0,X6) ),
    inference(forward_demodulation,[],[f171,f76])).

fof(f171,plain,(
    ! [X6] : k2_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X6),k1_xboole_0) ),
    inference(superposition,[],[f36,f47])).

fof(f938,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f934,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f934,plain,(
    k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f36,f923])).

fof(f923,plain,(
    sK1 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f919,f109])).

fof(f919,plain,(
    sK1 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f862,f43])).

fof(f862,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f173,f826])).

fof(f173,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f36,f105])).

fof(f257,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f256,f31])).

fof(f256,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))) ),
    inference(superposition,[],[f36,f195])).

fof(f195,plain,(
    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f194,f184])).

fof(f184,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f83,f178])).

fof(f178,plain,(
    ! [X5] : k2_xboole_0(X5,k1_xboole_0) = X5 ),
    inference(forward_demodulation,[],[f177,f28])).

fof(f177,plain,(
    ! [X5] : k2_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,k1_xboole_0) ),
    inference(forward_demodulation,[],[f164,f34])).

fof(f164,plain,(
    ! [X5] : k2_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k3_xboole_0(X5,k1_xboole_0)) ),
    inference(superposition,[],[f36,f76])).

fof(f83,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f35,f81])).

fof(f81,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f63,f25])).

fof(f63,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X4),X5) ) ),
    inference(resolution,[],[f41,f39])).

fof(f194,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f165,f107])).

fof(f107,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f105,f31])).

fof(f165,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f36,f109])).

fof(f26,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:28:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (19863)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.46  % (19867)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.47  % (19864)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.47  % (19868)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (19868)Refutation not found, incomplete strategy% (19868)------------------------------
% 0.21/0.47  % (19868)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (19868)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (19868)Memory used [KB]: 10618
% 0.21/0.47  % (19868)Time elapsed: 0.057 s
% 0.21/0.47  % (19868)------------------------------
% 0.21/0.47  % (19868)------------------------------
% 0.21/0.47  % (19859)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (19857)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (19871)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (19860)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.48  % (19861)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (19870)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (19862)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (19865)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (19872)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.50  % (19873)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (19858)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (19866)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (19869)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.52  % (19874)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.53  % (19873)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f941,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(subsumption_resolution,[],[f26,f940])).
% 0.21/0.53  fof(f940,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.53    inference(backward_demodulation,[],[f257,f939])).
% 0.21/0.53  fof(f939,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.53    inference(forward_demodulation,[],[f938,f826])).
% 0.21/0.53  fof(f826,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.53    inference(superposition,[],[f767,f401])).
% 0.21/0.53  fof(f401,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f400,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X4] : (k5_xboole_0(X4,k1_xboole_0) = X4) )),
% 0.21/0.53    inference(forward_demodulation,[],[f73,f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f34,f50])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f47,f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(resolution,[],[f37,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.53  fof(f400,plain,(
% 0.21/0.53    k5_xboole_0(sK1,k1_xboole_0) = k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f399,f47])).
% 0.21/0.53  fof(f399,plain,(
% 0.21/0.53    k2_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(sK1,k3_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)))),
% 0.21/0.53    inference(superposition,[],[f36,f393])).
% 0.21/0.53  fof(f393,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f389,f76])).
% 0.21/0.53  fof(f389,plain,(
% 0.21/0.53    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.53    inference(superposition,[],[f385,f77])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f74,f61])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k1_zfmisc_1(k3_tarski(X1)))) )),
% 0.21/0.53    inference(resolution,[],[f41,f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,axiom,(
% 0.21/0.53    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.53    inference(nnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X5] : (k4_xboole_0(X5,k1_zfmisc_1(k3_tarski(X5))) = k5_xboole_0(X5,X5)) )),
% 0.21/0.53    inference(superposition,[],[f34,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X1] : (k3_xboole_0(X1,k1_zfmisc_1(k3_tarski(X1))) = X1) )),
% 0.21/0.53    inference(resolution,[],[f37,f29])).
% 0.21/0.53  fof(f385,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0))) )),
% 0.21/0.53    inference(superposition,[],[f43,f378])).
% 0.21/0.53  fof(f378,plain,(
% 0.21/0.53    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.53    inference(forward_demodulation,[],[f368,f253])).
% 0.21/0.53  fof(f253,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(forward_demodulation,[],[f240,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 0.21/0.53    inference(superposition,[],[f34,f31])).
% 0.21/0.53  fof(f240,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 0.21/0.53    inference(superposition,[],[f43,f36])).
% 0.21/0.53  fof(f368,plain,(
% 0.21/0.53    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.53    inference(superposition,[],[f237,f77])).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    ( ! [X10] : (k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X10)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X10)) )),
% 0.21/0.53    inference(superposition,[],[f43,f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.53    inference(superposition,[],[f71,f105])).
% 0.21/0.53  fof(f105,plain,(
% 0.21/0.53    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.53    inference(resolution,[],[f49,f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.53    inference(negated_conjecture,[],[f17])).
% 0.21/0.53  fof(f17,conjecture,(
% 0.21/0.53    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X3] : (~r2_hidden(X2,X3) | k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),X3)) )),
% 0.21/0.53    inference(resolution,[],[f37,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.53    inference(nnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.53  fof(f767,plain,(
% 0.21/0.53    ( ! [X6] : (k2_xboole_0(k1_xboole_0,X6) = X6) )),
% 0.21/0.53    inference(backward_demodulation,[],[f199,f766])).
% 0.21/0.53  fof(f766,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.21/0.53    inference(forward_demodulation,[],[f727,f76])).
% 0.21/0.53  fof(f727,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.53    inference(superposition,[],[f235,f77])).
% 0.21/0.53  fof(f235,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k5_xboole_0(X6,k5_xboole_0(X6,X7)) = k5_xboole_0(k1_xboole_0,X7)) )),
% 0.21/0.53    inference(superposition,[],[f43,f77])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ( ! [X6] : (k2_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k1_xboole_0,X6)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f171,f76])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ( ! [X6] : (k2_xboole_0(k1_xboole_0,X6) = k5_xboole_0(k5_xboole_0(k1_xboole_0,X6),k1_xboole_0)) )),
% 0.21/0.53    inference(superposition,[],[f36,f47])).
% 0.21/0.53  fof(f938,plain,(
% 0.21/0.53    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.53    inference(forward_demodulation,[],[f934,f35])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.53  fof(f934,plain,(
% 0.21/0.53    k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.53    inference(superposition,[],[f36,f923])).
% 0.21/0.53  fof(f923,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.53    inference(forward_demodulation,[],[f919,f109])).
% 0.21/0.53  fof(f919,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.53    inference(superposition,[],[f862,f43])).
% 0.21/0.53  fof(f862,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 0.21/0.53    inference(backward_demodulation,[],[f173,f826])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 0.21/0.53    inference(superposition,[],[f36,f105])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.53    inference(forward_demodulation,[],[f256,f31])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)))),
% 0.21/0.53    inference(superposition,[],[f36,f195])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.53    inference(forward_demodulation,[],[f194,f184])).
% 0.21/0.53  fof(f184,plain,(
% 0.21/0.53    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.53    inference(backward_demodulation,[],[f83,f178])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    ( ! [X5] : (k2_xboole_0(X5,k1_xboole_0) = X5) )),
% 0.21/0.53    inference(forward_demodulation,[],[f177,f28])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    ( ! [X5] : (k2_xboole_0(X5,k1_xboole_0) = k4_xboole_0(X5,k1_xboole_0)) )),
% 0.21/0.53    inference(forward_demodulation,[],[f164,f34])).
% 0.21/0.53  fof(f164,plain,(
% 0.21/0.53    ( ! [X5] : (k2_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k3_xboole_0(X5,k1_xboole_0))) )),
% 0.21/0.53    inference(superposition,[],[f36,f76])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.53    inference(superposition,[],[f35,f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.53    inference(resolution,[],[f63,f25])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~r2_hidden(X4,X5) | k1_xboole_0 = k4_xboole_0(k1_tarski(X4),X5)) )),
% 0.21/0.53    inference(resolution,[],[f41,f39])).
% 0.21/0.53  fof(f194,plain,(
% 0.21/0.53    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.53    inference(forward_demodulation,[],[f165,f107])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.53    inference(superposition,[],[f105,f31])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.53    inference(superposition,[],[f36,f109])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (19873)------------------------------
% 0.21/0.53  % (19873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (19873)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (19873)Memory used [KB]: 6780
% 0.21/0.53  % (19873)Time elapsed: 0.090 s
% 0.21/0.53  % (19873)------------------------------
% 0.21/0.53  % (19873)------------------------------
% 0.21/0.53  % (19856)Success in time 0.179 s
%------------------------------------------------------------------------------
