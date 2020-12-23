%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 961 expanded)
%              Number of leaves         :   13 ( 292 expanded)
%              Depth                    :   27
%              Number of atoms          :  103 (1370 expanded)
%              Number of equality atoms :   76 ( 857 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f779,plain,(
    $false ),
    inference(subsumption_resolution,[],[f26,f778])).

fof(f778,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f230,f777])).

fof(f777,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f776,f719])).

fof(f719,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f688,f28])).

fof(f28,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f688,plain,(
    sK1 = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f687,f421])).

fof(f421,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f412,f28])).

fof(f412,plain,(
    ! [X10] : k5_xboole_0(sK1,X10) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X10)) ),
    inference(forward_demodulation,[],[f411,f300])).

fof(f300,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f43,f28])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f411,plain,(
    ! [X10] : k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X10)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X10)) ),
    inference(forward_demodulation,[],[f402,f391])).

fof(f391,plain,(
    ! [X4,X3] : k5_xboole_0(X4,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X3)) = k5_xboole_0(X4,k5_xboole_0(sK1,X3)) ),
    inference(superposition,[],[f300,f363])).

fof(f363,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0)) ),
    inference(superposition,[],[f43,f360])).

fof(f360,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f356,f28])).

fof(f356,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(superposition,[],[f351,f77])).

fof(f77,plain,(
    ! [X4] : k1_xboole_0 = k5_xboole_0(X4,X4) ),
    inference(forward_demodulation,[],[f75,f56])).

fof(f56,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(resolution,[],[f41,f29])).

fof(f29,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f75,plain,(
    ! [X4] : k4_xboole_0(X4,k1_zfmisc_1(k3_tarski(X4))) = k5_xboole_0(X4,X4) ),
    inference(superposition,[],[f34,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) = X0 ),
    inference(resolution,[],[f37,f29])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f351,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0)) ),
    inference(superposition,[],[f43,f345])).

fof(f345,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f335,f327])).

fof(f327,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f312,f73])).

fof(f73,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f34,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f312,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f43,f36])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f335,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(superposition,[],[f311,f77])).

fof(f311,plain,(
    ! [X23] : k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X23)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X23) ),
    inference(superposition,[],[f43,f126])).

fof(f126,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f73,f122])).

fof(f122,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f51,f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,X2)
      | k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2) ) ),
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f402,plain,(
    ! [X10] : k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X10)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X10)) ),
    inference(superposition,[],[f363,f300])).

fof(f687,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f674,f390])).

fof(f390,plain,(
    ! [X2] : k5_xboole_0(X2,k2_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(X2,sK1) ),
    inference(superposition,[],[f300,f360])).

fof(f674,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(superposition,[],[f538,f345])).

fof(f538,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k5_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f43,f506])).

fof(f506,plain,(
    k1_xboole_0 = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(superposition,[],[f390,f77])).

fof(f776,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f772,f35])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f772,plain,(
    k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f36,f767])).

fof(f767,plain,(
    sK1 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f763,f126])).

fof(f763,plain,(
    sK1 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f723,f43])).

fof(f723,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f213,f719])).

fof(f213,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f36,f122])).

fof(f230,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f229,f31])).

fof(f229,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))) ),
    inference(superposition,[],[f36,f220])).

fof(f220,plain,(
    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f219,f90])).

fof(f90,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f89,f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f89,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f35,f87])).

fof(f87,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f58,f25])).

fof(f58,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X3),X4) ) ),
    inference(resolution,[],[f41,f39])).

fof(f219,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f205,f124])).

fof(f124,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f122,f31])).

fof(f205,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f36,f126])).

fof(f26,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:44:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (6271)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (6271)Refutation not found, incomplete strategy% (6271)------------------------------
% 0.21/0.47  % (6271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (6271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (6271)Memory used [KB]: 10618
% 0.21/0.47  % (6271)Time elapsed: 0.046 s
% 0.21/0.47  % (6271)------------------------------
% 0.21/0.47  % (6271)------------------------------
% 0.21/0.47  % (6266)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (6262)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (6275)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (6274)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (6272)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (6263)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (6270)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (6267)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (6265)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.50  % (6264)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (6260)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (6261)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (6276)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (6268)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.53  % (6273)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.53  % (6269)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.55  % (6276)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f779,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f26,f778])).
% 0.21/0.55  fof(f778,plain,(
% 0.21/0.55    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.55    inference(backward_demodulation,[],[f230,f777])).
% 0.21/0.55  fof(f777,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.55    inference(forward_demodulation,[],[f776,f719])).
% 0.21/0.55  fof(f719,plain,(
% 0.21/0.55    sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.55    inference(superposition,[],[f688,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.55  fof(f688,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f687,f421])).
% 0.21/0.55  fof(f421,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.55    inference(superposition,[],[f412,f28])).
% 0.21/0.55  fof(f412,plain,(
% 0.21/0.55    ( ! [X10] : (k5_xboole_0(sK1,X10) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X10))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f411,f300])).
% 0.21/0.55  fof(f300,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 0.21/0.55    inference(superposition,[],[f43,f28])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.55  fof(f411,plain,(
% 0.21/0.55    ( ! [X10] : (k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X10)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X10))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f402,f391])).
% 0.21/0.55  fof(f391,plain,(
% 0.21/0.55    ( ! [X4,X3] : (k5_xboole_0(X4,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X3)) = k5_xboole_0(X4,k5_xboole_0(sK1,X3))) )),
% 0.21/0.55    inference(superposition,[],[f300,f363])).
% 0.21/0.55  fof(f363,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0))) )),
% 0.21/0.55    inference(superposition,[],[f43,f360])).
% 0.21/0.55  fof(f360,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.55    inference(forward_demodulation,[],[f356,f28])).
% 0.21/0.55  fof(f356,plain,(
% 0.21/0.55    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.55    inference(superposition,[],[f351,f77])).
% 0.21/0.55  fof(f77,plain,(
% 0.21/0.55    ( ! [X4] : (k1_xboole_0 = k5_xboole_0(X4,X4)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f75,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.55    inference(resolution,[],[f41,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.55  fof(f75,plain,(
% 0.21/0.55    ( ! [X4] : (k4_xboole_0(X4,k1_zfmisc_1(k3_tarski(X4))) = k5_xboole_0(X4,X4)) )),
% 0.21/0.55    inference(superposition,[],[f34,f50])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ( ! [X0] : (k3_xboole_0(X0,k1_zfmisc_1(k3_tarski(X0))) = X0) )),
% 0.21/0.55    inference(resolution,[],[f37,f29])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f351,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0))) )),
% 0.21/0.55    inference(superposition,[],[f43,f345])).
% 0.21/0.55  fof(f345,plain,(
% 0.21/0.55    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.55    inference(forward_demodulation,[],[f335,f327])).
% 0.21/0.55  fof(f327,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f312,f73])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 0.21/0.55    inference(superposition,[],[f34,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f312,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 0.21/0.55    inference(superposition,[],[f43,f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f9])).
% 0.21/0.55  fof(f9,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.55  fof(f335,plain,(
% 0.21/0.55    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.55    inference(superposition,[],[f311,f77])).
% 0.21/0.55  fof(f311,plain,(
% 0.21/0.55    ( ! [X23] : (k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X23)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X23)) )),
% 0.21/0.55    inference(superposition,[],[f43,f126])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.55    inference(superposition,[],[f73,f122])).
% 0.21/0.55  fof(f122,plain,(
% 0.21/0.55    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.55    inference(resolution,[],[f51,f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f19,f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.55    inference(negated_conjecture,[],[f17])).
% 0.21/0.55  fof(f17,conjecture,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X2,X1] : (~r2_hidden(X1,X2) | k1_tarski(X1) = k3_xboole_0(k1_tarski(X1),X2)) )),
% 0.21/0.55    inference(resolution,[],[f37,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.55  fof(f402,plain,(
% 0.21/0.55    ( ! [X10] : (k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X10)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X10))) )),
% 0.21/0.55    inference(superposition,[],[f363,f300])).
% 0.21/0.55  fof(f687,plain,(
% 0.21/0.55    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f674,f390])).
% 0.21/0.55  fof(f390,plain,(
% 0.21/0.55    ( ! [X2] : (k5_xboole_0(X2,k2_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(X2,sK1)) )),
% 0.21/0.55    inference(superposition,[],[f300,f360])).
% 0.21/0.55  fof(f674,plain,(
% 0.21/0.55    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.55    inference(superposition,[],[f538,f345])).
% 0.21/0.55  fof(f538,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k5_xboole_0(sK1,X0))) )),
% 0.21/0.55    inference(superposition,[],[f43,f506])).
% 0.21/0.55  fof(f506,plain,(
% 0.21/0.55    k1_xboole_0 = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.21/0.55    inference(superposition,[],[f390,f77])).
% 0.21/0.55  fof(f776,plain,(
% 0.21/0.55    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.55    inference(forward_demodulation,[],[f772,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.55  fof(f772,plain,(
% 0.21/0.55    k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.55    inference(superposition,[],[f36,f767])).
% 0.21/0.55  fof(f767,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.55    inference(forward_demodulation,[],[f763,f126])).
% 0.21/0.55  fof(f763,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.55    inference(superposition,[],[f723,f43])).
% 0.21/0.55  fof(f723,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 0.21/0.55    inference(backward_demodulation,[],[f213,f719])).
% 0.21/0.55  fof(f213,plain,(
% 0.21/0.55    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 0.21/0.55    inference(superposition,[],[f36,f122])).
% 0.21/0.55  fof(f230,plain,(
% 0.21/0.55    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.55    inference(forward_demodulation,[],[f229,f31])).
% 0.21/0.55  fof(f229,plain,(
% 0.21/0.55    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)))),
% 0.21/0.55    inference(superposition,[],[f36,f220])).
% 0.21/0.55  fof(f220,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f219,f90])).
% 0.21/0.55  fof(f90,plain,(
% 0.21/0.55    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f89,f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.55    inference(superposition,[],[f35,f87])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.55    inference(resolution,[],[f58,f25])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X4,X3] : (~r2_hidden(X3,X4) | k1_xboole_0 = k4_xboole_0(k1_tarski(X3),X4)) )),
% 0.21/0.55    inference(resolution,[],[f41,f39])).
% 0.21/0.55  fof(f219,plain,(
% 0.21/0.55    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f205,f124])).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.55    inference(superposition,[],[f122,f31])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.55    inference(superposition,[],[f36,f126])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (6276)------------------------------
% 0.21/0.55  % (6276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6276)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (6276)Memory used [KB]: 6780
% 0.21/0.55  % (6276)Time elapsed: 0.105 s
% 0.21/0.55  % (6276)------------------------------
% 0.21/0.55  % (6276)------------------------------
% 0.21/0.55  % (6259)Success in time 0.192 s
%------------------------------------------------------------------------------
