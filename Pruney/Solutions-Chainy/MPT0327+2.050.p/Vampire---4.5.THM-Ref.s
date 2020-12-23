%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 983 expanded)
%              Number of leaves         :   13 ( 299 expanded)
%              Depth                    :   27
%              Number of atoms          :  110 (1395 expanded)
%              Number of equality atoms :   81 ( 877 expanded)
%              Maximal formula depth    :    6 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1038,plain,(
    $false ),
    inference(subsumption_resolution,[],[f29,f1037])).

fof(f1037,plain,(
    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f290,f1036])).

fof(f1036,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f1035,f980])).

fof(f980,plain,(
    sK1 = k2_xboole_0(k1_tarski(sK0),sK1) ),
    inference(superposition,[],[f941,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f941,plain,(
    sK1 = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f940,f707])).

fof(f707,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(superposition,[],[f697,f31])).

fof(f697,plain,(
    ! [X15] : k5_xboole_0(sK1,X15) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X15)) ),
    inference(forward_demodulation,[],[f696,f238])).

fof(f238,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f49,f31])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f696,plain,(
    ! [X15] : k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X15)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X15)) ),
    inference(forward_demodulation,[],[f676,f660])).

fof(f660,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X1)) = k5_xboole_0(X2,k5_xboole_0(sK1,X1)) ),
    inference(superposition,[],[f238,f436])).

fof(f436,plain,(
    ! [X0] : k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0)) ),
    inference(superposition,[],[f49,f432])).

fof(f432,plain,(
    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f428,f31])).

fof(f428,plain,(
    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(superposition,[],[f423,f88])).

fof(f88,plain,(
    ! [X5] : k1_xboole_0 = k5_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f85,f69])).

fof(f69,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,k1_zfmisc_1(k3_tarski(X1))) ),
    inference(resolution,[],[f47,f32])).

fof(f32,plain,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f85,plain,(
    ! [X5] : k4_xboole_0(X5,k1_zfmisc_1(k3_tarski(X5))) = k5_xboole_0(X5,X5) ),
    inference(superposition,[],[f38,f54])).

fof(f54,plain,(
    ! [X1] : k3_xboole_0(X1,k1_zfmisc_1(k3_tarski(X1))) = X1 ),
    inference(resolution,[],[f41,f32])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f423,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0)) ),
    inference(superposition,[],[f49,f417])).

fof(f417,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(forward_demodulation,[],[f407,f258])).

fof(f258,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f245,f82])).

fof(f82,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f38,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f245,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    inference(superposition,[],[f49,f40])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f407,plain,(
    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(superposition,[],[f242,f88])).

fof(f242,plain,(
    ! [X10] : k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X10)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X10) ),
    inference(superposition,[],[f49,f131])).

fof(f131,plain,(
    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f82,f127])).

fof(f127,plain,(
    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f55,f28])).

fof(f28,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).

fof(f23,plain,
    ( ? [X0,X1] :
        ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
        & r2_hidden(X0,X1) )
   => ( sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1] :
      ( k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r2_hidden(X0,X1)
       => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

fof(f55,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X2,X3)
      | k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),X3) ) ),
    inference(resolution,[],[f41,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f676,plain,(
    ! [X15] : k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X15)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X15)) ),
    inference(superposition,[],[f436,f238])).

fof(f940,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f925,f659])).

fof(f659,plain,(
    ! [X0] : k5_xboole_0(X0,k2_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(X0,sK1) ),
    inference(superposition,[],[f238,f432])).

fof(f925,plain,(
    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1)) ),
    inference(superposition,[],[f834,f417])).

fof(f834,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k5_xboole_0(sK1,X0)) ),
    inference(superposition,[],[f49,f783])).

fof(f783,plain,(
    k1_xboole_0 = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1) ),
    inference(superposition,[],[f659,f88])).

fof(f1035,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f1031,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1031,plain,(
    k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f40,f1026])).

fof(f1026,plain,(
    sK1 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(forward_demodulation,[],[f1022,f131])).

fof(f1022,plain,(
    sK1 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f984,f49])).

fof(f984,plain,(
    sK1 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f201,f980])).

fof(f201,plain,(
    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0)) ),
    inference(superposition,[],[f40,f127])).

fof(f290,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) ),
    inference(forward_demodulation,[],[f289,f35])).

fof(f289,plain,(
    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))) ),
    inference(superposition,[],[f40,f223])).

fof(f223,plain,(
    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f222,f211])).

fof(f211,plain,(
    sK1 = k2_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(backward_demodulation,[],[f102,f205])).

fof(f205,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f204,f87])).

fof(f87,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = X4 ),
    inference(forward_demodulation,[],[f84,f31])).

fof(f84,plain,(
    ! [X4] : k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f38,f56])).

fof(f56,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) ),
    inference(superposition,[],[f53,f35])).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(resolution,[],[f41,f30])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f204,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f189,f38])).

fof(f189,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0)) ),
    inference(superposition,[],[f40,f31])).

fof(f102,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f39,f99])).

fof(f99,plain,(
    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(resolution,[],[f71,f28])).

fof(f71,plain,(
    ! [X4,X5] :
      ( ~ r2_hidden(X4,X5)
      | k1_xboole_0 = k4_xboole_0(k1_tarski(X4),X5) ) ),
    inference(resolution,[],[f47,f45])).

fof(f222,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(forward_demodulation,[],[f193,f129])).

fof(f129,plain,(
    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f127,f35])).

fof(f193,plain,(
    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0))) ),
    inference(superposition,[],[f40,f131])).

fof(f29,plain,(
    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:23:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (31083)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (31086)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (31085)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (31091)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (31095)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (31091)Refutation not found, incomplete strategy% (31091)------------------------------
% 0.21/0.48  % (31091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (31091)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (31091)Memory used [KB]: 10618
% 0.21/0.48  % (31091)Time elapsed: 0.061 s
% 0.21/0.48  % (31091)------------------------------
% 0.21/0.48  % (31091)------------------------------
% 0.21/0.49  % (31094)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (31093)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (31081)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (31087)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (31084)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (31080)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (31089)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.51  % (31092)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.51  % (31082)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.51  % (31096)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.52  % (31088)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (31090)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.53  % (31097)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.55  % (31096)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f1038,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(subsumption_resolution,[],[f29,f1037])).
% 0.21/0.55  fof(f1037,plain,(
% 0.21/0.55    sK1 = k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.55    inference(backward_demodulation,[],[f290,f1036])).
% 0.21/0.55  fof(f1036,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.55    inference(forward_demodulation,[],[f1035,f980])).
% 0.21/0.55  fof(f980,plain,(
% 0.21/0.55    sK1 = k2_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.55    inference(superposition,[],[f941,f31])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.55  fof(f941,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0)),
% 0.21/0.55    inference(forward_demodulation,[],[f940,f707])).
% 0.21/0.55  fof(f707,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.55    inference(superposition,[],[f697,f31])).
% 0.21/0.55  fof(f697,plain,(
% 0.21/0.55    ( ! [X15] : (k5_xboole_0(sK1,X15) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X15))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f696,f238])).
% 0.21/0.55  fof(f238,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k1_xboole_0,X1))) )),
% 0.21/0.55    inference(superposition,[],[f49,f31])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.55  fof(f696,plain,(
% 0.21/0.55    ( ! [X15] : (k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X15)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,X15))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f676,f660])).
% 0.21/0.55  fof(f660,plain,(
% 0.21/0.55    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X1)) = k5_xboole_0(X2,k5_xboole_0(sK1,X1))) )),
% 0.21/0.55    inference(superposition,[],[f238,f436])).
% 0.21/0.55  fof(f436,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(sK1,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0))) )),
% 0.21/0.55    inference(superposition,[],[f49,f432])).
% 0.21/0.55  fof(f432,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.55    inference(forward_demodulation,[],[f428,f31])).
% 0.21/0.55  fof(f428,plain,(
% 0.21/0.55    k5_xboole_0(sK1,k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.55    inference(superposition,[],[f423,f88])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    ( ! [X5] : (k1_xboole_0 = k5_xboole_0(X5,X5)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f85,f69])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k1_zfmisc_1(k3_tarski(X1)))) )),
% 0.21/0.55    inference(resolution,[],[f47,f32])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(X0,k1_zfmisc_1(k3_tarski(X0)))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.55    inference(nnf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.55  fof(f85,plain,(
% 0.21/0.55    ( ! [X5] : (k4_xboole_0(X5,k1_zfmisc_1(k3_tarski(X5))) = k5_xboole_0(X5,X5)) )),
% 0.21/0.55    inference(superposition,[],[f38,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X1] : (k3_xboole_0(X1,k1_zfmisc_1(k3_tarski(X1))) = X1) )),
% 0.21/0.55    inference(resolution,[],[f41,f32])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.55  fof(f423,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK1,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X0))) )),
% 0.21/0.55    inference(superposition,[],[f49,f417])).
% 0.21/0.55  fof(f417,plain,(
% 0.21/0.55    k1_xboole_0 = k5_xboole_0(sK1,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.55    inference(forward_demodulation,[],[f407,f258])).
% 0.21/0.55  fof(f258,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.55    inference(forward_demodulation,[],[f245,f82])).
% 0.21/0.55  fof(f82,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 0.21/0.55    inference(superposition,[],[f38,f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.55  fof(f245,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) )),
% 0.21/0.55    inference(superposition,[],[f49,f40])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.55    inference(cnf_transformation,[],[f11])).
% 0.21/0.55  fof(f11,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.55  fof(f407,plain,(
% 0.21/0.55    k1_xboole_0 = k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.55    inference(superposition,[],[f242,f88])).
% 0.21/0.55  fof(f242,plain,(
% 0.21/0.55    ( ! [X10] : (k5_xboole_0(sK1,k5_xboole_0(k1_tarski(sK0),X10)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),X10)) )),
% 0.21/0.55    inference(superposition,[],[f49,f131])).
% 0.21/0.55  fof(f131,plain,(
% 0.21/0.55    k4_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.55    inference(superposition,[],[f82,f127])).
% 0.21/0.55  fof(f127,plain,(
% 0.21/0.55    k1_tarski(sK0) = k3_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.55    inference(resolution,[],[f55,f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    r2_hidden(sK0,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f21,f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1)) => (sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) & r2_hidden(sK0,sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ? [X0,X1] : (k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & r2_hidden(X0,X1))),
% 0.21/0.55    inference(ennf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,negated_conjecture,(
% 0.21/0.55    ~! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.55    inference(negated_conjecture,[],[f19])).
% 0.21/0.55  fof(f19,conjecture,(
% 0.21/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => k2_xboole_0(k4_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X2,X3] : (~r2_hidden(X2,X3) | k1_tarski(X2) = k3_xboole_0(k1_tarski(X2),X3)) )),
% 0.21/0.55    inference(resolution,[],[f41,f45])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f26])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.55    inference(nnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,axiom,(
% 0.21/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.55  fof(f676,plain,(
% 0.21/0.55    ( ! [X15] : (k5_xboole_0(sK1,k5_xboole_0(k1_xboole_0,X15)) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),X15))) )),
% 0.21/0.55    inference(superposition,[],[f436,f238])).
% 0.21/0.55  fof(f940,plain,(
% 0.21/0.55    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,sK1)),
% 0.21/0.55    inference(forward_demodulation,[],[f925,f659])).
% 0.21/0.55  fof(f659,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(X0,k2_xboole_0(k1_tarski(sK0),sK1)) = k5_xboole_0(X0,sK1)) )),
% 0.21/0.55    inference(superposition,[],[f238,f432])).
% 0.21/0.55  fof(f925,plain,(
% 0.21/0.55    k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(k1_tarski(sK0),sK1))),
% 0.21/0.55    inference(superposition,[],[f834,f417])).
% 0.21/0.55  fof(f834,plain,(
% 0.21/0.55    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),k5_xboole_0(sK1,X0))) )),
% 0.21/0.55    inference(superposition,[],[f49,f783])).
% 0.21/0.55  fof(f783,plain,(
% 0.21/0.55    k1_xboole_0 = k5_xboole_0(k2_xboole_0(k1_tarski(sK0),sK1),sK1)),
% 0.21/0.55    inference(superposition,[],[f659,f88])).
% 0.21/0.55  fof(f1035,plain,(
% 0.21/0.55    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.55    inference(forward_demodulation,[],[f1031,f39])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.55  fof(f1031,plain,(
% 0.21/0.55    k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))) = k2_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.55    inference(superposition,[],[f40,f1026])).
% 0.21/0.55  fof(f1026,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.55    inference(forward_demodulation,[],[f1022,f131])).
% 0.21/0.55  fof(f1022,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k1_tarski(sK0),k5_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.55    inference(superposition,[],[f984,f49])).
% 0.21/0.55  fof(f984,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 0.21/0.55    inference(backward_demodulation,[],[f201,f980])).
% 0.21/0.55  fof(f201,plain,(
% 0.21/0.55    k2_xboole_0(k1_tarski(sK0),sK1) = k5_xboole_0(k5_xboole_0(k1_tarski(sK0),sK1),k1_tarski(sK0))),
% 0.21/0.55    inference(superposition,[],[f40,f127])).
% 0.21/0.55  fof(f290,plain,(
% 0.21/0.55    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k1_tarski(sK0),k4_xboole_0(sK1,k1_tarski(sK0))))),
% 0.21/0.55    inference(forward_demodulation,[],[f289,f35])).
% 0.21/0.55  fof(f289,plain,(
% 0.21/0.55    k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) = k5_xboole_0(sK1,k3_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)))),
% 0.21/0.55    inference(superposition,[],[f40,f223])).
% 0.21/0.55  fof(f223,plain,(
% 0.21/0.55    sK1 = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f222,f211])).
% 0.21/0.55  fof(f211,plain,(
% 0.21/0.55    sK1 = k2_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.55    inference(backward_demodulation,[],[f102,f205])).
% 0.21/0.55  fof(f205,plain,(
% 0.21/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.55    inference(forward_demodulation,[],[f204,f87])).
% 0.21/0.55  fof(f87,plain,(
% 0.21/0.55    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 0.21/0.55    inference(forward_demodulation,[],[f84,f31])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    ( ! [X4] : (k4_xboole_0(X4,k1_xboole_0) = k5_xboole_0(X4,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f38,f56])).
% 0.21/0.55  fof(f56,plain,(
% 0.21/0.55    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0)) )),
% 0.21/0.55    inference(superposition,[],[f53,f35])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(resolution,[],[f41,f30])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.21/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.21/0.55  fof(f204,plain,(
% 0.21/0.55    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = k2_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.55    inference(forward_demodulation,[],[f189,f38])).
% 0.21/0.55  fof(f189,plain,(
% 0.21/0.55    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k3_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.55    inference(superposition,[],[f40,f31])).
% 0.21/0.55  fof(f102,plain,(
% 0.21/0.55    k2_xboole_0(sK1,k1_tarski(sK0)) = k2_xboole_0(sK1,k1_xboole_0)),
% 0.21/0.55    inference(superposition,[],[f39,f99])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    k1_xboole_0 = k4_xboole_0(k1_tarski(sK0),sK1)),
% 0.21/0.55    inference(resolution,[],[f71,f28])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    ( ! [X4,X5] : (~r2_hidden(X4,X5) | k1_xboole_0 = k4_xboole_0(k1_tarski(X4),X5)) )),
% 0.21/0.55    inference(resolution,[],[f47,f45])).
% 0.21/0.55  fof(f222,plain,(
% 0.21/0.55    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.55    inference(forward_demodulation,[],[f193,f129])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    k1_tarski(sK0) = k3_xboole_0(sK1,k1_tarski(sK0))),
% 0.21/0.55    inference(superposition,[],[f127,f35])).
% 0.21/0.55  fof(f193,plain,(
% 0.21/0.55    k2_xboole_0(sK1,k1_tarski(sK0)) = k5_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k3_xboole_0(sK1,k1_tarski(sK0)))),
% 0.21/0.55    inference(superposition,[],[f40,f131])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    sK1 != k2_xboole_0(k4_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 0.21/0.55    inference(cnf_transformation,[],[f24])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (31096)------------------------------
% 0.21/0.55  % (31096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (31096)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (31096)Memory used [KB]: 6780
% 0.21/0.55  % (31096)Time elapsed: 0.131 s
% 0.21/0.55  % (31096)------------------------------
% 0.21/0.55  % (31096)------------------------------
% 0.21/0.55  % (31079)Success in time 0.186 s
%------------------------------------------------------------------------------
