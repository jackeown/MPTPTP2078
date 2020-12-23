%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:58 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 539 expanded)
%              Number of leaves         :   18 ( 165 expanded)
%              Depth                    :   24
%              Number of atoms          :  128 ( 621 expanded)
%              Number of equality atoms :   88 ( 545 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1380,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1371,f1255])).

fof(f1255,plain,(
    r2_hidden(sK0,sK1) ),
    inference(subsumption_resolution,[],[f40,f1254])).

fof(f1254,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(backward_demodulation,[],[f466,f1242])).

fof(f1242,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(X16,k2_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f1213,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f1213,plain,(
    ! [X15,X16] : k5_xboole_0(X15,k3_xboole_0(X15,X16)) = k5_xboole_0(X16,k2_xboole_0(X15,X16)) ),
    inference(superposition,[],[f181,f168])).

fof(f168,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f57,f53])).

fof(f53,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f181,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f160,f129])).

fof(f129,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f128,f44])).

fof(f44,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f128,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f115,f45])).

fof(f45,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f115,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f53,f41])).

fof(f41,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f160,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f57,f41])).

fof(f466,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k5_xboole_0(X1,k2_xboole_0(k1_tarski(X0),X1))
      | r2_hidden(X0,X1) ) ),
    inference(backward_demodulation,[],[f114,f463])).

fof(f463,plain,(
    ! [X4,X3] : k4_xboole_0(k2_xboole_0(X3,X4),X4) = k5_xboole_0(X4,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f462,f47])).

fof(f47,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f462,plain,(
    ! [X4,X3] : k4_xboole_0(k2_xboole_0(X3,X4),X4) = k5_xboole_0(k2_xboole_0(X3,X4),X4) ),
    inference(superposition,[],[f50,f438])).

fof(f438,plain,(
    ! [X2,X1] : k3_xboole_0(k2_xboole_0(X2,X1),X1) = X1 ),
    inference(superposition,[],[f435,f77])).

fof(f77,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f71,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f71,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f49,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f435,plain,(
    ! [X4,X5] : k3_xboole_0(k2_xboole_0(X4,X5),X4) = X4 ),
    inference(forward_demodulation,[],[f426,f206])).

fof(f206,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f185,f185])).

fof(f185,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f181,f47])).

fof(f426,plain,(
    ! [X4,X5] : k3_xboole_0(k2_xboole_0(X4,X5),X4) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X4,X5),X4),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f53,f244])).

fof(f244,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f243,f42])).

fof(f42,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f243,plain,(
    ! [X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f52,f234])).

fof(f234,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f233,f41])).

fof(f233,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f50,f219])).

fof(f219,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f123,f205])).

fof(f205,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f185,f181])).

fof(f123,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f53,f51])).

fof(f51,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f114,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),X1)
      | r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f55,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f40,plain,
    ( k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( ( r2_hidden(sK0,sK1)
      | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
    & ( ~ r2_hidden(sK0,sK1)
      | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).

fof(f35,plain,
    ( ? [X0,X1] :
        ( ( r2_hidden(X0,X1)
          | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
        & ( ~ r2_hidden(X0,X1)
          | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) )
   => ( ( r2_hidden(sK0,sK1)
        | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) )
      & ( ~ r2_hidden(sK0,sK1)
        | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ? [X0,X1] :
      ( ( r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ? [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <~> ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      <=> ~ r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

fof(f1371,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f69,f1358])).

fof(f1358,plain,(
    sK1 = k4_xboole_0(sK1,k1_tarski(sK0)) ),
    inference(superposition,[],[f1326,f1256])).

fof(f1256,plain,(
    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(subsumption_resolution,[],[f39,f1255])).

fof(f39,plain,
    ( ~ r2_hidden(sK0,sK1)
    | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f1326,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(X12,X11)) = X11 ),
    inference(forward_demodulation,[],[f1291,f1247])).

fof(f1247,plain,(
    ! [X8,X7] : k5_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8)) = X7 ),
    inference(backward_demodulation,[],[f695,f1242])).

fof(f695,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X7,X8)) = X7 ),
    inference(forward_demodulation,[],[f671,f220])).

fof(f220,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7 ),
    inference(backward_demodulation,[],[f124,f205])).

fof(f124,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X8,X7)) ),
    inference(superposition,[],[f53,f92])).

fof(f92,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f51,f77])).

fof(f671,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X7,X8)) ),
    inference(superposition,[],[f53,f421])).

fof(f421,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f244,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f1291,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f1242,f52])).

fof(f69,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2))) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:50:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.51  % (21773)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (21765)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.52  % (21757)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (21758)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.53  % (21751)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (21754)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (21753)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (21776)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (21778)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (21752)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (21759)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (21769)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (21777)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (21770)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (21774)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (21756)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (21768)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (21762)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (21761)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (21775)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (21750)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.56  % (21760)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.56  % (21767)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (21766)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.56  % (21755)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.56  % (21772)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.45/0.57  % (21772)Refutation not found, incomplete strategy% (21772)------------------------------
% 1.45/0.57  % (21772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (21770)Refutation not found, incomplete strategy% (21770)------------------------------
% 1.45/0.57  % (21770)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (21770)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (21770)Memory used [KB]: 10746
% 1.45/0.57  % (21770)Time elapsed: 0.139 s
% 1.45/0.57  % (21770)------------------------------
% 1.45/0.57  % (21770)------------------------------
% 1.45/0.57  % (21772)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (21772)Memory used [KB]: 10746
% 1.45/0.57  % (21772)Time elapsed: 0.134 s
% 1.45/0.57  % (21772)------------------------------
% 1.45/0.57  % (21772)------------------------------
% 1.45/0.58  % (21767)Refutation not found, incomplete strategy% (21767)------------------------------
% 1.45/0.58  % (21767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (21767)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (21767)Memory used [KB]: 10618
% 1.45/0.58  % (21767)Time elapsed: 0.167 s
% 1.45/0.58  % (21767)------------------------------
% 1.45/0.58  % (21767)------------------------------
% 1.74/0.59  % (21764)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.74/0.60  % (21779)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.74/0.60  % (21771)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.74/0.61  % (21763)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.74/0.63  % (21757)Refutation found. Thanks to Tanya!
% 1.74/0.63  % SZS status Theorem for theBenchmark
% 1.74/0.63  % SZS output start Proof for theBenchmark
% 1.74/0.63  fof(f1380,plain,(
% 1.74/0.63    $false),
% 1.74/0.63    inference(subsumption_resolution,[],[f1371,f1255])).
% 1.74/0.63  fof(f1255,plain,(
% 1.74/0.63    r2_hidden(sK0,sK1)),
% 1.74/0.63    inference(subsumption_resolution,[],[f40,f1254])).
% 1.74/0.63  fof(f1254,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.74/0.63    inference(backward_demodulation,[],[f466,f1242])).
% 1.74/0.63  fof(f1242,plain,(
% 1.74/0.63    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k5_xboole_0(X16,k2_xboole_0(X15,X16))) )),
% 1.74/0.63    inference(forward_demodulation,[],[f1213,f50])).
% 1.74/0.63  fof(f50,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.74/0.63    inference(cnf_transformation,[],[f4])).
% 1.74/0.63  fof(f4,axiom,(
% 1.74/0.63    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.74/0.63  fof(f1213,plain,(
% 1.74/0.63    ( ! [X15,X16] : (k5_xboole_0(X15,k3_xboole_0(X15,X16)) = k5_xboole_0(X16,k2_xboole_0(X15,X16))) )),
% 1.74/0.63    inference(superposition,[],[f181,f168])).
% 1.74/0.63  fof(f168,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 1.74/0.63    inference(superposition,[],[f57,f53])).
% 1.74/0.63  fof(f53,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.74/0.63    inference(cnf_transformation,[],[f12])).
% 1.74/0.63  fof(f12,axiom,(
% 1.74/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.74/0.63  fof(f57,plain,(
% 1.74/0.63    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.74/0.63    inference(cnf_transformation,[],[f10])).
% 1.74/0.63  fof(f10,axiom,(
% 1.74/0.63    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.74/0.63  fof(f181,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.74/0.63    inference(forward_demodulation,[],[f160,f129])).
% 1.74/0.63  fof(f129,plain,(
% 1.74/0.63    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.74/0.63    inference(forward_demodulation,[],[f128,f44])).
% 1.74/0.63  fof(f44,plain,(
% 1.74/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.74/0.63    inference(cnf_transformation,[],[f29])).
% 1.74/0.63  fof(f29,plain,(
% 1.74/0.63    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.74/0.63    inference(rectify,[],[f3])).
% 1.74/0.63  fof(f3,axiom,(
% 1.74/0.63    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.74/0.63  fof(f128,plain,(
% 1.74/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 1.74/0.63    inference(forward_demodulation,[],[f115,f45])).
% 1.74/0.63  fof(f45,plain,(
% 1.74/0.63    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.74/0.63    inference(cnf_transformation,[],[f30])).
% 1.74/0.63  fof(f30,plain,(
% 1.74/0.63    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.74/0.63    inference(rectify,[],[f2])).
% 1.74/0.63  fof(f2,axiom,(
% 1.74/0.63    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.74/0.63  fof(f115,plain,(
% 1.74/0.63    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 1.74/0.63    inference(superposition,[],[f53,f41])).
% 1.74/0.63  fof(f41,plain,(
% 1.74/0.63    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f11])).
% 1.74/0.63  fof(f11,axiom,(
% 1.74/0.63    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.74/0.63  fof(f160,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.74/0.63    inference(superposition,[],[f57,f41])).
% 1.74/0.63  fof(f466,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k1_tarski(X0) = k5_xboole_0(X1,k2_xboole_0(k1_tarski(X0),X1)) | r2_hidden(X0,X1)) )),
% 1.74/0.63    inference(backward_demodulation,[],[f114,f463])).
% 1.74/0.63  fof(f463,plain,(
% 1.74/0.63    ( ! [X4,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),X4) = k5_xboole_0(X4,k2_xboole_0(X3,X4))) )),
% 1.74/0.63    inference(forward_demodulation,[],[f462,f47])).
% 1.74/0.63  fof(f47,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f1])).
% 1.74/0.63  fof(f1,axiom,(
% 1.74/0.63    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.74/0.63  fof(f462,plain,(
% 1.74/0.63    ( ! [X4,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),X4) = k5_xboole_0(k2_xboole_0(X3,X4),X4)) )),
% 1.74/0.63    inference(superposition,[],[f50,f438])).
% 1.74/0.63  fof(f438,plain,(
% 1.74/0.63    ( ! [X2,X1] : (k3_xboole_0(k2_xboole_0(X2,X1),X1) = X1) )),
% 1.74/0.63    inference(superposition,[],[f435,f77])).
% 1.74/0.63  fof(f77,plain,(
% 1.74/0.63    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 1.74/0.63    inference(superposition,[],[f71,f49])).
% 1.74/0.63  fof(f49,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.74/0.63    inference(cnf_transformation,[],[f25])).
% 1.74/0.63  fof(f25,axiom,(
% 1.74/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.74/0.63  fof(f71,plain,(
% 1.74/0.63    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 1.74/0.63    inference(superposition,[],[f49,f46])).
% 1.74/0.63  fof(f46,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f13])).
% 1.74/0.63  fof(f13,axiom,(
% 1.74/0.63    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 1.74/0.63  fof(f435,plain,(
% 1.74/0.63    ( ! [X4,X5] : (k3_xboole_0(k2_xboole_0(X4,X5),X4) = X4) )),
% 1.74/0.63    inference(forward_demodulation,[],[f426,f206])).
% 1.74/0.63  fof(f206,plain,(
% 1.74/0.63    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 1.74/0.63    inference(superposition,[],[f185,f185])).
% 1.74/0.63  fof(f185,plain,(
% 1.74/0.63    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.74/0.63    inference(superposition,[],[f181,f47])).
% 1.74/0.63  fof(f426,plain,(
% 1.74/0.63    ( ! [X4,X5] : (k3_xboole_0(k2_xboole_0(X4,X5),X4) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X4,X5),X4),k2_xboole_0(X4,X5))) )),
% 1.74/0.63    inference(superposition,[],[f53,f244])).
% 1.74/0.63  fof(f244,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k2_xboole_0(X0,X1),X0)) )),
% 1.74/0.63    inference(forward_demodulation,[],[f243,f42])).
% 1.74/0.63  fof(f42,plain,(
% 1.74/0.63    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.74/0.63    inference(cnf_transformation,[],[f5])).
% 1.74/0.63  fof(f5,axiom,(
% 1.74/0.63    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.74/0.63  fof(f243,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X0) = k2_xboole_0(k2_xboole_0(X0,X1),k1_xboole_0)) )),
% 1.74/0.63    inference(superposition,[],[f52,f234])).
% 1.74/0.63  fof(f234,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.74/0.63    inference(forward_demodulation,[],[f233,f41])).
% 1.74/0.63  fof(f233,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.74/0.63    inference(superposition,[],[f50,f219])).
% 1.74/0.63  fof(f219,plain,(
% 1.74/0.63    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5) )),
% 1.74/0.63    inference(backward_demodulation,[],[f123,f205])).
% 1.74/0.63  fof(f205,plain,(
% 1.74/0.63    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 1.74/0.63    inference(superposition,[],[f185,f181])).
% 1.74/0.63  fof(f123,plain,(
% 1.74/0.63    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6))) )),
% 1.74/0.63    inference(superposition,[],[f53,f51])).
% 1.74/0.63  fof(f51,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 1.74/0.63    inference(cnf_transformation,[],[f8])).
% 1.74/0.63  fof(f8,axiom,(
% 1.74/0.63    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 1.74/0.63  fof(f52,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f6])).
% 1.74/0.63  fof(f6,axiom,(
% 1.74/0.63    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.74/0.63  fof(f114,plain,(
% 1.74/0.63    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k2_xboole_0(k1_tarski(X0),X1),X1) | r2_hidden(X0,X1)) )),
% 1.74/0.63    inference(resolution,[],[f55,f54])).
% 1.74/0.63  fof(f54,plain,(
% 1.74/0.63    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 1.74/0.63    inference(cnf_transformation,[],[f32])).
% 1.74/0.63  fof(f32,plain,(
% 1.74/0.63    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 1.74/0.63    inference(ennf_transformation,[],[f24])).
% 1.74/0.63  fof(f24,axiom,(
% 1.74/0.63    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 1.74/0.63  fof(f55,plain,(
% 1.74/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 1.74/0.63    inference(cnf_transformation,[],[f33])).
% 1.74/0.63  fof(f33,plain,(
% 1.74/0.63    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 1.74/0.63    inference(ennf_transformation,[],[f9])).
% 1.74/0.63  fof(f9,axiom,(
% 1.74/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 1.74/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 1.74/0.63  fof(f40,plain,(
% 1.74/0.63    k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1) | r2_hidden(sK0,sK1)),
% 1.74/0.63    inference(cnf_transformation,[],[f36])).
% 1.74/0.63  fof(f36,plain,(
% 1.74/0.63    (r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1))),
% 1.74/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f34,f35])).
% 1.74/0.63  fof(f35,plain,(
% 1.74/0.63    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1))) => ((r2_hidden(sK0,sK1) | k1_tarski(sK0) != k4_xboole_0(k1_tarski(sK0),sK1)) & (~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)))),
% 1.74/0.63    introduced(choice_axiom,[])).
% 1.74/0.64  fof(f34,plain,(
% 1.74/0.64    ? [X0,X1] : ((r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)))),
% 1.74/0.64    inference(nnf_transformation,[],[f31])).
% 1.74/0.64  fof(f31,plain,(
% 1.74/0.64    ? [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <~> ~r2_hidden(X0,X1))),
% 1.74/0.64    inference(ennf_transformation,[],[f28])).
% 1.74/0.64  fof(f28,negated_conjecture,(
% 1.74/0.64    ~! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.74/0.64    inference(negated_conjecture,[],[f27])).
% 1.74/0.64  fof(f27,conjecture,(
% 1.74/0.64    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 1.74/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).
% 1.74/0.64  fof(f1371,plain,(
% 1.74/0.64    ~r2_hidden(sK0,sK1)),
% 1.74/0.64    inference(superposition,[],[f69,f1358])).
% 1.74/0.64  fof(f1358,plain,(
% 1.74/0.64    sK1 = k4_xboole_0(sK1,k1_tarski(sK0))),
% 1.74/0.64    inference(superposition,[],[f1326,f1256])).
% 1.74/0.64  fof(f1256,plain,(
% 1.74/0.64    k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.74/0.64    inference(subsumption_resolution,[],[f39,f1255])).
% 1.74/0.64  fof(f39,plain,(
% 1.74/0.64    ~r2_hidden(sK0,sK1) | k1_tarski(sK0) = k4_xboole_0(k1_tarski(sK0),sK1)),
% 1.74/0.64    inference(cnf_transformation,[],[f36])).
% 1.74/0.64  fof(f1326,plain,(
% 1.74/0.64    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(X12,X11)) = X11) )),
% 1.74/0.64    inference(forward_demodulation,[],[f1291,f1247])).
% 1.74/0.64  fof(f1247,plain,(
% 1.74/0.64    ( ! [X8,X7] : (k5_xboole_0(k4_xboole_0(X8,X7),k2_xboole_0(X7,X8)) = X7) )),
% 1.74/0.64    inference(backward_demodulation,[],[f695,f1242])).
% 1.74/0.64  fof(f695,plain,(
% 1.74/0.64    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X7,X8)) = X7) )),
% 1.74/0.64    inference(forward_demodulation,[],[f671,f220])).
% 1.74/0.64  fof(f220,plain,(
% 1.74/0.64    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7) )),
% 1.74/0.64    inference(backward_demodulation,[],[f124,f205])).
% 1.74/0.64  fof(f124,plain,(
% 1.74/0.64    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X8,X7))) )),
% 1.74/0.64    inference(superposition,[],[f53,f92])).
% 1.74/0.64  fof(f92,plain,(
% 1.74/0.64    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 1.74/0.64    inference(superposition,[],[f51,f77])).
% 1.74/0.64  fof(f671,plain,(
% 1.74/0.64    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X7,X8))) )),
% 1.74/0.64    inference(superposition,[],[f53,f421])).
% 1.74/0.64  fof(f421,plain,(
% 1.74/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 1.74/0.64    inference(superposition,[],[f244,f58])).
% 1.74/0.64  fof(f58,plain,(
% 1.74/0.64    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.74/0.64    inference(cnf_transformation,[],[f7])).
% 1.74/0.64  fof(f7,axiom,(
% 1.74/0.64    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.74/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 1.74/0.64  fof(f1291,plain,(
% 1.74/0.64    ( ! [X12,X11] : (k4_xboole_0(X11,k4_xboole_0(X12,X11)) = k5_xboole_0(k4_xboole_0(X12,X11),k2_xboole_0(X11,X12))) )),
% 1.74/0.64    inference(superposition,[],[f1242,f52])).
% 1.74/0.64  fof(f69,plain,(
% 1.74/0.64    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.74/0.64    inference(equality_resolution,[],[f60])).
% 1.74/0.64  fof(f60,plain,(
% 1.74/0.64    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.74/0.64    inference(cnf_transformation,[],[f38])).
% 1.74/0.64  fof(f38,plain,(
% 1.74/0.64    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.74/0.64    inference(flattening,[],[f37])).
% 1.74/0.64  fof(f37,plain,(
% 1.74/0.64    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 1.74/0.64    inference(nnf_transformation,[],[f26])).
% 1.74/0.64  fof(f26,axiom,(
% 1.74/0.64    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.74/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.74/0.64  % SZS output end Proof for theBenchmark
% 1.74/0.64  % (21757)------------------------------
% 1.74/0.64  % (21757)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.74/0.64  % (21757)Termination reason: Refutation
% 1.74/0.64  
% 1.74/0.64  % (21757)Memory used [KB]: 7419
% 1.74/0.64  % (21757)Time elapsed: 0.162 s
% 1.74/0.64  % (21757)------------------------------
% 1.74/0.64  % (21757)------------------------------
% 1.74/0.64  % (21749)Success in time 0.281 s
%------------------------------------------------------------------------------
