%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:21 EST 2020

% Result     : Theorem 4.36s
% Output     : Refutation 4.93s
% Verified   : 
% Statistics : Number of formulae       :  159 (1456 expanded)
%              Number of leaves         :   26 ( 447 expanded)
%              Depth                    :   28
%              Number of atoms          :  406 (2805 expanded)
%              Number of equality atoms :  182 (1753 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6543,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6542,f6456])).

fof(f6456,plain,(
    r2_hidden(sK3,sK4) ),
    inference(subsumption_resolution,[],[f3721,f6450])).

fof(f6450,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(superposition,[],[f6414,f5903])).

fof(f5903,plain,(
    sK4 = k4_xboole_0(sK4,k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f3753,f5755])).

fof(f5755,plain,(
    k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(global_subsumption,[],[f63,f62,f3721])).

fof(f62,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( r2_hidden(sK3,sK4)
      | r2_hidden(sK2,sK4)
      | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) )
    & ( ( ~ r2_hidden(sK3,sK4)
        & ~ r2_hidden(sK2,sK4) )
      | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f46])).

fof(f46,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK3,sK4)
        | r2_hidden(sK2,sK4)
        | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) )
      & ( ( ~ r2_hidden(sK3,sK4)
          & ~ r2_hidden(sK2,sK4) )
        | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f63,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f3753,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f3749,f668])).

fof(f668,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f667,f68])).

fof(f68,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f667,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f645,f69])).

fof(f69,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f645,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f77,f65])).

fof(f65,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f3749,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f1124,f3714])).

fof(f3714,plain,(
    ! [X15,X16] : k1_xboole_0 = k3_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(forward_demodulation,[],[f3713,f65])).

fof(f3713,plain,(
    ! [X15,X16] : k5_xboole_0(X15,X15) = k3_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(backward_demodulation,[],[f3669,f3706])).

fof(f3706,plain,(
    ! [X19,X18] : k5_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X19,X18)) = X18 ),
    inference(backward_demodulation,[],[f3671,f3694])).

fof(f3694,plain,(
    ! [X19,X18] : k4_xboole_0(X18,X19) = k5_xboole_0(X19,k2_xboole_0(X18,X19)) ),
    inference(forward_demodulation,[],[f3646,f74])).

fof(f74,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f3646,plain,(
    ! [X19,X18] : k5_xboole_0(X19,k2_xboole_0(X18,X19)) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(superposition,[],[f814,f801])).

fof(f801,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f88,f77])).

fof(f88,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f814,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f793,f668])).

fof(f793,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f88,f65])).

fof(f3671,plain,(
    ! [X19,X18] : k5_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,k2_xboole_0(X19,X18))) = X18 ),
    inference(forward_demodulation,[],[f3622,f922])).

fof(f922,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,X17),X16) = X16 ),
    inference(backward_demodulation,[],[f672,f920])).

fof(f920,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f653,f906])).

fof(f906,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f818,f814])).

fof(f818,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f814,f71])).

fof(f71,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f653,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f77,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f672,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,X17),X16) = k3_xboole_0(X16,k2_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f671,f653])).

fof(f671,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,X17),X16) = k5_xboole_0(k5_xboole_0(X16,k2_xboole_0(X16,X17)),k2_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f660,f71])).

fof(f660,plain,(
    ! [X17,X16] : k3_xboole_0(k2_xboole_0(X16,X17),X16) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X16,X17),X16),k2_xboole_0(X16,X17)) ),
    inference(superposition,[],[f77,f367])).

fof(f367,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k2_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f252,f124])).

fof(f124,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f73,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f252,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,k2_xboole_0(X0,X1))) ),
    inference(resolution,[],[f229,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f28,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).

fof(f229,plain,(
    ! [X4,X5] : sP0(k2_tarski(X4,k2_xboole_0(X4,X5)),k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f227,f70])).

fof(f227,plain,(
    ! [X4,X5] : sP0(k2_tarski(k2_xboole_0(X4,X5),X4),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f132,f75])).

fof(f132,plain,(
    ! [X2,X1] : sP0(k2_tarski(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f126,f70])).

fof(f126,plain,(
    ! [X0,X1] : sP0(k2_tarski(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f114,f73])).

fof(f114,plain,(
    ! [X0] : sP0(X0,k3_tarski(X0)) ),
    inference(equality_resolution,[],[f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f3622,plain,(
    ! [X19,X18] : k5_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,k2_xboole_0(X19,X18))) = k3_xboole_0(k2_xboole_0(X18,X19),X18) ),
    inference(superposition,[],[f801,f2716])).

fof(f2716,plain,(
    ! [X6,X7] : k2_xboole_0(X7,X6) = k2_xboole_0(k2_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f1891,f124])).

fof(f1891,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k3_tarski(k2_tarski(X3,k2_xboole_0(X3,X4))) ),
    inference(resolution,[],[f1690,f86])).

fof(f1690,plain,(
    ! [X12,X11] : sP0(k2_tarski(X11,k2_xboole_0(X11,X12)),k2_xboole_0(X12,X11)) ),
    inference(forward_demodulation,[],[f1689,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1689,plain,(
    ! [X12,X11] : sP0(k2_tarski(X11,k2_xboole_0(X11,k4_xboole_0(X12,X11))),k2_xboole_0(X12,X11)) ),
    inference(forward_demodulation,[],[f1654,f199])).

fof(f199,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f124,f73])).

fof(f1654,plain,(
    ! [X12,X11] : sP0(k2_tarski(X11,k2_xboole_0(k4_xboole_0(X12,X11),X11)),k2_xboole_0(X12,X11)) ),
    inference(superposition,[],[f1423,f503])).

fof(f503,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(superposition,[],[f337,f73])).

fof(f337,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(resolution,[],[f267,f86])).

fof(f267,plain,(
    ! [X2,X1] : sP0(k2_tarski(X1,k4_xboole_0(X2,X1)),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f238,f199])).

fof(f238,plain,(
    ! [X6,X7] : sP0(k2_tarski(X6,k4_xboole_0(X7,X6)),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f233,f70])).

fof(f233,plain,(
    ! [X6,X7] : sP0(k2_tarski(k4_xboole_0(X7,X6),X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f132,f76])).

fof(f1423,plain,(
    ! [X17,X16] : sP0(k2_tarski(X16,k2_xboole_0(X17,X16)),k2_xboole_0(X16,X17)) ),
    inference(superposition,[],[f126,f849])).

fof(f849,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f89,f367])).

fof(f89,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f3669,plain,(
    ! [X15,X16] : k3_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k5_xboole_0(k2_xboole_0(X15,X16),k4_xboole_0(X16,X15))) ),
    inference(forward_demodulation,[],[f3620,f71])).

fof(f3620,plain,(
    ! [X15,X16] : k3_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X16,X15),k2_xboole_0(X15,X16))) ),
    inference(superposition,[],[f801,f76])).

fof(f1124,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(k3_xboole_0(X15,X16),X15) ),
    inference(superposition,[],[f907,f820])).

fof(f820,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f814,f74])).

fof(f907,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f818,f818])).

fof(f6414,plain,(
    ! [X45,X43,X44] : ~ r2_hidden(X43,k4_xboole_0(X45,k2_tarski(X43,X44))) ),
    inference(subsumption_resolution,[],[f4030,f6413])).

fof(f6413,plain,(
    ! [X39,X41,X40] : r2_hidden(X39,k2_xboole_0(k2_tarski(X39,X40),X41)) ),
    inference(forward_demodulation,[],[f6392,f73])).

fof(f6392,plain,(
    ! [X39,X41,X40] : r2_hidden(X39,k3_tarski(k2_tarski(k2_tarski(X39,X40),X41))) ),
    inference(resolution,[],[f6134,f172])).

fof(f172,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f168,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f168,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f118,f117])).

fof(f117,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f98])).

fof(f98,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ( ( ( sK8(X0,X1,X2,X3) != X0
              & sK8(X0,X1,X2,X3) != X1
              & sK8(X0,X1,X2,X3) != X2 )
            | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
          & ( sK8(X0,X1,X2,X3) = X0
            | sK8(X0,X1,X2,X3) = X1
            | sK8(X0,X1,X2,X3) = X2
            | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f58,f59])).

fof(f59,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ( X0 != X4
              & X1 != X4
              & X2 != X4 )
            | ~ r2_hidden(X4,X3) )
          & ( X0 = X4
            | X1 = X4
            | X2 = X4
            | r2_hidden(X4,X3) ) )
     => ( ( ( sK8(X0,X1,X2,X3) != X0
            & sK8(X0,X1,X2,X3) != X1
            & sK8(X0,X1,X2,X3) != X2 )
          | ~ r2_hidden(sK8(X0,X1,X2,X3),X3) )
        & ( sK8(X0,X1,X2,X3) = X0
          | sK8(X0,X1,X2,X3) = X1
          | sK8(X0,X1,X2,X3) = X2
          | r2_hidden(sK8(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f58,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP1(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ( X0 != X4
                & X1 != X4
                & X2 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X0 = X4
              | X1 = X4
              | X2 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X3)
              | ( X0 != X5
                & X1 != X5
                & X2 != X5 ) )
            & ( X0 = X5
              | X1 = X5
              | X2 = X5
              | ~ r2_hidden(X5,X3) ) )
        | ~ sP1(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f57])).

fof(f57,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X2,X1,X0,X3] :
      ( ( sP1(X2,X1,X0,X3)
        | ? [X4] :
            ( ( ( X2 != X4
                & X1 != X4
                & X0 != X4 )
              | ~ r2_hidden(X4,X3) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ( X2 != X4
                & X1 != X4
                & X0 != X4 ) )
            & ( X2 = X4
              | X1 = X4
              | X0 = X4
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP1(X2,X1,X0,X3) ) ) ),
    inference(nnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f118,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f105])).

fof(f105,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f39,f42])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f6134,plain,(
    ! [X26,X27,X25] :
      ( ~ r2_hidden(k2_tarski(X25,X26),X27)
      | r2_hidden(X25,k3_tarski(X27)) ) ),
    inference(resolution,[],[f6092,f172])).

fof(f6092,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X2,k3_tarski(X1)) ) ),
    inference(resolution,[],[f81,f114])).

fof(f81,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | r2_hidden(X5,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(sK5(X0,X1),X3) )
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( ( r2_hidden(sK6(X0,X1),X0)
              & r2_hidden(sK5(X0,X1),sK6(X0,X1)) )
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ( r2_hidden(sK7(X0,X5),X0)
                & r2_hidden(X5,sK7(X0,X5)) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f49,f52,f51,f50])).

fof(f50,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X3) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( r2_hidden(X4,X0)
                & r2_hidden(X2,X4) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( ~ r2_hidden(X3,X0)
              | ~ r2_hidden(sK5(X0,X1),X3) )
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( ? [X4] :
              ( r2_hidden(X4,X0)
              & r2_hidden(sK5(X0,X1),X4) )
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X4] :
                  ( r2_hidden(X4,X0)
                  & r2_hidden(X2,X4) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X5] :
            ( ( r2_hidden(X5,X1)
              | ! [X6] :
                  ( ~ r2_hidden(X6,X0)
                  | ~ r2_hidden(X5,X6) ) )
            & ( ? [X7] :
                  ( r2_hidden(X7,X0)
                  & r2_hidden(X5,X7) )
              | ~ r2_hidden(X5,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | ! [X3] :
                  ( ~ r2_hidden(X3,X0)
                  | ~ r2_hidden(X2,X3) ) )
            & ( ? [X3] :
                  ( r2_hidden(X3,X0)
                  & r2_hidden(X2,X3) )
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f4030,plain,(
    ! [X45,X43,X44] :
      ( ~ r2_hidden(X43,k4_xboole_0(X45,k2_tarski(X43,X44)))
      | ~ r2_hidden(X43,k2_xboole_0(k2_tarski(X43,X44),X45)) ) ),
    inference(superposition,[],[f3085,f3818])).

fof(f3818,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f3694,f199])).

fof(f3085,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X2),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f91,f172])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f3721,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4) ),
    inference(subsumption_resolution,[],[f64,f3711])).

fof(f3711,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X2,X0) = k4_xboole_0(k2_tarski(X2,X0),X1)
      | r2_hidden(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(backward_demodulation,[],[f3347,f3694])).

fof(f3347,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | k2_tarski(X2,X0) = k5_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X0),X1)) ) ),
    inference(resolution,[],[f94,f1111])).

fof(f1111,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X0 ) ),
    inference(backward_demodulation,[],[f78,f1109])).

fof(f1109,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(forward_demodulation,[],[f1108,f71])).

fof(f1108,plain,(
    ! [X2,X1] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k5_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(superposition,[],[f74,f923])).

fof(f923,plain,(
    ! [X19,X18] : k3_xboole_0(k2_xboole_0(X18,X19),X19) = X19 ),
    inference(backward_demodulation,[],[f674,f921])).

fof(f921,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7 ),
    inference(backward_demodulation,[],[f654,f906])).

fof(f654,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X8,X7)) ),
    inference(superposition,[],[f77,f222])).

fof(f222,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f75,f199])).

fof(f674,plain,(
    ! [X19,X18] : k3_xboole_0(k2_xboole_0(X18,X19),X19) = k3_xboole_0(X19,k2_xboole_0(X18,X19)) ),
    inference(forward_demodulation,[],[f673,f654])).

fof(f673,plain,(
    ! [X19,X18] : k3_xboole_0(k2_xboole_0(X18,X19),X19) = k5_xboole_0(k5_xboole_0(X19,k2_xboole_0(X18,X19)),k2_xboole_0(X18,X19)) ),
    inference(forward_demodulation,[],[f661,f71])).

fof(f661,plain,(
    ! [X19,X18] : k3_xboole_0(k2_xboole_0(X18,X19),X19) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X18,X19),X19),k2_xboole_0(X18,X19)) ),
    inference(superposition,[],[f77,f377])).

fof(f377,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f367,f199])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f64,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f47])).

fof(f6542,plain,(
    ~ r2_hidden(sK3,sK4) ),
    inference(superposition,[],[f6439,f5903])).

fof(f6439,plain,(
    ! [X41,X42,X40] : ~ r2_hidden(X41,k4_xboole_0(X42,k2_tarski(X40,X41))) ),
    inference(subsumption_resolution,[],[f4029,f6427])).

fof(f6427,plain,(
    ! [X4,X2,X3] : r2_hidden(X2,k2_xboole_0(k2_tarski(X3,X2),X4)) ),
    inference(superposition,[],[f6413,f70])).

fof(f4029,plain,(
    ! [X41,X42,X40] :
      ( ~ r2_hidden(X41,k4_xboole_0(X42,k2_tarski(X40,X41)))
      | ~ r2_hidden(X41,k2_xboole_0(k2_tarski(X40,X41),X42)) ) ),
    inference(superposition,[],[f3086,f3818])).

fof(f3086,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(k2_tarski(X5,X3),X4))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f91,f174])).

fof(f174,plain,(
    ! [X2,X1] : r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(superposition,[],[f172,f70])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:01:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (22304)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.53  % (22296)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (22304)Refutation not found, incomplete strategy% (22304)------------------------------
% 0.20/0.53  % (22304)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (22304)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (22304)Memory used [KB]: 10874
% 0.20/0.53  % (22304)Time elapsed: 0.073 s
% 0.20/0.53  % (22304)------------------------------
% 0.20/0.53  % (22304)------------------------------
% 0.20/0.58  % (22301)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.58  % (22305)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.58  % (22299)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.59  % (22312)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.59  % (22298)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.59  % (22324)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.75/0.59  % (22303)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.75/0.59  % (22323)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.75/0.59  % (22297)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.75/0.59  % (22325)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.75/0.60  % (22302)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.75/0.60  % (22322)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.75/0.60  % (22295)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.75/0.60  % (22297)Refutation not found, incomplete strategy% (22297)------------------------------
% 1.75/0.60  % (22297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (22297)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (22297)Memory used [KB]: 10874
% 1.75/0.60  % (22297)Time elapsed: 0.170 s
% 1.75/0.60  % (22297)------------------------------
% 1.75/0.60  % (22297)------------------------------
% 1.75/0.60  % (22326)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.75/0.60  % (22327)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.75/0.60  % (22317)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.75/0.60  % (22314)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.75/0.60  % (22314)Refutation not found, incomplete strategy% (22314)------------------------------
% 1.75/0.60  % (22314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.75/0.60  % (22314)Termination reason: Refutation not found, incomplete strategy
% 1.75/0.60  
% 1.75/0.60  % (22314)Memory used [KB]: 10618
% 1.75/0.60  % (22314)Time elapsed: 0.181 s
% 1.75/0.60  % (22314)------------------------------
% 1.75/0.60  % (22314)------------------------------
% 1.75/0.60  % (22315)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.75/0.61  % (22306)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.75/0.61  % (22316)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.75/0.61  % (22321)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.91/0.61  % (22319)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.91/0.61  % (22320)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.91/0.61  % (22309)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.91/0.61  % (22307)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.91/0.61  % (22311)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.91/0.61  % (22308)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.91/0.62  % (22310)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.91/0.63  % (22392)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.15/0.72  % (22393)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.78/0.75  % (22394)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.23/0.83  % (22301)Time limit reached!
% 3.23/0.83  % (22301)------------------------------
% 3.23/0.83  % (22301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.23/0.84  % (22301)Termination reason: Time limit
% 3.23/0.84  
% 3.23/0.84  % (22301)Memory used [KB]: 8955
% 3.23/0.84  % (22301)Time elapsed: 0.401 s
% 3.23/0.84  % (22301)------------------------------
% 3.23/0.84  % (22301)------------------------------
% 4.07/0.92  % (22295)Time limit reached!
% 4.07/0.92  % (22295)------------------------------
% 4.07/0.92  % (22295)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.93  % (22306)Time limit reached!
% 4.07/0.93  % (22306)------------------------------
% 4.07/0.93  % (22306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.94  % (22295)Termination reason: Time limit
% 4.07/0.94  
% 4.07/0.94  % (22295)Memory used [KB]: 2430
% 4.07/0.94  % (22295)Time elapsed: 0.501 s
% 4.07/0.94  % (22295)------------------------------
% 4.07/0.94  % (22295)------------------------------
% 4.07/0.94  % (22306)Termination reason: Time limit
% 4.07/0.94  
% 4.07/0.94  % (22306)Memory used [KB]: 15735
% 4.07/0.94  % (22306)Time elapsed: 0.507 s
% 4.07/0.94  % (22306)------------------------------
% 4.07/0.94  % (22306)------------------------------
% 4.07/0.94  % (22308)Time limit reached!
% 4.07/0.94  % (22308)------------------------------
% 4.07/0.94  % (22308)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.07/0.94  % (22308)Termination reason: Time limit
% 4.07/0.94  
% 4.07/0.94  % (22308)Memory used [KB]: 7419
% 4.07/0.94  % (22308)Time elapsed: 0.509 s
% 4.07/0.94  % (22308)------------------------------
% 4.07/0.94  % (22308)------------------------------
% 4.36/0.96  % (22296)Time limit reached!
% 4.36/0.96  % (22296)------------------------------
% 4.36/0.96  % (22296)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.36/0.96  % (22296)Termination reason: Time limit
% 4.36/0.96  
% 4.36/0.96  % (22296)Memory used [KB]: 9978
% 4.36/0.96  % (22296)Time elapsed: 0.505 s
% 4.36/0.96  % (22296)------------------------------
% 4.36/0.96  % (22296)------------------------------
% 4.36/0.99  % (22499)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.36/1.01  % (22303)Refutation found. Thanks to Tanya!
% 4.36/1.01  % SZS status Theorem for theBenchmark
% 4.36/1.02  % SZS output start Proof for theBenchmark
% 4.36/1.02  fof(f6543,plain,(
% 4.36/1.02    $false),
% 4.36/1.02    inference(subsumption_resolution,[],[f6542,f6456])).
% 4.36/1.02  fof(f6456,plain,(
% 4.36/1.02    r2_hidden(sK3,sK4)),
% 4.36/1.02    inference(subsumption_resolution,[],[f3721,f6450])).
% 4.36/1.02  fof(f6450,plain,(
% 4.36/1.02    ~r2_hidden(sK2,sK4)),
% 4.36/1.02    inference(superposition,[],[f6414,f5903])).
% 4.36/1.02  fof(f5903,plain,(
% 4.36/1.02    sK4 = k4_xboole_0(sK4,k2_tarski(sK2,sK3))),
% 4.36/1.02    inference(superposition,[],[f3753,f5755])).
% 4.36/1.02  fof(f5755,plain,(
% 4.36/1.02    k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 4.36/1.02    inference(global_subsumption,[],[f63,f62,f3721])).
% 4.36/1.02  fof(f62,plain,(
% 4.36/1.02    ~r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 4.36/1.02    inference(cnf_transformation,[],[f47])).
% 4.36/1.02  fof(f47,plain,(
% 4.36/1.02    (r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4))),
% 4.36/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f45,f46])).
% 4.36/1.02  fof(f46,plain,(
% 4.36/1.02    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)))),
% 4.36/1.02    introduced(choice_axiom,[])).
% 4.36/1.02  fof(f45,plain,(
% 4.36/1.02    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.36/1.02    inference(flattening,[],[f44])).
% 4.36/1.02  fof(f44,plain,(
% 4.36/1.02    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.36/1.02    inference(nnf_transformation,[],[f35])).
% 4.36/1.02  fof(f35,plain,(
% 4.36/1.02    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.36/1.02    inference(ennf_transformation,[],[f32])).
% 4.36/1.02  fof(f32,negated_conjecture,(
% 4.36/1.02    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.36/1.02    inference(negated_conjecture,[],[f31])).
% 4.36/1.02  fof(f31,conjecture,(
% 4.36/1.02    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 4.36/1.02  fof(f63,plain,(
% 4.36/1.02    ~r2_hidden(sK3,sK4) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 4.36/1.02    inference(cnf_transformation,[],[f47])).
% 4.36/1.02  fof(f3753,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 4.36/1.02    inference(forward_demodulation,[],[f3749,f668])).
% 4.36/1.02  fof(f668,plain,(
% 4.36/1.02    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 4.36/1.02    inference(forward_demodulation,[],[f667,f68])).
% 4.36/1.02  fof(f68,plain,(
% 4.36/1.02    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.36/1.02    inference(cnf_transformation,[],[f33])).
% 4.36/1.02  fof(f33,plain,(
% 4.36/1.02    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.36/1.02    inference(rectify,[],[f3])).
% 4.36/1.02  fof(f3,axiom,(
% 4.36/1.02    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 4.36/1.02  fof(f667,plain,(
% 4.36/1.02    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 4.36/1.02    inference(forward_demodulation,[],[f645,f69])).
% 4.36/1.02  fof(f69,plain,(
% 4.36/1.02    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.36/1.02    inference(cnf_transformation,[],[f34])).
% 4.36/1.02  fof(f34,plain,(
% 4.36/1.02    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.36/1.02    inference(rectify,[],[f2])).
% 4.36/1.02  fof(f2,axiom,(
% 4.36/1.02    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 4.36/1.02  fof(f645,plain,(
% 4.36/1.02    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 4.36/1.02    inference(superposition,[],[f77,f65])).
% 4.36/1.02  fof(f65,plain,(
% 4.36/1.02    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.36/1.02    inference(cnf_transformation,[],[f12])).
% 4.36/1.02  fof(f12,axiom,(
% 4.36/1.02    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.36/1.02  fof(f77,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.36/1.02    inference(cnf_transformation,[],[f13])).
% 4.36/1.02  fof(f13,axiom,(
% 4.36/1.02    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.36/1.02  fof(f3749,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 4.36/1.02    inference(superposition,[],[f1124,f3714])).
% 4.36/1.02  fof(f3714,plain,(
% 4.36/1.02    ( ! [X15,X16] : (k1_xboole_0 = k3_xboole_0(X15,k4_xboole_0(X16,X15))) )),
% 4.36/1.02    inference(forward_demodulation,[],[f3713,f65])).
% 4.36/1.02  fof(f3713,plain,(
% 4.36/1.02    ( ! [X15,X16] : (k5_xboole_0(X15,X15) = k3_xboole_0(X15,k4_xboole_0(X16,X15))) )),
% 4.36/1.02    inference(backward_demodulation,[],[f3669,f3706])).
% 4.36/1.02  fof(f3706,plain,(
% 4.36/1.02    ( ! [X19,X18] : (k5_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X19,X18)) = X18) )),
% 4.36/1.02    inference(backward_demodulation,[],[f3671,f3694])).
% 4.36/1.02  fof(f3694,plain,(
% 4.36/1.02    ( ! [X19,X18] : (k4_xboole_0(X18,X19) = k5_xboole_0(X19,k2_xboole_0(X18,X19))) )),
% 4.36/1.02    inference(forward_demodulation,[],[f3646,f74])).
% 4.36/1.02  fof(f74,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.36/1.02    inference(cnf_transformation,[],[f5])).
% 4.36/1.02  fof(f5,axiom,(
% 4.36/1.02    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.36/1.02  fof(f3646,plain,(
% 4.36/1.02    ( ! [X19,X18] : (k5_xboole_0(X19,k2_xboole_0(X18,X19)) = k5_xboole_0(X18,k3_xboole_0(X18,X19))) )),
% 4.36/1.02    inference(superposition,[],[f814,f801])).
% 4.36/1.02  fof(f801,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 4.36/1.02    inference(superposition,[],[f88,f77])).
% 4.36/1.02  fof(f88,plain,(
% 4.36/1.02    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.36/1.02    inference(cnf_transformation,[],[f11])).
% 4.36/1.02  fof(f11,axiom,(
% 4.36/1.02    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.36/1.02  fof(f814,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.36/1.02    inference(forward_demodulation,[],[f793,f668])).
% 4.36/1.02  fof(f793,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.36/1.02    inference(superposition,[],[f88,f65])).
% 4.36/1.02  fof(f3671,plain,(
% 4.36/1.02    ( ! [X19,X18] : (k5_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,k2_xboole_0(X19,X18))) = X18) )),
% 4.36/1.02    inference(forward_demodulation,[],[f3622,f922])).
% 4.36/1.02  fof(f922,plain,(
% 4.36/1.02    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,X17),X16) = X16) )),
% 4.36/1.02    inference(backward_demodulation,[],[f672,f920])).
% 4.36/1.02  fof(f920,plain,(
% 4.36/1.02    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5) )),
% 4.36/1.02    inference(backward_demodulation,[],[f653,f906])).
% 4.36/1.02  fof(f906,plain,(
% 4.36/1.02    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 4.36/1.02    inference(superposition,[],[f818,f814])).
% 4.36/1.02  fof(f818,plain,(
% 4.36/1.02    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 4.36/1.02    inference(superposition,[],[f814,f71])).
% 4.36/1.02  fof(f71,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.36/1.02    inference(cnf_transformation,[],[f1])).
% 4.36/1.02  fof(f1,axiom,(
% 4.36/1.02    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.36/1.02  fof(f653,plain,(
% 4.36/1.02    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6))) )),
% 4.36/1.02    inference(superposition,[],[f77,f75])).
% 4.36/1.02  fof(f75,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.36/1.02    inference(cnf_transformation,[],[f9])).
% 4.36/1.02  fof(f9,axiom,(
% 4.36/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).
% 4.36/1.02  fof(f672,plain,(
% 4.36/1.02    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,X17),X16) = k3_xboole_0(X16,k2_xboole_0(X16,X17))) )),
% 4.36/1.02    inference(forward_demodulation,[],[f671,f653])).
% 4.36/1.02  fof(f671,plain,(
% 4.36/1.02    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,X17),X16) = k5_xboole_0(k5_xboole_0(X16,k2_xboole_0(X16,X17)),k2_xboole_0(X16,X17))) )),
% 4.36/1.02    inference(forward_demodulation,[],[f660,f71])).
% 4.36/1.02  fof(f660,plain,(
% 4.36/1.02    ( ! [X17,X16] : (k3_xboole_0(k2_xboole_0(X16,X17),X16) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X16,X17),X16),k2_xboole_0(X16,X17))) )),
% 4.36/1.02    inference(superposition,[],[f77,f367])).
% 4.36/1.02  fof(f367,plain,(
% 4.36/1.02    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k2_xboole_0(X2,X3),X2)) )),
% 4.36/1.02    inference(superposition,[],[f252,f124])).
% 4.36/1.02  fof(f124,plain,(
% 4.36/1.02    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 4.36/1.02    inference(superposition,[],[f73,f70])).
% 4.36/1.02  fof(f70,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.36/1.02    inference(cnf_transformation,[],[f14])).
% 4.36/1.02  fof(f14,axiom,(
% 4.36/1.02    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 4.36/1.02  fof(f73,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.36/1.02    inference(cnf_transformation,[],[f29])).
% 4.36/1.02  fof(f29,axiom,(
% 4.36/1.02    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 4.36/1.02  fof(f252,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,k2_xboole_0(X0,X1)))) )),
% 4.36/1.02    inference(resolution,[],[f229,f86])).
% 4.36/1.02  fof(f86,plain,(
% 4.36/1.02    ( ! [X0,X1] : (~sP0(X0,X1) | k3_tarski(X0) = X1) )),
% 4.36/1.02    inference(cnf_transformation,[],[f54])).
% 4.36/1.02  fof(f54,plain,(
% 4.36/1.02    ! [X0,X1] : ((k3_tarski(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k3_tarski(X0) != X1))),
% 4.36/1.02    inference(nnf_transformation,[],[f41])).
% 4.36/1.02  fof(f41,plain,(
% 4.36/1.02    ! [X0,X1] : (k3_tarski(X0) = X1 <=> sP0(X0,X1))),
% 4.36/1.02    inference(definition_folding,[],[f28,f40])).
% 4.36/1.02  fof(f40,plain,(
% 4.36/1.02    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 4.36/1.02    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.36/1.02  fof(f28,axiom,(
% 4.36/1.02    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tarski)).
% 4.36/1.02  fof(f229,plain,(
% 4.36/1.02    ( ! [X4,X5] : (sP0(k2_tarski(X4,k2_xboole_0(X4,X5)),k2_xboole_0(X4,X5))) )),
% 4.36/1.02    inference(forward_demodulation,[],[f227,f70])).
% 4.36/1.02  fof(f227,plain,(
% 4.36/1.02    ( ! [X4,X5] : (sP0(k2_tarski(k2_xboole_0(X4,X5),X4),k2_xboole_0(X4,X5))) )),
% 4.36/1.02    inference(superposition,[],[f132,f75])).
% 4.36/1.02  fof(f132,plain,(
% 4.36/1.02    ( ! [X2,X1] : (sP0(k2_tarski(X2,X1),k2_xboole_0(X1,X2))) )),
% 4.36/1.02    inference(superposition,[],[f126,f70])).
% 4.36/1.02  fof(f126,plain,(
% 4.36/1.02    ( ! [X0,X1] : (sP0(k2_tarski(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.36/1.02    inference(superposition,[],[f114,f73])).
% 4.36/1.02  fof(f114,plain,(
% 4.36/1.02    ( ! [X0] : (sP0(X0,k3_tarski(X0))) )),
% 4.36/1.02    inference(equality_resolution,[],[f85])).
% 4.36/1.02  fof(f85,plain,(
% 4.36/1.02    ( ! [X0,X1] : (sP0(X0,X1) | k3_tarski(X0) != X1) )),
% 4.36/1.02    inference(cnf_transformation,[],[f54])).
% 4.36/1.02  fof(f3622,plain,(
% 4.36/1.02    ( ! [X19,X18] : (k5_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,k2_xboole_0(X19,X18))) = k3_xboole_0(k2_xboole_0(X18,X19),X18)) )),
% 4.36/1.02    inference(superposition,[],[f801,f2716])).
% 4.36/1.02  fof(f2716,plain,(
% 4.36/1.02    ( ! [X6,X7] : (k2_xboole_0(X7,X6) = k2_xboole_0(k2_xboole_0(X6,X7),X6)) )),
% 4.36/1.02    inference(superposition,[],[f1891,f124])).
% 4.36/1.02  fof(f1891,plain,(
% 4.36/1.02    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k3_tarski(k2_tarski(X3,k2_xboole_0(X3,X4)))) )),
% 4.36/1.02    inference(resolution,[],[f1690,f86])).
% 4.36/1.02  fof(f1690,plain,(
% 4.36/1.02    ( ! [X12,X11] : (sP0(k2_tarski(X11,k2_xboole_0(X11,X12)),k2_xboole_0(X12,X11))) )),
% 4.36/1.02    inference(forward_demodulation,[],[f1689,f76])).
% 4.36/1.02  fof(f76,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 4.36/1.02    inference(cnf_transformation,[],[f7])).
% 4.36/1.02  fof(f7,axiom,(
% 4.36/1.02    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 4.36/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.36/1.02  fof(f1689,plain,(
% 4.36/1.02    ( ! [X12,X11] : (sP0(k2_tarski(X11,k2_xboole_0(X11,k4_xboole_0(X12,X11))),k2_xboole_0(X12,X11))) )),
% 4.36/1.02    inference(forward_demodulation,[],[f1654,f199])).
% 4.36/1.02  fof(f199,plain,(
% 4.36/1.02    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 4.36/1.02    inference(superposition,[],[f124,f73])).
% 4.36/1.02  fof(f1654,plain,(
% 4.36/1.02    ( ! [X12,X11] : (sP0(k2_tarski(X11,k2_xboole_0(k4_xboole_0(X12,X11),X11)),k2_xboole_0(X12,X11))) )),
% 4.36/1.02    inference(superposition,[],[f1423,f503])).
% 4.36/1.02  fof(f503,plain,(
% 4.36/1.02    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k2_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 4.36/1.02    inference(superposition,[],[f337,f73])).
% 4.36/1.02  fof(f337,plain,(
% 4.36/1.02    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 4.36/1.02    inference(resolution,[],[f267,f86])).
% 4.36/1.02  fof(f267,plain,(
% 4.36/1.02    ( ! [X2,X1] : (sP0(k2_tarski(X1,k4_xboole_0(X2,X1)),k2_xboole_0(X2,X1))) )),
% 4.36/1.02    inference(superposition,[],[f238,f199])).
% 4.36/1.02  fof(f238,plain,(
% 4.36/1.02    ( ! [X6,X7] : (sP0(k2_tarski(X6,k4_xboole_0(X7,X6)),k2_xboole_0(X6,X7))) )),
% 4.36/1.02    inference(forward_demodulation,[],[f233,f70])).
% 4.36/1.02  fof(f233,plain,(
% 4.36/1.02    ( ! [X6,X7] : (sP0(k2_tarski(k4_xboole_0(X7,X6),X6),k2_xboole_0(X6,X7))) )),
% 4.36/1.02    inference(superposition,[],[f132,f76])).
% 4.36/1.02  fof(f1423,plain,(
% 4.36/1.02    ( ! [X17,X16] : (sP0(k2_tarski(X16,k2_xboole_0(X17,X16)),k2_xboole_0(X16,X17))) )),
% 4.36/1.02    inference(superposition,[],[f126,f849])).
% 4.36/1.03  fof(f849,plain,(
% 4.36/1.03    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 4.36/1.03    inference(superposition,[],[f89,f367])).
% 4.36/1.03  fof(f89,plain,(
% 4.36/1.03    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.36/1.03    inference(cnf_transformation,[],[f8])).
% 4.36/1.03  fof(f8,axiom,(
% 4.36/1.03    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.36/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.36/1.03  fof(f3669,plain,(
% 4.36/1.03    ( ! [X15,X16] : (k3_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k5_xboole_0(k2_xboole_0(X15,X16),k4_xboole_0(X16,X15)))) )),
% 4.36/1.03    inference(forward_demodulation,[],[f3620,f71])).
% 4.36/1.03  fof(f3620,plain,(
% 4.36/1.03    ( ! [X15,X16] : (k3_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X16,X15),k2_xboole_0(X15,X16)))) )),
% 4.36/1.03    inference(superposition,[],[f801,f76])).
% 4.36/1.03  fof(f1124,plain,(
% 4.36/1.03    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k5_xboole_0(k3_xboole_0(X15,X16),X15)) )),
% 4.36/1.03    inference(superposition,[],[f907,f820])).
% 4.36/1.03  fof(f820,plain,(
% 4.36/1.03    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 4.36/1.03    inference(superposition,[],[f814,f74])).
% 4.36/1.03  fof(f907,plain,(
% 4.36/1.03    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 4.36/1.03    inference(superposition,[],[f818,f818])).
% 4.36/1.03  fof(f6414,plain,(
% 4.36/1.03    ( ! [X45,X43,X44] : (~r2_hidden(X43,k4_xboole_0(X45,k2_tarski(X43,X44)))) )),
% 4.36/1.03    inference(subsumption_resolution,[],[f4030,f6413])).
% 4.36/1.03  fof(f6413,plain,(
% 4.36/1.03    ( ! [X39,X41,X40] : (r2_hidden(X39,k2_xboole_0(k2_tarski(X39,X40),X41))) )),
% 4.36/1.03    inference(forward_demodulation,[],[f6392,f73])).
% 4.36/1.03  fof(f6392,plain,(
% 4.36/1.03    ( ! [X39,X41,X40] : (r2_hidden(X39,k3_tarski(k2_tarski(k2_tarski(X39,X40),X41)))) )),
% 4.36/1.03    inference(resolution,[],[f6134,f172])).
% 4.36/1.03  fof(f172,plain,(
% 4.36/1.03    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 4.36/1.03    inference(superposition,[],[f168,f72])).
% 4.36/1.03  fof(f72,plain,(
% 4.36/1.03    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.36/1.03    inference(cnf_transformation,[],[f22])).
% 4.36/1.03  fof(f22,axiom,(
% 4.36/1.03    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.36/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.36/1.03  fof(f168,plain,(
% 4.36/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 4.36/1.03    inference(resolution,[],[f118,f117])).
% 4.36/1.03  fof(f117,plain,(
% 4.36/1.03    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 4.36/1.03    inference(equality_resolution,[],[f98])).
% 4.36/1.03  fof(f98,plain,(
% 4.36/1.03    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 4.36/1.03    inference(cnf_transformation,[],[f60])).
% 4.36/1.03  fof(f60,plain,(
% 4.36/1.03    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK8(X0,X1,X2,X3) != X0 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X2) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X0 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X2 | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 4.36/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f58,f59])).
% 4.36/1.03  fof(f59,plain,(
% 4.36/1.03    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK8(X0,X1,X2,X3) != X0 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X2) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X0 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X2 | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 4.36/1.03    introduced(choice_axiom,[])).
% 4.36/1.03  fof(f58,plain,(
% 4.36/1.03    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 4.36/1.03    inference(rectify,[],[f57])).
% 4.36/1.03  fof(f57,plain,(
% 4.36/1.03    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 4.36/1.03    inference(flattening,[],[f56])).
% 4.36/1.03  fof(f56,plain,(
% 4.36/1.03    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 4.36/1.03    inference(nnf_transformation,[],[f42])).
% 4.36/1.03  fof(f42,plain,(
% 4.36/1.03    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.36/1.03    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.36/1.03  fof(f118,plain,(
% 4.36/1.03    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 4.36/1.03    inference(equality_resolution,[],[f105])).
% 4.36/1.03  fof(f105,plain,(
% 4.36/1.03    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.36/1.03    inference(cnf_transformation,[],[f61])).
% 4.36/1.03  fof(f61,plain,(
% 4.36/1.03    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 4.36/1.03    inference(nnf_transformation,[],[f43])).
% 4.36/1.03  fof(f43,plain,(
% 4.36/1.03    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 4.36/1.03    inference(definition_folding,[],[f39,f42])).
% 4.36/1.03  fof(f39,plain,(
% 4.36/1.03    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.36/1.03    inference(ennf_transformation,[],[f15])).
% 4.36/1.03  fof(f15,axiom,(
% 4.36/1.03    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.36/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 4.93/1.03  fof(f6134,plain,(
% 4.93/1.03    ( ! [X26,X27,X25] : (~r2_hidden(k2_tarski(X25,X26),X27) | r2_hidden(X25,k3_tarski(X27))) )),
% 4.93/1.03    inference(resolution,[],[f6092,f172])).
% 4.93/1.03  fof(f6092,plain,(
% 4.93/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X0,X1) | r2_hidden(X2,k3_tarski(X1))) )),
% 4.93/1.03    inference(resolution,[],[f81,f114])).
% 4.93/1.03  fof(f81,plain,(
% 4.93/1.03    ( ! [X6,X0,X5,X1] : (~sP0(X0,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | r2_hidden(X5,X1)) )),
% 4.93/1.03    inference(cnf_transformation,[],[f53])).
% 4.93/1.03  fof(f53,plain,(
% 4.93/1.03    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 4.93/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f49,f52,f51,f50])).
% 4.93/1.03  fof(f50,plain,(
% 4.93/1.03    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 4.93/1.03    introduced(choice_axiom,[])).
% 4.93/1.03  fof(f51,plain,(
% 4.93/1.03    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 4.93/1.03    introduced(choice_axiom,[])).
% 4.93/1.03  fof(f52,plain,(
% 4.93/1.03    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 4.93/1.03    introduced(choice_axiom,[])).
% 4.93/1.03  fof(f49,plain,(
% 4.93/1.03    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 4.93/1.03    inference(rectify,[],[f48])).
% 4.93/1.03  fof(f48,plain,(
% 4.93/1.03    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 4.93/1.03    inference(nnf_transformation,[],[f40])).
% 4.93/1.03  fof(f4030,plain,(
% 4.93/1.03    ( ! [X45,X43,X44] : (~r2_hidden(X43,k4_xboole_0(X45,k2_tarski(X43,X44))) | ~r2_hidden(X43,k2_xboole_0(k2_tarski(X43,X44),X45))) )),
% 4.93/1.03    inference(superposition,[],[f3085,f3818])).
% 4.93/1.03  fof(f3818,plain,(
% 4.93/1.03    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X2,k2_xboole_0(X2,X1))) )),
% 4.93/1.03    inference(superposition,[],[f3694,f199])).
% 4.93/1.03  fof(f3085,plain,(
% 4.93/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X2),X1)) | ~r2_hidden(X0,X1)) )),
% 4.93/1.03    inference(resolution,[],[f91,f172])).
% 4.93/1.03  fof(f91,plain,(
% 4.93/1.03    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 4.93/1.03    inference(cnf_transformation,[],[f55])).
% 4.93/1.03  fof(f55,plain,(
% 4.93/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 4.93/1.03    inference(nnf_transformation,[],[f37])).
% 4.93/1.03  fof(f37,plain,(
% 4.93/1.03    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 4.93/1.03    inference(ennf_transformation,[],[f4])).
% 4.93/1.03  fof(f4,axiom,(
% 4.93/1.03    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 4.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 4.93/1.03  fof(f3721,plain,(
% 4.93/1.03    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4)),
% 4.93/1.03    inference(subsumption_resolution,[],[f64,f3711])).
% 4.93/1.03  fof(f3711,plain,(
% 4.93/1.03    ( ! [X2,X0,X1] : (k2_tarski(X2,X0) = k4_xboole_0(k2_tarski(X2,X0),X1) | r2_hidden(X0,X1) | r2_hidden(X2,X1)) )),
% 4.93/1.03    inference(backward_demodulation,[],[f3347,f3694])).
% 4.93/1.03  fof(f3347,plain,(
% 4.93/1.03    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | k2_tarski(X2,X0) = k5_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X0),X1))) )),
% 4.93/1.03    inference(resolution,[],[f94,f1111])).
% 4.93/1.03  fof(f1111,plain,(
% 4.93/1.03    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X0) )),
% 4.93/1.03    inference(backward_demodulation,[],[f78,f1109])).
% 4.93/1.03  fof(f1109,plain,(
% 4.93/1.03    ( ! [X2,X1] : (k5_xboole_0(X2,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X1,X2),X2)) )),
% 4.93/1.03    inference(forward_demodulation,[],[f1108,f71])).
% 4.93/1.03  fof(f1108,plain,(
% 4.93/1.03    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X1,X2),X2) = k5_xboole_0(k2_xboole_0(X1,X2),X2)) )),
% 4.93/1.03    inference(superposition,[],[f74,f923])).
% 4.93/1.03  fof(f923,plain,(
% 4.93/1.03    ( ! [X19,X18] : (k3_xboole_0(k2_xboole_0(X18,X19),X19) = X19) )),
% 4.93/1.03    inference(backward_demodulation,[],[f674,f921])).
% 4.93/1.03  fof(f921,plain,(
% 4.93/1.03    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7) )),
% 4.93/1.03    inference(backward_demodulation,[],[f654,f906])).
% 4.93/1.03  fof(f654,plain,(
% 4.93/1.03    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X8,X7))) )),
% 4.93/1.03    inference(superposition,[],[f77,f222])).
% 4.93/1.03  fof(f222,plain,(
% 4.93/1.03    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 4.93/1.03    inference(superposition,[],[f75,f199])).
% 4.93/1.03  fof(f674,plain,(
% 4.93/1.03    ( ! [X19,X18] : (k3_xboole_0(k2_xboole_0(X18,X19),X19) = k3_xboole_0(X19,k2_xboole_0(X18,X19))) )),
% 4.93/1.03    inference(forward_demodulation,[],[f673,f654])).
% 4.93/1.03  fof(f673,plain,(
% 4.93/1.03    ( ! [X19,X18] : (k3_xboole_0(k2_xboole_0(X18,X19),X19) = k5_xboole_0(k5_xboole_0(X19,k2_xboole_0(X18,X19)),k2_xboole_0(X18,X19))) )),
% 4.93/1.03    inference(forward_demodulation,[],[f661,f71])).
% 4.93/1.03  fof(f661,plain,(
% 4.93/1.03    ( ! [X19,X18] : (k3_xboole_0(k2_xboole_0(X18,X19),X19) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X18,X19),X19),k2_xboole_0(X18,X19))) )),
% 4.93/1.03    inference(superposition,[],[f77,f377])).
% 4.93/1.03  fof(f377,plain,(
% 4.93/1.03    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 4.93/1.03    inference(superposition,[],[f367,f199])).
% 4.93/1.03  fof(f78,plain,(
% 4.93/1.03    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 4.93/1.03    inference(cnf_transformation,[],[f36])).
% 4.93/1.03  fof(f36,plain,(
% 4.93/1.03    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 4.93/1.03    inference(ennf_transformation,[],[f10])).
% 4.93/1.03  fof(f10,axiom,(
% 4.93/1.03    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 4.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).
% 4.93/1.03  fof(f94,plain,(
% 4.93/1.03    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 4.93/1.03    inference(cnf_transformation,[],[f38])).
% 4.93/1.03  fof(f38,plain,(
% 4.93/1.03    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 4.93/1.03    inference(ennf_transformation,[],[f30])).
% 4.93/1.03  fof(f30,axiom,(
% 4.93/1.03    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 4.93/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 4.93/1.03  fof(f64,plain,(
% 4.93/1.03    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 4.93/1.03    inference(cnf_transformation,[],[f47])).
% 4.93/1.03  fof(f6542,plain,(
% 4.93/1.03    ~r2_hidden(sK3,sK4)),
% 4.93/1.03    inference(superposition,[],[f6439,f5903])).
% 4.93/1.03  fof(f6439,plain,(
% 4.93/1.03    ( ! [X41,X42,X40] : (~r2_hidden(X41,k4_xboole_0(X42,k2_tarski(X40,X41)))) )),
% 4.93/1.03    inference(subsumption_resolution,[],[f4029,f6427])).
% 4.93/1.03  fof(f6427,plain,(
% 4.93/1.03    ( ! [X4,X2,X3] : (r2_hidden(X2,k2_xboole_0(k2_tarski(X3,X2),X4))) )),
% 4.93/1.03    inference(superposition,[],[f6413,f70])).
% 4.93/1.03  fof(f4029,plain,(
% 4.93/1.03    ( ! [X41,X42,X40] : (~r2_hidden(X41,k4_xboole_0(X42,k2_tarski(X40,X41))) | ~r2_hidden(X41,k2_xboole_0(k2_tarski(X40,X41),X42))) )),
% 4.93/1.03    inference(superposition,[],[f3086,f3818])).
% 4.93/1.03  fof(f3086,plain,(
% 4.93/1.03    ( ! [X4,X5,X3] : (~r2_hidden(X3,k5_xboole_0(k2_tarski(X5,X3),X4)) | ~r2_hidden(X3,X4)) )),
% 4.93/1.03    inference(resolution,[],[f91,f174])).
% 4.93/1.03  fof(f174,plain,(
% 4.93/1.03    ( ! [X2,X1] : (r2_hidden(X1,k2_tarski(X2,X1))) )),
% 4.93/1.03    inference(superposition,[],[f172,f70])).
% 4.93/1.03  % SZS output end Proof for theBenchmark
% 4.93/1.03  % (22303)------------------------------
% 4.93/1.03  % (22303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.93/1.03  % (22303)Termination reason: Refutation
% 4.93/1.03  
% 4.93/1.03  % (22303)Memory used [KB]: 10362
% 4.93/1.03  % (22303)Time elapsed: 0.577 s
% 4.93/1.03  % (22303)------------------------------
% 4.93/1.03  % (22303)------------------------------
% 4.93/1.03  % (22289)Success in time 0.67 s
%------------------------------------------------------------------------------
