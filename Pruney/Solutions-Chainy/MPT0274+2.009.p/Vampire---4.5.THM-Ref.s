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
% DateTime   : Thu Dec  3 12:41:21 EST 2020

% Result     : Theorem 4.26s
% Output     : Refutation 4.26s
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
fof(f6545,plain,(
    $false ),
    inference(subsumption_resolution,[],[f6544,f6458])).

fof(f6458,plain,(
    r2_hidden(sK3,sK4) ),
    inference(subsumption_resolution,[],[f3630,f6452])).

fof(f6452,plain,(
    ~ r2_hidden(sK2,sK4) ),
    inference(superposition,[],[f6416,f5813])).

fof(f5813,plain,(
    sK4 = k4_xboole_0(sK4,k2_tarski(sK2,sK3)) ),
    inference(superposition,[],[f3662,f5665])).

fof(f5665,plain,(
    k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(global_subsumption,[],[f61,f60,f3630])).

fof(f60,plain,
    ( ~ r2_hidden(sK2,sK4)
    | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ( r2_hidden(sK3,sK4)
      | r2_hidden(sK2,sK4)
      | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) )
    & ( ( ~ r2_hidden(sK3,sK4)
        & ~ r2_hidden(sK2,sK4) )
      | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f43,f44])).

fof(f44,plain,
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

fof(f43,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f61,plain,
    ( ~ r2_hidden(sK3,sK4)
    | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f3662,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(forward_demodulation,[],[f3658,f568])).

fof(f568,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f567,f66])).

fof(f66,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f567,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(forward_demodulation,[],[f549,f67])).

fof(f67,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f549,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0)) ),
    inference(superposition,[],[f75,f63])).

fof(f63,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f3658,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f987,f3623])).

fof(f3623,plain,(
    ! [X15,X16] : k1_xboole_0 = k3_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(forward_demodulation,[],[f3622,f63])).

fof(f3622,plain,(
    ! [X15,X16] : k5_xboole_0(X15,X15) = k3_xboole_0(X15,k4_xboole_0(X16,X15)) ),
    inference(backward_demodulation,[],[f3578,f3615])).

fof(f3615,plain,(
    ! [X19,X18] : k5_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X19,X18)) = X18 ),
    inference(backward_demodulation,[],[f3580,f3603])).

fof(f3603,plain,(
    ! [X19,X18] : k4_xboole_0(X18,X19) = k5_xboole_0(X19,k2_xboole_0(X18,X19)) ),
    inference(forward_demodulation,[],[f3555,f72])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f3555,plain,(
    ! [X19,X18] : k5_xboole_0(X19,k2_xboole_0(X18,X19)) = k5_xboole_0(X18,k3_xboole_0(X18,X19)) ),
    inference(superposition,[],[f751,f738])).

fof(f738,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f87,f75])).

fof(f87,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f751,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f730,f568])).

fof(f730,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f87,f63])).

fof(f3580,plain,(
    ! [X19,X18] : k5_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,k2_xboole_0(X19,X18))) = X18 ),
    inference(forward_demodulation,[],[f3531,f791])).

fof(f791,plain,(
    ! [X14,X13] : k3_xboole_0(k2_xboole_0(X13,X14),X13) = X13 ),
    inference(backward_demodulation,[],[f572,f789])).

fof(f789,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5 ),
    inference(backward_demodulation,[],[f557,f775])).

fof(f775,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f755,f751])).

fof(f755,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f751,f69])).

fof(f69,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f557,plain,(
    ! [X6,X5] : k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6)) ),
    inference(superposition,[],[f75,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).

fof(f572,plain,(
    ! [X14,X13] : k3_xboole_0(k2_xboole_0(X13,X14),X13) = k3_xboole_0(X13,k2_xboole_0(X13,X14)) ),
    inference(forward_demodulation,[],[f571,f557])).

fof(f571,plain,(
    ! [X14,X13] : k3_xboole_0(k2_xboole_0(X13,X14),X13) = k5_xboole_0(k5_xboole_0(X13,k2_xboole_0(X13,X14)),k2_xboole_0(X13,X14)) ),
    inference(forward_demodulation,[],[f562,f69])).

fof(f562,plain,(
    ! [X14,X13] : k3_xboole_0(k2_xboole_0(X13,X14),X13) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X13,X14),X13),k2_xboole_0(X13,X14)) ),
    inference(superposition,[],[f75,f402])).

fof(f402,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(k2_xboole_0(X2,X3),X2) ),
    inference(superposition,[],[f287,f120])).

fof(f120,plain,(
    ! [X2,X1] : k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1)) ),
    inference(superposition,[],[f71,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f287,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,k2_xboole_0(X0,X1))) ),
    inference(resolution,[],[f225,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ sP0(X0,X1)
      | k3_tarski(X0) = X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k3_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k3_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f26,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( k3_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] :
              ( r2_hidden(X3,X0)
              & r2_hidden(X2,X3) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

fof(f225,plain,(
    ! [X4,X5] : sP0(k2_tarski(X4,k2_xboole_0(X4,X5)),k2_xboole_0(X4,X5)) ),
    inference(forward_demodulation,[],[f223,f68])).

fof(f223,plain,(
    ! [X4,X5] : sP0(k2_tarski(k2_xboole_0(X4,X5),X4),k2_xboole_0(X4,X5)) ),
    inference(superposition,[],[f128,f73])).

fof(f128,plain,(
    ! [X2,X1] : sP0(k2_tarski(X2,X1),k2_xboole_0(X1,X2)) ),
    inference(superposition,[],[f122,f68])).

fof(f122,plain,(
    ! [X0,X1] : sP0(k2_tarski(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(superposition,[],[f110,f71])).

fof(f110,plain,(
    ! [X0] : sP0(X0,k3_tarski(X0)) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k3_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3531,plain,(
    ! [X19,X18] : k5_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,k2_xboole_0(X19,X18))) = k3_xboole_0(k2_xboole_0(X18,X19),X18) ),
    inference(superposition,[],[f738,f2654])).

fof(f2654,plain,(
    ! [X6,X7] : k2_xboole_0(X7,X6) = k2_xboole_0(k2_xboole_0(X6,X7),X6) ),
    inference(superposition,[],[f1870,f120])).

fof(f1870,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k3_tarski(k2_tarski(X3,k2_xboole_0(X3,X4))) ),
    inference(resolution,[],[f1731,f84])).

fof(f1731,plain,(
    ! [X12,X11] : sP0(k2_tarski(X11,k2_xboole_0(X11,X12)),k2_xboole_0(X12,X11)) ),
    inference(forward_demodulation,[],[f1730,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1730,plain,(
    ! [X12,X11] : sP0(k2_tarski(X11,k2_xboole_0(X11,k4_xboole_0(X12,X11))),k2_xboole_0(X12,X11)) ),
    inference(forward_demodulation,[],[f1695,f195])).

fof(f195,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2) ),
    inference(superposition,[],[f120,f71])).

fof(f1695,plain,(
    ! [X12,X11] : sP0(k2_tarski(X11,k2_xboole_0(k4_xboole_0(X12,X11),X11)),k2_xboole_0(X12,X11)) ),
    inference(superposition,[],[f1577,f538])).

fof(f538,plain,(
    ! [X8,X7] : k2_xboole_0(X8,X7) = k2_xboole_0(X7,k4_xboole_0(X8,X7)) ),
    inference(superposition,[],[f372,f71])).

fof(f372,plain,(
    ! [X0,X1] : k2_xboole_0(X1,X0) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0))) ),
    inference(resolution,[],[f302,f84])).

fof(f302,plain,(
    ! [X2,X1] : sP0(k2_tarski(X1,k4_xboole_0(X2,X1)),k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f234,f195])).

fof(f234,plain,(
    ! [X6,X7] : sP0(k2_tarski(X6,k4_xboole_0(X7,X6)),k2_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f229,f68])).

fof(f229,plain,(
    ! [X6,X7] : sP0(k2_tarski(k4_xboole_0(X7,X6),X6),k2_xboole_0(X6,X7)) ),
    inference(superposition,[],[f128,f74])).

fof(f1577,plain,(
    ! [X17,X16] : sP0(k2_tarski(X16,k2_xboole_0(X17,X16)),k2_xboole_0(X16,X17)) ),
    inference(superposition,[],[f122,f1339])).

fof(f1339,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0)) ),
    inference(superposition,[],[f88,f402])).

fof(f88,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f3578,plain,(
    ! [X15,X16] : k3_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k5_xboole_0(k2_xboole_0(X15,X16),k4_xboole_0(X16,X15))) ),
    inference(forward_demodulation,[],[f3529,f69])).

fof(f3529,plain,(
    ! [X15,X16] : k3_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X16,X15),k2_xboole_0(X15,X16))) ),
    inference(superposition,[],[f738,f74])).

fof(f987,plain,(
    ! [X15,X16] : k4_xboole_0(X15,X16) = k5_xboole_0(k3_xboole_0(X15,X16),X15) ),
    inference(superposition,[],[f776,f757])).

fof(f757,plain,(
    ! [X8,X7] : k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8)) ),
    inference(superposition,[],[f751,f72])).

fof(f776,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f755,f755])).

fof(f6416,plain,(
    ! [X45,X43,X44] : ~ r2_hidden(X43,k4_xboole_0(X45,k2_tarski(X43,X44))) ),
    inference(subsumption_resolution,[],[f3940,f6415])).

fof(f6415,plain,(
    ! [X39,X41,X40] : r2_hidden(X39,k2_xboole_0(k2_tarski(X39,X40),X41)) ),
    inference(forward_demodulation,[],[f6394,f71])).

fof(f6394,plain,(
    ! [X39,X41,X40] : r2_hidden(X39,k3_tarski(k2_tarski(k2_tarski(X39,X40),X41))) ),
    inference(resolution,[],[f6130,f168])).

fof(f168,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(superposition,[],[f164,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f164,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k1_enumset1(X0,X1,X2)) ),
    inference(resolution,[],[f114,f113])).

fof(f113,plain,(
    ! [X0,X5,X3,X1] :
      ( ~ sP1(X0,X1,X5,X3)
      | r2_hidden(X5,X3) ) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X5,X3,X1] :
      ( r2_hidden(X5,X3)
      | X2 != X5
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f56,f57])).

fof(f57,plain,(
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

fof(f56,plain,(
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
    inference(rectify,[],[f55])).

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(nnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X2,X1,X0,X3] :
      ( sP1(X2,X1,X0,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f114,plain,(
    ! [X2,X0,X1] : sP1(X2,X1,X0,k1_enumset1(X0,X1,X2)) ),
    inference(equality_resolution,[],[f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X2,X1,X0,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2,X3] :
      ( ( k1_enumset1(X0,X1,X2) = X3
        | ~ sP1(X2,X1,X0,X3) )
      & ( sP1(X2,X1,X0,X3)
        | k1_enumset1(X0,X1,X2) != X3 ) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> sP1(X2,X1,X0,X3) ) ),
    inference(definition_folding,[],[f37,f40])).

fof(f37,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

fof(f6130,plain,(
    ! [X26,X27,X25] :
      ( ~ r2_hidden(k2_tarski(X25,X26),X27)
      | r2_hidden(X25,k3_tarski(X27)) ) ),
    inference(resolution,[],[f6109,f168])).

fof(f6109,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X2,k3_tarski(X1)) ) ),
    inference(resolution,[],[f79,f110])).

fof(f79,plain,(
    ! [X6,X0,X5,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X6,X0)
      | ~ r2_hidden(X5,X6)
      | r2_hidden(X5,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f47,f50,f49,f48])).

fof(f48,plain,(
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

fof(f49,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X0)
          & r2_hidden(sK5(X0,X1),X4) )
     => ( r2_hidden(sK6(X0,X1),X0)
        & r2_hidden(sK5(X0,X1),sK6(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( r2_hidden(X7,X0)
          & r2_hidden(X5,X7) )
     => ( r2_hidden(sK7(X0,X5),X0)
        & r2_hidden(X5,sK7(X0,X5)) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f38])).

fof(f3940,plain,(
    ! [X45,X43,X44] :
      ( ~ r2_hidden(X43,k4_xboole_0(X45,k2_tarski(X43,X44)))
      | ~ r2_hidden(X43,k2_xboole_0(k2_tarski(X43,X44),X45)) ) ),
    inference(superposition,[],[f3024,f3727])).

fof(f3727,plain,(
    ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X2,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f3603,f195])).

fof(f3024,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X2),X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(resolution,[],[f90,f168])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2)
      | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f3630,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4) ),
    inference(subsumption_resolution,[],[f62,f3620])).

fof(f3620,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X2,X0) = k4_xboole_0(k2_tarski(X2,X0),X1)
      | r2_hidden(X0,X1)
      | r2_hidden(X2,X1) ) ),
    inference(backward_demodulation,[],[f3286,f3603])).

fof(f3286,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X1)
      | r2_hidden(X2,X1)
      | k2_tarski(X2,X0) = k5_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X0),X1)) ) ),
    inference(resolution,[],[f93,f974])).

fof(f974,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X0 ) ),
    inference(backward_demodulation,[],[f76,f972])).

fof(f972,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(forward_demodulation,[],[f971,f69])).

fof(f971,plain,(
    ! [X2,X1] : k4_xboole_0(k2_xboole_0(X1,X2),X2) = k5_xboole_0(k2_xboole_0(X1,X2),X2) ),
    inference(superposition,[],[f72,f792])).

fof(f792,plain,(
    ! [X15,X16] : k3_xboole_0(k2_xboole_0(X15,X16),X16) = X16 ),
    inference(backward_demodulation,[],[f574,f790])).

fof(f790,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7 ),
    inference(backward_demodulation,[],[f558,f775])).

fof(f558,plain,(
    ! [X8,X7] : k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X8,X7)) ),
    inference(superposition,[],[f75,f218])).

fof(f218,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f73,f195])).

fof(f574,plain,(
    ! [X15,X16] : k3_xboole_0(k2_xboole_0(X15,X16),X16) = k3_xboole_0(X16,k2_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f573,f558])).

fof(f573,plain,(
    ! [X15,X16] : k3_xboole_0(k2_xboole_0(X15,X16),X16) = k5_xboole_0(k5_xboole_0(X16,k2_xboole_0(X15,X16)),k2_xboole_0(X15,X16)) ),
    inference(forward_demodulation,[],[f563,f69])).

fof(f563,plain,(
    ! [X15,X16] : k3_xboole_0(k2_xboole_0(X15,X16),X16) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X15,X16),X16),k2_xboole_0(X15,X16)) ),
    inference(superposition,[],[f75,f412])).

fof(f412,plain,(
    ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f402,f195])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f62,plain,
    ( r2_hidden(sK3,sK4)
    | r2_hidden(sK2,sK4)
    | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f45])).

fof(f6544,plain,(
    ~ r2_hidden(sK3,sK4) ),
    inference(superposition,[],[f6441,f5813])).

fof(f6441,plain,(
    ! [X41,X42,X40] : ~ r2_hidden(X41,k4_xboole_0(X42,k2_tarski(X40,X41))) ),
    inference(subsumption_resolution,[],[f3939,f6429])).

fof(f6429,plain,(
    ! [X4,X2,X3] : r2_hidden(X2,k2_xboole_0(k2_tarski(X3,X2),X4)) ),
    inference(superposition,[],[f6415,f68])).

fof(f3939,plain,(
    ! [X41,X42,X40] :
      ( ~ r2_hidden(X41,k4_xboole_0(X42,k2_tarski(X40,X41)))
      | ~ r2_hidden(X41,k2_xboole_0(k2_tarski(X40,X41),X42)) ) ),
    inference(superposition,[],[f3025,f3727])).

fof(f3025,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X3,k5_xboole_0(k2_tarski(X5,X3),X4))
      | ~ r2_hidden(X3,X4) ) ),
    inference(resolution,[],[f90,f170])).

fof(f170,plain,(
    ! [X2,X1] : r2_hidden(X1,k2_tarski(X2,X1)) ),
    inference(superposition,[],[f168,f68])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 13:50:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (8926)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (8932)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (8942)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.51  % (8924)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.51  % (8927)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (8929)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.51  % (8926)Refutation not found, incomplete strategy% (8926)------------------------------
% 0.21/0.51  % (8926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (8926)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (8926)Memory used [KB]: 10874
% 0.21/0.51  % (8926)Time elapsed: 0.113 s
% 0.21/0.51  % (8926)------------------------------
% 0.21/0.51  % (8926)------------------------------
% 0.21/0.51  % (8930)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (8928)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.52  % (8934)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (8919)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (8925)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.53  % (8938)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (8921)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (8922)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (8920)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.53  % (8935)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (8940)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (8920)Refutation not found, incomplete strategy% (8920)------------------------------
% 0.21/0.54  % (8920)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (8920)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (8920)Memory used [KB]: 10874
% 0.21/0.54  % (8920)Time elapsed: 0.137 s
% 0.21/0.54  % (8920)------------------------------
% 0.21/0.54  % (8920)------------------------------
% 0.21/0.54  % (8918)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (8943)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.54  % (8945)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (8946)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (8923)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.55  % (8941)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (8944)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.55  % (8937)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.55  % (8947)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.56  % (8936)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (8935)Refutation not found, incomplete strategy% (8935)------------------------------
% 0.21/0.56  % (8935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (8935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (8935)Memory used [KB]: 10618
% 0.21/0.56  % (8935)Time elapsed: 0.163 s
% 0.21/0.56  % (8935)------------------------------
% 0.21/0.56  % (8935)------------------------------
% 0.21/0.56  % (8939)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (8933)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.57  % (8931)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 2.14/0.69  % (8967)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.14/0.72  % (8969)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.89/0.74  % (8968)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.36/0.82  % (8923)Time limit reached!
% 3.36/0.82  % (8923)------------------------------
% 3.36/0.82  % (8923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.36/0.82  % (8923)Termination reason: Time limit
% 3.36/0.82  % (8923)Termination phase: Saturation
% 3.36/0.82  
% 3.36/0.82  % (8923)Memory used [KB]: 8827
% 3.36/0.82  % (8923)Time elapsed: 0.400 s
% 3.36/0.82  % (8923)------------------------------
% 3.36/0.82  % (8923)------------------------------
% 4.26/0.92  % (8930)Time limit reached!
% 4.26/0.92  % (8930)------------------------------
% 4.26/0.92  % (8930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.92  % (8930)Termination reason: Time limit
% 4.26/0.92  
% 4.26/0.92  % (8930)Memory used [KB]: 7547
% 4.26/0.92  % (8930)Time elapsed: 0.518 s
% 4.26/0.92  % (8930)------------------------------
% 4.26/0.92  % (8930)------------------------------
% 4.26/0.92  % (8928)Time limit reached!
% 4.26/0.92  % (8928)------------------------------
% 4.26/0.92  % (8928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.92  % (8928)Termination reason: Time limit
% 4.26/0.92  
% 4.26/0.92  % (8928)Memory used [KB]: 17142
% 4.26/0.92  % (8928)Time elapsed: 0.520 s
% 4.26/0.92  % (8928)------------------------------
% 4.26/0.92  % (8928)------------------------------
% 4.26/0.93  % (8918)Time limit reached!
% 4.26/0.93  % (8918)------------------------------
% 4.26/0.93  % (8918)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.93  % (8918)Termination reason: Time limit
% 4.26/0.93  
% 4.26/0.93  % (8918)Memory used [KB]: 2430
% 4.26/0.93  % (8918)Time elapsed: 0.526 s
% 4.26/0.93  % (8918)------------------------------
% 4.26/0.93  % (8918)------------------------------
% 4.26/0.93  % (8925)Refutation found. Thanks to Tanya!
% 4.26/0.93  % SZS status Theorem for theBenchmark
% 4.26/0.93  % SZS output start Proof for theBenchmark
% 4.26/0.93  fof(f6545,plain,(
% 4.26/0.93    $false),
% 4.26/0.93    inference(subsumption_resolution,[],[f6544,f6458])).
% 4.26/0.93  fof(f6458,plain,(
% 4.26/0.93    r2_hidden(sK3,sK4)),
% 4.26/0.93    inference(subsumption_resolution,[],[f3630,f6452])).
% 4.26/0.93  fof(f6452,plain,(
% 4.26/0.93    ~r2_hidden(sK2,sK4)),
% 4.26/0.93    inference(superposition,[],[f6416,f5813])).
% 4.26/0.93  fof(f5813,plain,(
% 4.26/0.93    sK4 = k4_xboole_0(sK4,k2_tarski(sK2,sK3))),
% 4.26/0.93    inference(superposition,[],[f3662,f5665])).
% 4.26/0.93  fof(f5665,plain,(
% 4.26/0.93    k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 4.26/0.93    inference(global_subsumption,[],[f61,f60,f3630])).
% 4.26/0.93  fof(f60,plain,(
% 4.26/0.93    ~r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 4.26/0.93    inference(cnf_transformation,[],[f45])).
% 4.26/0.93  fof(f45,plain,(
% 4.26/0.93    (r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4))),
% 4.26/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f43,f44])).
% 4.26/0.93  fof(f44,plain,(
% 4.26/0.93    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)) & ((~r2_hidden(sK3,sK4) & ~r2_hidden(sK2,sK4)) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)))),
% 4.26/0.93    introduced(choice_axiom,[])).
% 4.26/0.93  fof(f43,plain,(
% 4.26/0.93    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.26/0.93    inference(flattening,[],[f42])).
% 4.26/0.93  fof(f42,plain,(
% 4.26/0.93    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 4.26/0.93    inference(nnf_transformation,[],[f33])).
% 4.26/0.93  fof(f33,plain,(
% 4.26/0.93    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.26/0.93    inference(ennf_transformation,[],[f30])).
% 4.26/0.93  fof(f30,negated_conjecture,(
% 4.26/0.93    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.26/0.93    inference(negated_conjecture,[],[f29])).
% 4.26/0.93  fof(f29,conjecture,(
% 4.26/0.93    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 4.26/0.93  fof(f61,plain,(
% 4.26/0.93    ~r2_hidden(sK3,sK4) | k2_tarski(sK2,sK3) = k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 4.26/0.93    inference(cnf_transformation,[],[f45])).
% 4.26/0.93  fof(f3662,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 4.26/0.93    inference(forward_demodulation,[],[f3658,f568])).
% 4.26/0.93  fof(f568,plain,(
% 4.26/0.93    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 4.26/0.93    inference(forward_demodulation,[],[f567,f66])).
% 4.26/0.93  fof(f66,plain,(
% 4.26/0.93    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.26/0.93    inference(cnf_transformation,[],[f31])).
% 4.26/0.93  fof(f31,plain,(
% 4.26/0.93    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.26/0.93    inference(rectify,[],[f3])).
% 4.26/0.93  fof(f3,axiom,(
% 4.26/0.93    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 4.26/0.93  fof(f567,plain,(
% 4.26/0.93    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 4.26/0.93    inference(forward_demodulation,[],[f549,f67])).
% 4.26/0.93  fof(f67,plain,(
% 4.26/0.93    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 4.26/0.93    inference(cnf_transformation,[],[f32])).
% 4.26/0.93  fof(f32,plain,(
% 4.26/0.93    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 4.26/0.93    inference(rectify,[],[f2])).
% 4.26/0.93  fof(f2,axiom,(
% 4.26/0.93    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 4.26/0.93  fof(f549,plain,(
% 4.26/0.93    ( ! [X0] : (k3_xboole_0(X0,X0) = k5_xboole_0(k1_xboole_0,k2_xboole_0(X0,X0))) )),
% 4.26/0.93    inference(superposition,[],[f75,f63])).
% 4.26/0.93  fof(f63,plain,(
% 4.26/0.93    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.26/0.93    inference(cnf_transformation,[],[f12])).
% 4.26/0.93  fof(f12,axiom,(
% 4.26/0.93    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.26/0.93  fof(f75,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.26/0.93    inference(cnf_transformation,[],[f13])).
% 4.26/0.93  fof(f13,axiom,(
% 4.26/0.93    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.26/0.93  fof(f3658,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = k5_xboole_0(k1_xboole_0,X0)) )),
% 4.26/0.93    inference(superposition,[],[f987,f3623])).
% 4.26/0.93  fof(f3623,plain,(
% 4.26/0.93    ( ! [X15,X16] : (k1_xboole_0 = k3_xboole_0(X15,k4_xboole_0(X16,X15))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f3622,f63])).
% 4.26/0.93  fof(f3622,plain,(
% 4.26/0.93    ( ! [X15,X16] : (k5_xboole_0(X15,X15) = k3_xboole_0(X15,k4_xboole_0(X16,X15))) )),
% 4.26/0.93    inference(backward_demodulation,[],[f3578,f3615])).
% 4.26/0.93  fof(f3615,plain,(
% 4.26/0.93    ( ! [X19,X18] : (k5_xboole_0(k2_xboole_0(X18,X19),k4_xboole_0(X19,X18)) = X18) )),
% 4.26/0.93    inference(backward_demodulation,[],[f3580,f3603])).
% 4.26/0.93  fof(f3603,plain,(
% 4.26/0.93    ( ! [X19,X18] : (k4_xboole_0(X18,X19) = k5_xboole_0(X19,k2_xboole_0(X18,X19))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f3555,f72])).
% 4.26/0.93  fof(f72,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.26/0.93    inference(cnf_transformation,[],[f5])).
% 4.26/0.93  fof(f5,axiom,(
% 4.26/0.93    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.26/0.93  fof(f3555,plain,(
% 4.26/0.93    ( ! [X19,X18] : (k5_xboole_0(X19,k2_xboole_0(X18,X19)) = k5_xboole_0(X18,k3_xboole_0(X18,X19))) )),
% 4.26/0.93    inference(superposition,[],[f751,f738])).
% 4.26/0.93  fof(f738,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k2_xboole_0(X0,X1)))) )),
% 4.26/0.93    inference(superposition,[],[f87,f75])).
% 4.26/0.93  fof(f87,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.26/0.93    inference(cnf_transformation,[],[f11])).
% 4.26/0.93  fof(f11,axiom,(
% 4.26/0.93    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.26/0.93  fof(f751,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.26/0.93    inference(forward_demodulation,[],[f730,f568])).
% 4.26/0.93  fof(f730,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.26/0.93    inference(superposition,[],[f87,f63])).
% 4.26/0.93  fof(f3580,plain,(
% 4.26/0.93    ( ! [X19,X18] : (k5_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,k2_xboole_0(X19,X18))) = X18) )),
% 4.26/0.93    inference(forward_demodulation,[],[f3531,f791])).
% 4.26/0.93  fof(f791,plain,(
% 4.26/0.93    ( ! [X14,X13] : (k3_xboole_0(k2_xboole_0(X13,X14),X13) = X13) )),
% 4.26/0.93    inference(backward_demodulation,[],[f572,f789])).
% 4.26/0.93  fof(f789,plain,(
% 4.26/0.93    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = X5) )),
% 4.26/0.93    inference(backward_demodulation,[],[f557,f775])).
% 4.26/0.93  fof(f775,plain,(
% 4.26/0.93    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 4.26/0.93    inference(superposition,[],[f755,f751])).
% 4.26/0.93  fof(f755,plain,(
% 4.26/0.93    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 4.26/0.93    inference(superposition,[],[f751,f69])).
% 4.26/0.93  fof(f69,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.26/0.93    inference(cnf_transformation,[],[f1])).
% 4.26/0.93  fof(f1,axiom,(
% 4.26/0.93    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.26/0.93  fof(f557,plain,(
% 4.26/0.93    ( ! [X6,X5] : (k3_xboole_0(X5,k2_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,k2_xboole_0(X5,X6)),k2_xboole_0(X5,X6))) )),
% 4.26/0.93    inference(superposition,[],[f75,f73])).
% 4.26/0.93  fof(f73,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 4.26/0.93    inference(cnf_transformation,[],[f9])).
% 4.26/0.93  fof(f9,axiom,(
% 4.26/0.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X0,X1))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_xboole_1)).
% 4.26/0.93  fof(f572,plain,(
% 4.26/0.93    ( ! [X14,X13] : (k3_xboole_0(k2_xboole_0(X13,X14),X13) = k3_xboole_0(X13,k2_xboole_0(X13,X14))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f571,f557])).
% 4.26/0.93  fof(f571,plain,(
% 4.26/0.93    ( ! [X14,X13] : (k3_xboole_0(k2_xboole_0(X13,X14),X13) = k5_xboole_0(k5_xboole_0(X13,k2_xboole_0(X13,X14)),k2_xboole_0(X13,X14))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f562,f69])).
% 4.26/0.93  fof(f562,plain,(
% 4.26/0.93    ( ! [X14,X13] : (k3_xboole_0(k2_xboole_0(X13,X14),X13) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X13,X14),X13),k2_xboole_0(X13,X14))) )),
% 4.26/0.93    inference(superposition,[],[f75,f402])).
% 4.26/0.93  fof(f402,plain,(
% 4.26/0.93    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(k2_xboole_0(X2,X3),X2)) )),
% 4.26/0.93    inference(superposition,[],[f287,f120])).
% 4.26/0.93  fof(f120,plain,(
% 4.26/0.93    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k3_tarski(k2_tarski(X2,X1))) )),
% 4.26/0.93    inference(superposition,[],[f71,f68])).
% 4.26/0.93  fof(f68,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.26/0.93    inference(cnf_transformation,[],[f14])).
% 4.26/0.93  fof(f14,axiom,(
% 4.26/0.93    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 4.26/0.93  fof(f71,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.26/0.93    inference(cnf_transformation,[],[f27])).
% 4.26/0.93  fof(f27,axiom,(
% 4.26/0.93    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 4.26/0.93  fof(f287,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,k2_xboole_0(X0,X1)))) )),
% 4.26/0.93    inference(resolution,[],[f225,f84])).
% 4.26/0.93  fof(f84,plain,(
% 4.26/0.93    ( ! [X0,X1] : (~sP0(X0,X1) | k3_tarski(X0) = X1) )),
% 4.26/0.93    inference(cnf_transformation,[],[f52])).
% 4.26/0.93  fof(f52,plain,(
% 4.26/0.93    ! [X0,X1] : ((k3_tarski(X0) = X1 | ~sP0(X0,X1)) & (sP0(X0,X1) | k3_tarski(X0) != X1))),
% 4.26/0.93    inference(nnf_transformation,[],[f39])).
% 4.26/0.93  fof(f39,plain,(
% 4.26/0.93    ! [X0,X1] : (k3_tarski(X0) = X1 <=> sP0(X0,X1))),
% 4.26/0.93    inference(definition_folding,[],[f26,f38])).
% 4.26/0.93  fof(f38,plain,(
% 4.26/0.93    ! [X0,X1] : (sP0(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 4.26/0.93    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 4.26/0.93  fof(f26,axiom,(
% 4.26/0.93    ! [X0,X1] : (k3_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3))))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).
% 4.26/0.93  fof(f225,plain,(
% 4.26/0.93    ( ! [X4,X5] : (sP0(k2_tarski(X4,k2_xboole_0(X4,X5)),k2_xboole_0(X4,X5))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f223,f68])).
% 4.26/0.93  fof(f223,plain,(
% 4.26/0.93    ( ! [X4,X5] : (sP0(k2_tarski(k2_xboole_0(X4,X5),X4),k2_xboole_0(X4,X5))) )),
% 4.26/0.93    inference(superposition,[],[f128,f73])).
% 4.26/0.93  fof(f128,plain,(
% 4.26/0.93    ( ! [X2,X1] : (sP0(k2_tarski(X2,X1),k2_xboole_0(X1,X2))) )),
% 4.26/0.93    inference(superposition,[],[f122,f68])).
% 4.26/0.93  fof(f122,plain,(
% 4.26/0.93    ( ! [X0,X1] : (sP0(k2_tarski(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.26/0.93    inference(superposition,[],[f110,f71])).
% 4.26/0.93  fof(f110,plain,(
% 4.26/0.93    ( ! [X0] : (sP0(X0,k3_tarski(X0))) )),
% 4.26/0.93    inference(equality_resolution,[],[f83])).
% 4.26/0.93  fof(f83,plain,(
% 4.26/0.93    ( ! [X0,X1] : (sP0(X0,X1) | k3_tarski(X0) != X1) )),
% 4.26/0.93    inference(cnf_transformation,[],[f52])).
% 4.26/0.93  fof(f3531,plain,(
% 4.26/0.93    ( ! [X19,X18] : (k5_xboole_0(k2_xboole_0(X18,X19),k5_xboole_0(X18,k2_xboole_0(X19,X18))) = k3_xboole_0(k2_xboole_0(X18,X19),X18)) )),
% 4.26/0.93    inference(superposition,[],[f738,f2654])).
% 4.26/0.93  fof(f2654,plain,(
% 4.26/0.93    ( ! [X6,X7] : (k2_xboole_0(X7,X6) = k2_xboole_0(k2_xboole_0(X6,X7),X6)) )),
% 4.26/0.93    inference(superposition,[],[f1870,f120])).
% 4.26/0.93  fof(f1870,plain,(
% 4.26/0.93    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k3_tarski(k2_tarski(X3,k2_xboole_0(X3,X4)))) )),
% 4.26/0.93    inference(resolution,[],[f1731,f84])).
% 4.26/0.93  fof(f1731,plain,(
% 4.26/0.93    ( ! [X12,X11] : (sP0(k2_tarski(X11,k2_xboole_0(X11,X12)),k2_xboole_0(X12,X11))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f1730,f74])).
% 4.26/0.93  fof(f74,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)) )),
% 4.26/0.93    inference(cnf_transformation,[],[f7])).
% 4.26/0.93  fof(f7,axiom,(
% 4.26/0.93    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,X0)) = k2_xboole_0(X0,X1)),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 4.26/0.93  fof(f1730,plain,(
% 4.26/0.93    ( ! [X12,X11] : (sP0(k2_tarski(X11,k2_xboole_0(X11,k4_xboole_0(X12,X11))),k2_xboole_0(X12,X11))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f1695,f195])).
% 4.26/0.93  fof(f195,plain,(
% 4.26/0.93    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X3,X2)) )),
% 4.26/0.93    inference(superposition,[],[f120,f71])).
% 4.26/0.93  fof(f1695,plain,(
% 4.26/0.93    ( ! [X12,X11] : (sP0(k2_tarski(X11,k2_xboole_0(k4_xboole_0(X12,X11),X11)),k2_xboole_0(X12,X11))) )),
% 4.26/0.93    inference(superposition,[],[f1577,f538])).
% 4.26/0.93  fof(f538,plain,(
% 4.26/0.93    ( ! [X8,X7] : (k2_xboole_0(X8,X7) = k2_xboole_0(X7,k4_xboole_0(X8,X7))) )),
% 4.26/0.93    inference(superposition,[],[f372,f71])).
% 4.26/0.93  fof(f372,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k3_tarski(k2_tarski(X0,k4_xboole_0(X1,X0)))) )),
% 4.26/0.93    inference(resolution,[],[f302,f84])).
% 4.26/0.93  fof(f302,plain,(
% 4.26/0.93    ( ! [X2,X1] : (sP0(k2_tarski(X1,k4_xboole_0(X2,X1)),k2_xboole_0(X2,X1))) )),
% 4.26/0.93    inference(superposition,[],[f234,f195])).
% 4.26/0.93  fof(f234,plain,(
% 4.26/0.93    ( ! [X6,X7] : (sP0(k2_tarski(X6,k4_xboole_0(X7,X6)),k2_xboole_0(X6,X7))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f229,f68])).
% 4.26/0.93  fof(f229,plain,(
% 4.26/0.93    ( ! [X6,X7] : (sP0(k2_tarski(k4_xboole_0(X7,X6),X6),k2_xboole_0(X6,X7))) )),
% 4.26/0.93    inference(superposition,[],[f128,f74])).
% 4.26/0.93  fof(f1577,plain,(
% 4.26/0.93    ( ! [X17,X16] : (sP0(k2_tarski(X16,k2_xboole_0(X17,X16)),k2_xboole_0(X16,X17))) )),
% 4.26/0.93    inference(superposition,[],[f122,f1339])).
% 4.26/0.93  fof(f1339,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k2_xboole_0(X1,X0))) )),
% 4.26/0.93    inference(superposition,[],[f88,f402])).
% 4.26/0.93  fof(f88,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 4.26/0.93    inference(cnf_transformation,[],[f8])).
% 4.26/0.93  fof(f8,axiom,(
% 4.26/0.93    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).
% 4.26/0.93  fof(f3578,plain,(
% 4.26/0.93    ( ! [X15,X16] : (k3_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k5_xboole_0(k2_xboole_0(X15,X16),k4_xboole_0(X16,X15)))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f3529,f69])).
% 4.26/0.93  fof(f3529,plain,(
% 4.26/0.93    ( ! [X15,X16] : (k3_xboole_0(X15,k4_xboole_0(X16,X15)) = k5_xboole_0(X15,k5_xboole_0(k4_xboole_0(X16,X15),k2_xboole_0(X15,X16)))) )),
% 4.26/0.93    inference(superposition,[],[f738,f74])).
% 4.26/0.93  fof(f987,plain,(
% 4.26/0.93    ( ! [X15,X16] : (k4_xboole_0(X15,X16) = k5_xboole_0(k3_xboole_0(X15,X16),X15)) )),
% 4.26/0.93    inference(superposition,[],[f776,f757])).
% 4.26/0.93  fof(f757,plain,(
% 4.26/0.93    ( ! [X8,X7] : (k3_xboole_0(X7,X8) = k5_xboole_0(X7,k4_xboole_0(X7,X8))) )),
% 4.26/0.93    inference(superposition,[],[f751,f72])).
% 4.26/0.93  fof(f776,plain,(
% 4.26/0.93    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 4.26/0.93    inference(superposition,[],[f755,f755])).
% 4.26/0.93  fof(f6416,plain,(
% 4.26/0.93    ( ! [X45,X43,X44] : (~r2_hidden(X43,k4_xboole_0(X45,k2_tarski(X43,X44)))) )),
% 4.26/0.93    inference(subsumption_resolution,[],[f3940,f6415])).
% 4.26/0.93  fof(f6415,plain,(
% 4.26/0.93    ( ! [X39,X41,X40] : (r2_hidden(X39,k2_xboole_0(k2_tarski(X39,X40),X41))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f6394,f71])).
% 4.26/0.93  fof(f6394,plain,(
% 4.26/0.93    ( ! [X39,X41,X40] : (r2_hidden(X39,k3_tarski(k2_tarski(k2_tarski(X39,X40),X41)))) )),
% 4.26/0.93    inference(resolution,[],[f6130,f168])).
% 4.26/0.93  fof(f168,plain,(
% 4.26/0.93    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 4.26/0.93    inference(superposition,[],[f164,f70])).
% 4.26/0.93  fof(f70,plain,(
% 4.26/0.93    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.26/0.93    inference(cnf_transformation,[],[f20])).
% 4.26/0.93  fof(f20,axiom,(
% 4.26/0.93    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 4.26/0.93  fof(f164,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X1,X2))) )),
% 4.26/0.93    inference(resolution,[],[f114,f113])).
% 4.26/0.93  fof(f113,plain,(
% 4.26/0.93    ( ! [X0,X5,X3,X1] : (~sP1(X0,X1,X5,X3) | r2_hidden(X5,X3)) )),
% 4.26/0.93    inference(equality_resolution,[],[f96])).
% 4.26/0.93  fof(f96,plain,(
% 4.26/0.93    ( ! [X2,X0,X5,X3,X1] : (r2_hidden(X5,X3) | X2 != X5 | ~sP1(X0,X1,X2,X3)) )),
% 4.26/0.93    inference(cnf_transformation,[],[f58])).
% 4.26/0.93  fof(f58,plain,(
% 4.26/0.93    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | (((sK8(X0,X1,X2,X3) != X0 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X2) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X0 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X2 | r2_hidden(sK8(X0,X1,X2,X3),X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 4.26/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f56,f57])).
% 4.26/0.93  fof(f57,plain,(
% 4.26/0.93    ! [X3,X2,X1,X0] : (? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3))) => (((sK8(X0,X1,X2,X3) != X0 & sK8(X0,X1,X2,X3) != X1 & sK8(X0,X1,X2,X3) != X2) | ~r2_hidden(sK8(X0,X1,X2,X3),X3)) & (sK8(X0,X1,X2,X3) = X0 | sK8(X0,X1,X2,X3) = X1 | sK8(X0,X1,X2,X3) = X2 | r2_hidden(sK8(X0,X1,X2,X3),X3))))),
% 4.26/0.93    introduced(choice_axiom,[])).
% 4.26/0.93  fof(f56,plain,(
% 4.26/0.93    ! [X0,X1,X2,X3] : ((sP1(X0,X1,X2,X3) | ? [X4] : (((X0 != X4 & X1 != X4 & X2 != X4) | ~r2_hidden(X4,X3)) & (X0 = X4 | X1 = X4 | X2 = X4 | r2_hidden(X4,X3)))) & (! [X5] : ((r2_hidden(X5,X3) | (X0 != X5 & X1 != X5 & X2 != X5)) & (X0 = X5 | X1 = X5 | X2 = X5 | ~r2_hidden(X5,X3))) | ~sP1(X0,X1,X2,X3)))),
% 4.26/0.93    inference(rectify,[],[f55])).
% 4.26/0.93  fof(f55,plain,(
% 4.26/0.93    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & (X2 = X4 | X1 = X4 | X0 = X4 | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & (X2 = X4 | X1 = X4 | X0 = X4 | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 4.26/0.93    inference(flattening,[],[f54])).
% 4.26/0.93  fof(f54,plain,(
% 4.26/0.93    ! [X2,X1,X0,X3] : ((sP1(X2,X1,X0,X3) | ? [X4] : (((X2 != X4 & X1 != X4 & X0 != X4) | ~r2_hidden(X4,X3)) & ((X2 = X4 | X1 = X4 | X0 = X4) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | (X2 != X4 & X1 != X4 & X0 != X4)) & ((X2 = X4 | X1 = X4 | X0 = X4) | ~r2_hidden(X4,X3))) | ~sP1(X2,X1,X0,X3)))),
% 4.26/0.93    inference(nnf_transformation,[],[f40])).
% 4.26/0.93  fof(f40,plain,(
% 4.26/0.93    ! [X2,X1,X0,X3] : (sP1(X2,X1,X0,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.26/0.93    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 4.26/0.93  fof(f114,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (sP1(X2,X1,X0,k1_enumset1(X0,X1,X2))) )),
% 4.26/0.93    inference(equality_resolution,[],[f103])).
% 4.26/0.93  fof(f103,plain,(
% 4.26/0.93    ( ! [X2,X0,X3,X1] : (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.26/0.93    inference(cnf_transformation,[],[f59])).
% 4.26/0.93  fof(f59,plain,(
% 4.26/0.93    ! [X0,X1,X2,X3] : ((k1_enumset1(X0,X1,X2) = X3 | ~sP1(X2,X1,X0,X3)) & (sP1(X2,X1,X0,X3) | k1_enumset1(X0,X1,X2) != X3))),
% 4.26/0.93    inference(nnf_transformation,[],[f41])).
% 4.26/0.93  fof(f41,plain,(
% 4.26/0.93    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> sP1(X2,X1,X0,X3))),
% 4.26/0.93    inference(definition_folding,[],[f37,f40])).
% 4.26/0.93  fof(f37,plain,(
% 4.26/0.93    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.26/0.93    inference(ennf_transformation,[],[f15])).
% 4.26/0.93  fof(f15,axiom,(
% 4.26/0.93    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).
% 4.26/0.93  fof(f6130,plain,(
% 4.26/0.93    ( ! [X26,X27,X25] : (~r2_hidden(k2_tarski(X25,X26),X27) | r2_hidden(X25,k3_tarski(X27))) )),
% 4.26/0.93    inference(resolution,[],[f6109,f168])).
% 4.26/0.93  fof(f6109,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X0,X1) | r2_hidden(X2,k3_tarski(X1))) )),
% 4.26/0.93    inference(resolution,[],[f79,f110])).
% 4.26/0.93  fof(f79,plain,(
% 4.26/0.93    ( ! [X6,X0,X5,X1] : (~sP0(X0,X1) | ~r2_hidden(X6,X0) | ~r2_hidden(X5,X6) | r2_hidden(X5,X1)) )),
% 4.26/0.93    inference(cnf_transformation,[],[f51])).
% 4.26/0.93  fof(f51,plain,(
% 4.26/0.93    ! [X0,X1] : ((sP0(X0,X1) | ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & ((r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))) | r2_hidden(sK5(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & ((r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 4.26/0.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7])],[f47,f50,f49,f48])).
% 4.26/0.93  fof(f48,plain,(
% 4.26/0.93    ! [X1,X0] : (? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1))) => ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(sK5(X0,X1),X3)) | ~r2_hidden(sK5(X0,X1),X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) | r2_hidden(sK5(X0,X1),X1))))),
% 4.26/0.93    introduced(choice_axiom,[])).
% 4.26/0.93  fof(f49,plain,(
% 4.26/0.93    ! [X1,X0] : (? [X4] : (r2_hidden(X4,X0) & r2_hidden(sK5(X0,X1),X4)) => (r2_hidden(sK6(X0,X1),X0) & r2_hidden(sK5(X0,X1),sK6(X0,X1))))),
% 4.26/0.93    introduced(choice_axiom,[])).
% 4.26/0.93  fof(f50,plain,(
% 4.26/0.93    ! [X5,X0] : (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) => (r2_hidden(sK7(X0,X5),X0) & r2_hidden(X5,sK7(X0,X5))))),
% 4.26/0.93    introduced(choice_axiom,[])).
% 4.26/0.93  fof(f47,plain,(
% 4.26/0.93    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X4] : (r2_hidden(X4,X0) & r2_hidden(X2,X4)) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (~r2_hidden(X6,X0) | ~r2_hidden(X5,X6))) & (? [X7] : (r2_hidden(X7,X0) & r2_hidden(X5,X7)) | ~r2_hidden(X5,X1))) | ~sP0(X0,X1)))),
% 4.26/0.93    inference(rectify,[],[f46])).
% 4.26/0.93  fof(f46,plain,(
% 4.26/0.93    ! [X0,X1] : ((sP0(X0,X1) | ? [X2] : ((! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3)) | ~r2_hidden(X2,X1)) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (~r2_hidden(X3,X0) | ~r2_hidden(X2,X3))) & (? [X3] : (r2_hidden(X3,X0) & r2_hidden(X2,X3)) | ~r2_hidden(X2,X1))) | ~sP0(X0,X1)))),
% 4.26/0.93    inference(nnf_transformation,[],[f38])).
% 4.26/0.93  fof(f3940,plain,(
% 4.26/0.93    ( ! [X45,X43,X44] : (~r2_hidden(X43,k4_xboole_0(X45,k2_tarski(X43,X44))) | ~r2_hidden(X43,k2_xboole_0(k2_tarski(X43,X44),X45))) )),
% 4.26/0.93    inference(superposition,[],[f3024,f3727])).
% 4.26/0.93  fof(f3727,plain,(
% 4.26/0.93    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X2,k2_xboole_0(X2,X1))) )),
% 4.26/0.93    inference(superposition,[],[f3603,f195])).
% 4.26/0.93  fof(f3024,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (~r2_hidden(X0,k5_xboole_0(k2_tarski(X0,X2),X1)) | ~r2_hidden(X0,X1)) )),
% 4.26/0.93    inference(resolution,[],[f90,f168])).
% 4.26/0.93  fof(f90,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X0,X2) | ~r2_hidden(X0,k5_xboole_0(X1,X2))) )),
% 4.26/0.93    inference(cnf_transformation,[],[f53])).
% 4.26/0.93  fof(f53,plain,(
% 4.26/0.93    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 4.26/0.93    inference(nnf_transformation,[],[f35])).
% 4.26/0.93  fof(f35,plain,(
% 4.26/0.93    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 4.26/0.93    inference(ennf_transformation,[],[f4])).
% 4.26/0.93  fof(f4,axiom,(
% 4.26/0.93    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).
% 4.26/0.93  fof(f3630,plain,(
% 4.26/0.93    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4)),
% 4.26/0.93    inference(subsumption_resolution,[],[f62,f3620])).
% 4.26/0.93  fof(f3620,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (k2_tarski(X2,X0) = k4_xboole_0(k2_tarski(X2,X0),X1) | r2_hidden(X0,X1) | r2_hidden(X2,X1)) )),
% 4.26/0.93    inference(backward_demodulation,[],[f3286,f3603])).
% 4.26/0.93  fof(f3286,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (r2_hidden(X0,X1) | r2_hidden(X2,X1) | k2_tarski(X2,X0) = k5_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X0),X1))) )),
% 4.26/0.93    inference(resolution,[],[f93,f974])).
% 4.26/0.93  fof(f974,plain,(
% 4.26/0.93    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X1,k2_xboole_0(X0,X1)) = X0) )),
% 4.26/0.93    inference(backward_demodulation,[],[f76,f972])).
% 4.26/0.93  fof(f972,plain,(
% 4.26/0.93    ( ! [X2,X1] : (k5_xboole_0(X2,k2_xboole_0(X1,X2)) = k4_xboole_0(k2_xboole_0(X1,X2),X2)) )),
% 4.26/0.93    inference(forward_demodulation,[],[f971,f69])).
% 4.26/0.93  fof(f971,plain,(
% 4.26/0.93    ( ! [X2,X1] : (k4_xboole_0(k2_xboole_0(X1,X2),X2) = k5_xboole_0(k2_xboole_0(X1,X2),X2)) )),
% 4.26/0.93    inference(superposition,[],[f72,f792])).
% 4.26/0.93  fof(f792,plain,(
% 4.26/0.93    ( ! [X15,X16] : (k3_xboole_0(k2_xboole_0(X15,X16),X16) = X16) )),
% 4.26/0.93    inference(backward_demodulation,[],[f574,f790])).
% 4.26/0.93  fof(f790,plain,(
% 4.26/0.93    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = X7) )),
% 4.26/0.93    inference(backward_demodulation,[],[f558,f775])).
% 4.26/0.93  fof(f558,plain,(
% 4.26/0.93    ( ! [X8,X7] : (k3_xboole_0(X7,k2_xboole_0(X8,X7)) = k5_xboole_0(k5_xboole_0(X7,k2_xboole_0(X8,X7)),k2_xboole_0(X8,X7))) )),
% 4.26/0.93    inference(superposition,[],[f75,f218])).
% 4.26/0.93  fof(f218,plain,(
% 4.26/0.93    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) )),
% 4.26/0.93    inference(superposition,[],[f73,f195])).
% 4.26/0.93  fof(f574,plain,(
% 4.26/0.93    ( ! [X15,X16] : (k3_xboole_0(k2_xboole_0(X15,X16),X16) = k3_xboole_0(X16,k2_xboole_0(X15,X16))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f573,f558])).
% 4.26/0.93  fof(f573,plain,(
% 4.26/0.93    ( ! [X15,X16] : (k3_xboole_0(k2_xboole_0(X15,X16),X16) = k5_xboole_0(k5_xboole_0(X16,k2_xboole_0(X15,X16)),k2_xboole_0(X15,X16))) )),
% 4.26/0.93    inference(forward_demodulation,[],[f563,f69])).
% 4.26/0.93  fof(f563,plain,(
% 4.26/0.93    ( ! [X15,X16] : (k3_xboole_0(k2_xboole_0(X15,X16),X16) = k5_xboole_0(k5_xboole_0(k2_xboole_0(X15,X16),X16),k2_xboole_0(X15,X16))) )),
% 4.26/0.93    inference(superposition,[],[f75,f412])).
% 4.26/0.93  fof(f412,plain,(
% 4.26/0.93    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(k2_xboole_0(X2,X1),X1)) )),
% 4.26/0.93    inference(superposition,[],[f402,f195])).
% 4.26/0.93  fof(f76,plain,(
% 4.26/0.93    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0) )),
% 4.26/0.93    inference(cnf_transformation,[],[f34])).
% 4.26/0.93  fof(f34,plain,(
% 4.26/0.93    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 4.26/0.93    inference(ennf_transformation,[],[f10])).
% 4.26/0.93  fof(f10,axiom,(
% 4.26/0.93    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 4.26/0.93  fof(f93,plain,(
% 4.26/0.93    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 4.26/0.93    inference(cnf_transformation,[],[f36])).
% 4.26/0.93  fof(f36,plain,(
% 4.26/0.93    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 4.26/0.93    inference(ennf_transformation,[],[f28])).
% 4.26/0.93  fof(f28,axiom,(
% 4.26/0.93    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 4.26/0.93    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 4.26/0.93  fof(f62,plain,(
% 4.26/0.93    r2_hidden(sK3,sK4) | r2_hidden(sK2,sK4) | k2_tarski(sK2,sK3) != k4_xboole_0(k2_tarski(sK2,sK3),sK4)),
% 4.26/0.93    inference(cnf_transformation,[],[f45])).
% 4.26/0.93  fof(f6544,plain,(
% 4.26/0.93    ~r2_hidden(sK3,sK4)),
% 4.26/0.93    inference(superposition,[],[f6441,f5813])).
% 4.26/0.93  fof(f6441,plain,(
% 4.26/0.93    ( ! [X41,X42,X40] : (~r2_hidden(X41,k4_xboole_0(X42,k2_tarski(X40,X41)))) )),
% 4.26/0.93    inference(subsumption_resolution,[],[f3939,f6429])).
% 4.26/0.93  fof(f6429,plain,(
% 4.26/0.93    ( ! [X4,X2,X3] : (r2_hidden(X2,k2_xboole_0(k2_tarski(X3,X2),X4))) )),
% 4.26/0.93    inference(superposition,[],[f6415,f68])).
% 4.26/0.93  fof(f3939,plain,(
% 4.26/0.93    ( ! [X41,X42,X40] : (~r2_hidden(X41,k4_xboole_0(X42,k2_tarski(X40,X41))) | ~r2_hidden(X41,k2_xboole_0(k2_tarski(X40,X41),X42))) )),
% 4.26/0.93    inference(superposition,[],[f3025,f3727])).
% 4.26/0.93  fof(f3025,plain,(
% 4.26/0.93    ( ! [X4,X5,X3] : (~r2_hidden(X3,k5_xboole_0(k2_tarski(X5,X3),X4)) | ~r2_hidden(X3,X4)) )),
% 4.26/0.93    inference(resolution,[],[f90,f170])).
% 4.26/0.93  fof(f170,plain,(
% 4.26/0.93    ( ! [X2,X1] : (r2_hidden(X1,k2_tarski(X2,X1))) )),
% 4.26/0.93    inference(superposition,[],[f168,f68])).
% 4.26/0.93  % SZS output end Proof for theBenchmark
% 4.26/0.93  % (8925)------------------------------
% 4.26/0.93  % (8925)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.26/0.93  % (8925)Termination reason: Refutation
% 4.26/0.93  
% 4.26/0.93  % (8925)Memory used [KB]: 10362
% 4.26/0.93  % (8925)Time elapsed: 0.521 s
% 4.26/0.93  % (8925)------------------------------
% 4.26/0.93  % (8925)------------------------------
% 4.26/0.93  % (8915)Success in time 0.573 s
%------------------------------------------------------------------------------
