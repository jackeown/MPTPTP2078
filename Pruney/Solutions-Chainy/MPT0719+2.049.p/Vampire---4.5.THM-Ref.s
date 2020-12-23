%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:02 EST 2020

% Result     : Theorem 3.00s
% Output     : Refutation 3.00s
% Verified   : 
% Statistics : Number of formulae       :  145 (2752 expanded)
%              Number of leaves         :   21 ( 786 expanded)
%              Depth                    :   48
%              Number of atoms          :  303 (4447 expanded)
%              Number of equality atoms :   88 (1572 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3992,plain,(
    $false ),
    inference(global_subsumption,[],[f3981,f3991])).

fof(f3991,plain,(
    ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3990,f269])).

fof(f269,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(superposition,[],[f85,f108])).

fof(f108,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(X2,X2) ),
    inference(superposition,[],[f104,f51])).

fof(f51,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f104,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X0) = k3_xboole_0(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f103,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f103,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X0),X1) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k2_xboole_0(X1,X2))
      | r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
      | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
     => r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

fof(f85,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k4_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)))) ),
    inference(equality_resolution,[],[f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2)))) ) ),
    inference(definition_unfolding,[],[f75,f81])).

fof(f81,plain,(
    ! [X0] : k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0)) ),
    inference(definition_unfolding,[],[f52,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f52,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
        | X0 = X2
        | ~ r2_hidden(X0,X1) )
      & ( ( X0 != X2
          & r2_hidden(X0,X1) )
        | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f3990,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(forward_demodulation,[],[f3989,f3979])).

fof(f3979,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f65,f3977])).

fof(f3977,plain,(
    ! [X12] : k1_xboole_0 = sK2(k1_xboole_0,X12) ),
    inference(forward_demodulation,[],[f3976,f51])).

fof(f3976,plain,(
    ! [X12] : sK2(k1_xboole_0,X12) = k3_xboole_0(sK2(k1_xboole_0,X12),k1_xboole_0) ),
    inference(superposition,[],[f169,f3965])).

fof(f3965,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(resolution,[],[f3603,f162])).

fof(f162,plain,(
    ! [X1] : r1_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f160,f96])).

fof(f96,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(resolution,[],[f61,f57])).

fof(f160,plain,(
    ! [X0,X1] : r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f72,f115])).

fof(f115,plain,(
    ! [X1] : r1_tarski(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f103,f108])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,X2))
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k5_xboole_0(X1,X2))
        | ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,k2_xboole_0(X1,X2)) )
      & ( ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
          & r1_tarski(X0,k2_xboole_0(X1,X2)) )
        | ~ r1_tarski(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k5_xboole_0(X1,X2))
    <=> ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
        & r1_tarski(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).

fof(f3603,plain,(
    ! [X6,X7] :
      ( ~ r1_xboole_0(X6,X6)
      | k1_xboole_0 = k2_zfmisc_1(X6,X7) ) ),
    inference(resolution,[],[f3587,f79])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))
      | ( ~ r1_xboole_0(X2,X3)
        & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        | r1_xboole_0(X0,X1) )
     => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).

fof(f3587,plain,(
    ! [X1] :
      ( ~ r1_xboole_0(X1,X1)
      | k1_xboole_0 = X1 ) ),
    inference(forward_demodulation,[],[f3572,f108])).

fof(f3572,plain,(
    ! [X1] :
      ( k4_xboole_0(X1,X1) = X1
      | ~ r1_xboole_0(X1,X1) ) ),
    inference(superposition,[],[f62,f3537])).

fof(f3537,plain,(
    ! [X1] : k2_xboole_0(X1,X1) = X1 ),
    inference(superposition,[],[f3005,f96])).

fof(f3005,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6 ),
    inference(forward_demodulation,[],[f3004,f2855])).

fof(f2855,plain,(
    ! [X20] : k4_xboole_0(X20,k1_xboole_0) = X20 ),
    inference(resolution,[],[f2697,f97])).

fof(f97,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) ),
    inference(superposition,[],[f58,f96])).

fof(f58,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_xboole_1)).

fof(f2697,plain,(
    ! [X2,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | k4_xboole_0(X1,k1_xboole_0) = X1 ) ),
    inference(resolution,[],[f2599,f99])).

fof(f99,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,k1_xboole_0)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(superposition,[],[f78,f51])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f2599,plain,(
    ! [X4] :
      ( ~ r1_xboole_0(X4,k1_xboole_0)
      | k4_xboole_0(X4,k1_xboole_0) = X4 ) ),
    inference(condensation,[],[f2573])).

fof(f2573,plain,(
    ! [X4,X5] :
      ( k4_xboole_0(X4,k1_xboole_0) = X4
      | ~ r1_xboole_0(X4,k1_xboole_0)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f62,f2538])).

fof(f2538,plain,(
    ! [X2,X1] :
      ( k2_xboole_0(X1,k1_xboole_0) = X1
      | ~ r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f2490,f99])).

fof(f2490,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(X0,k1_xboole_0)
      | k2_xboole_0(X0,k1_xboole_0) = X0 ) ),
    inference(superposition,[],[f2435,f62])).

fof(f2435,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X14,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2434,f354])).

fof(f354,plain,(
    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f353,f139])).

fof(f139,plain,(
    ! [X2] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2) ),
    inference(superposition,[],[f124,f51])).

fof(f124,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1) ),
    inference(resolution,[],[f114,f61])).

fof(f114,plain,(
    ! [X4,X3] : r1_tarski(k4_xboole_0(k1_xboole_0,X3),X4) ),
    inference(backward_demodulation,[],[f105,f108])).

fof(f105,plain,(
    ! [X4,X2,X3] : r1_tarski(k4_xboole_0(k4_xboole_0(X2,X2),X3),X4) ),
    inference(resolution,[],[f103,f70])).

fof(f353,plain,(
    ! [X10,X11] : k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X11,X10)) ),
    inference(forward_demodulation,[],[f337,f139])).

fof(f337,plain,(
    ! [X10,X11] : k4_xboole_0(k1_xboole_0,k4_xboole_0(X11,X10)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X11),k1_xboole_0) ),
    inference(superposition,[],[f68,f113])).

fof(f113,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f104,f108])).

fof(f68,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f2434,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X14,k2_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f2395,f139])).

fof(f2395,plain,(
    ! [X14] : k4_xboole_0(X14,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X14,k2_xboole_0(k4_xboole_0(k1_xboole_0,sK0),k1_xboole_0)),k1_xboole_0) ),
    inference(superposition,[],[f332,f2333])).

fof(f2333,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),X1) ),
    inference(forward_demodulation,[],[f2317,f51])).

fof(f2317,plain,(
    ! [X1] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),X1) = k3_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),X1),k1_xboole_0) ),
    inference(resolution,[],[f2300,f61])).

fof(f2300,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK0),k1_xboole_0),X0),k1_xboole_0) ),
    inference(superposition,[],[f339,f2257])).

fof(f2257,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),k4_xboole_0(X1,sK0)) ),
    inference(forward_demodulation,[],[f2243,f51])).

fof(f2243,plain,(
    ! [X1] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),k4_xboole_0(X1,sK0)) = k3_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),k4_xboole_0(X1,sK0)),k1_xboole_0) ),
    inference(resolution,[],[f2210,f61])).

fof(f2210,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK0),k1_xboole_0),k4_xboole_0(X0,sK0)),k1_xboole_0) ),
    inference(resolution,[],[f2193,f70])).

fof(f2193,plain,(
    ! [X20] : r1_tarski(k2_xboole_0(k4_xboole_0(X20,sK0),k1_xboole_0),k2_xboole_0(k4_xboole_0(X20,sK0),k1_xboole_0)) ),
    inference(forward_demodulation,[],[f1745,f332])).

fof(f1745,plain,(
    ! [X20] : r1_tarski(k4_xboole_0(X20,k4_xboole_0(sK0,k1_xboole_0)),k4_xboole_0(X20,k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f339,f1561])).

fof(f1561,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1550,f429])).

fof(f429,plain,(
    r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(forward_demodulation,[],[f412,f108])).

fof(f412,plain,(
    r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0))) ),
    inference(superposition,[],[f97,f404])).

fof(f404,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0) ),
    inference(superposition,[],[f338,f139])).

fof(f338,plain,(
    ! [X12] : k4_xboole_0(sK0,k4_xboole_0(X12,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) = k2_xboole_0(k4_xboole_0(sK0,X12),sK0) ),
    inference(superposition,[],[f68,f167])).

fof(f167,plain,(
    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(resolution,[],[f53,f48])).

fof(f48,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ~ v5_funct_1(k1_xboole_0,sK0)
    & v1_funct_1(sK0)
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f36])).

fof(f36,plain,
    ( ? [X0] :
        ( ~ v5_funct_1(k1_xboole_0,X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
   => ( ~ v5_funct_1(k1_xboole_0,sK0)
      & v1_funct_1(sK0)
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0] :
      ( ~ v5_funct_1(k1_xboole_0,X0)
      & v1_funct_1(X0)
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0] :
        ( ( v1_funct_1(X0)
          & v1_relat_1(X0) )
       => v5_funct_1(k1_xboole_0,X0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => v5_funct_1(k1_xboole_0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f1550,plain,
    ( k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)
    | ~ r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f62,f1527])).

fof(f1527,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f1521,f51])).

fof(f1521,plain,(
    ! [X1] : k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(sK0,X1)) ),
    inference(forward_demodulation,[],[f1520,f402])).

fof(f402,plain,(
    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k1_xboole_0),k1_xboole_0)),sK0) ),
    inference(superposition,[],[f338,f242])).

fof(f242,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f241,f51])).

fof(f241,plain,(
    ! [X0] : k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0) = k3_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0),k1_xboole_0) ),
    inference(resolution,[],[f229,f61])).

fof(f229,plain,(
    ! [X0] : r1_tarski(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0),k1_xboole_0) ),
    inference(resolution,[],[f227,f70])).

fof(f227,plain,(
    ! [X7] : r1_tarski(k5_xboole_0(k5_xboole_0(X7,k1_xboole_0),k1_xboole_0),k2_xboole_0(X7,k1_xboole_0)) ),
    inference(superposition,[],[f178,f170])).

fof(f170,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0) ),
    inference(superposition,[],[f59,f51])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f178,plain,(
    ! [X12,X11] : r1_tarski(k5_xboole_0(X11,X12),k2_xboole_0(X11,X12)) ),
    inference(superposition,[],[f57,f59])).

fof(f1520,plain,(
    ! [X1] : k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k1_xboole_0),k1_xboole_0)),sK0),k3_xboole_0(sK0,X1)) ),
    inference(forward_demodulation,[],[f1504,f139])).

fof(f1504,plain,(
    ! [X1] : k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k1_xboole_0),k1_xboole_0)),sK0),k3_xboole_0(sK0,X1)) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X1)) ),
    inference(superposition,[],[f406,f242])).

fof(f406,plain,(
    ! [X2,X1] : k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X1),sK0),k3_xboole_0(sK0,X2)) ),
    inference(superposition,[],[f68,f338])).

fof(f339,plain,(
    ! [X2,X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f57,f68])).

fof(f332,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0) ),
    inference(superposition,[],[f68,f51])).

fof(f3004,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(forward_demodulation,[],[f2960,f139])).

fof(f2960,plain,(
    ! [X6,X7] : k4_xboole_0(X6,k4_xboole_0(k1_xboole_0,X7)) = k2_xboole_0(X6,k3_xboole_0(X6,X7)) ),
    inference(superposition,[],[f68,f2855])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

fof(f169,plain,(
    ! [X2,X3] : sK2(X2,X3) = k3_xboole_0(sK2(X2,X3),k2_zfmisc_1(X2,k2_relat_1(sK2(X2,X3)))) ),
    inference(forward_demodulation,[],[f168,f65])).

fof(f168,plain,(
    ! [X2,X3] : sK2(X2,X3) = k3_xboole_0(sK2(X2,X3),k2_zfmisc_1(k1_relat_1(sK2(X2,X3)),k2_relat_1(sK2(X2,X3)))) ),
    inference(resolution,[],[f53,f63])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X3] :
          ( k1_funct_1(sK2(X0,X1),X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(sK2(X0,X1)) = X0
      & v1_funct_1(sK2(X0,X1))
      & v1_relat_1(sK2(X0,X1)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f42])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ! [X3] :
              ( k1_funct_1(X2,X3) = X1
              | ~ r2_hidden(X3,X0) )
          & k1_relat_1(X2) = X0
          & v1_funct_1(X2)
          & v1_relat_1(X2) )
     => ( ! [X3] :
            ( k1_funct_1(sK2(X0,X1),X3) = X1
            | ~ r2_hidden(X3,X0) )
        & k1_relat_1(sK2(X0,X1)) = X0
        & v1_funct_1(sK2(X0,X1))
        & v1_relat_1(sK2(X0,X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( k1_funct_1(X2,X3) = X1
          | ~ r2_hidden(X3,X0) )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
    ? [X2] :
      ( ! [X3] :
          ( r2_hidden(X3,X0)
         => k1_funct_1(X2,X3) = X1 )
      & k1_relat_1(X2) = X0
      & v1_funct_1(X2)
      & v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).

fof(f65,plain,(
    ! [X0,X1] : k1_relat_1(sK2(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f43])).

fof(f3989,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3988,f48])).

fof(f3988,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f3987,f49])).

fof(f49,plain,(
    v1_funct_1(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f3987,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f924,f3980])).

fof(f3980,plain,(
    v1_funct_1(k1_xboole_0) ),
    inference(superposition,[],[f64,f3977])).

fof(f64,plain,(
    ! [X0,X1] : v1_funct_1(sK2(X0,X1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f924,plain,
    ( r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0))
    | ~ v1_funct_1(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK0)
    | ~ v1_relat_1(sK0) ),
    inference(resolution,[],[f55,f50])).

fof(f50,plain,(
    ~ v5_funct_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v5_funct_1(X1,X0)
      | r2_hidden(sK1(X0,X1),k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
                & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
          & r2_hidden(X2,k1_relat_1(X1)) )
     => ( ~ r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1)))
        & r2_hidden(sK1(X0,X1),k1_relat_1(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X3] :
                  ( r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3))
                  | ~ r2_hidden(X3,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v5_funct_1(X1,X0)
              | ? [X2] :
                  ( ~ r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  & r2_hidden(X2,k1_relat_1(X1)) ) )
            & ( ! [X2] :
                  ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                  | ~ r2_hidden(X2,k1_relat_1(X1)) )
              | ~ v5_funct_1(X1,X0) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))
                | ~ r2_hidden(X2,k1_relat_1(X1)) ) )
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( v5_funct_1(X1,X0)
          <=> ! [X2] :
                ( r2_hidden(X2,k1_relat_1(X1))
               => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).

fof(f3981,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[],[f63,f3977])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:38:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (6261)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.47  % (6278)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.48  % (6269)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.50  % (6286)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.51  % (6273)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (6263)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (6260)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.51  % (6266)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.52  % (6281)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (6262)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (6259)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (6282)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (6283)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (6267)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (6288)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.54  % (6264)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (6274)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (6285)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (6289)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.54  % (6268)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.55  % (6275)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.55  % (6280)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (6274)Refutation not found, incomplete strategy% (6274)------------------------------
% 0.21/0.55  % (6274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (6271)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.47/0.55  % (6281)Refutation not found, incomplete strategy% (6281)------------------------------
% 1.47/0.55  % (6281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (6281)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (6281)Memory used [KB]: 10746
% 1.47/0.55  % (6281)Time elapsed: 0.131 s
% 1.47/0.55  % (6281)------------------------------
% 1.47/0.55  % (6281)------------------------------
% 1.47/0.55  % (6274)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (6274)Memory used [KB]: 6140
% 1.47/0.55  % (6274)Time elapsed: 0.004 s
% 1.47/0.55  % (6274)------------------------------
% 1.47/0.55  % (6274)------------------------------
% 1.47/0.55  % (6265)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.47/0.55  % (6277)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.55  % (6279)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.47/0.55  % (6270)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.55  % (6272)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.47/0.56  % (6284)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.56  % (6276)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.47/0.56  % (6276)Refutation not found, incomplete strategy% (6276)------------------------------
% 1.47/0.56  % (6276)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (6276)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (6276)Memory used [KB]: 10618
% 1.47/0.56  % (6276)Time elapsed: 0.150 s
% 1.47/0.56  % (6276)------------------------------
% 1.47/0.56  % (6276)------------------------------
% 2.21/0.67  % (6373)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.21/0.67  % (6374)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.21/0.72  % (6386)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 3.00/0.77  % (6262)Refutation found. Thanks to Tanya!
% 3.00/0.77  % SZS status Theorem for theBenchmark
% 3.00/0.77  % SZS output start Proof for theBenchmark
% 3.00/0.78  fof(f3992,plain,(
% 3.00/0.78    $false),
% 3.00/0.78    inference(global_subsumption,[],[f3981,f3991])).
% 3.00/0.78  fof(f3991,plain,(
% 3.00/0.78    ~v1_relat_1(k1_xboole_0)),
% 3.00/0.78    inference(subsumption_resolution,[],[f3990,f269])).
% 3.00/0.78  fof(f269,plain,(
% 3.00/0.78    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 3.00/0.78    inference(superposition,[],[f85,f108])).
% 3.00/0.78  fof(f108,plain,(
% 3.00/0.78    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(X2,X2)) )),
% 3.00/0.78    inference(superposition,[],[f104,f51])).
% 3.00/0.78  fof(f51,plain,(
% 3.00/0.78    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.00/0.78    inference(cnf_transformation,[],[f4])).
% 3.00/0.78  fof(f4,axiom,(
% 3.00/0.78    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.00/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 3.00/0.78  fof(f104,plain,(
% 3.00/0.78    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k3_xboole_0(k4_xboole_0(X0,X0),X1)) )),
% 3.00/0.78    inference(resolution,[],[f103,f61])).
% 3.00/0.78  fof(f61,plain,(
% 3.00/0.78    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 3.00/0.78    inference(cnf_transformation,[],[f29])).
% 3.00/0.78  fof(f29,plain,(
% 3.00/0.78    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.00/0.78    inference(ennf_transformation,[],[f3])).
% 3.00/0.78  fof(f3,axiom,(
% 3.00/0.78    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.00/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.00/0.78  fof(f103,plain,(
% 3.00/0.78    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X0),X1)) )),
% 3.00/0.78    inference(resolution,[],[f70,f57])).
% 3.00/0.78  fof(f57,plain,(
% 3.00/0.78    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.00/0.78    inference(cnf_transformation,[],[f8])).
% 3.00/0.78  fof(f8,axiom,(
% 3.00/0.78    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.00/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.00/0.78  fof(f70,plain,(
% 3.00/0.78    ( ! [X2,X0,X1] : (~r1_tarski(X0,k2_xboole_0(X1,X2)) | r1_tarski(k4_xboole_0(X0,X1),X2)) )),
% 3.00/0.78    inference(cnf_transformation,[],[f32])).
% 3.00/0.78  fof(f32,plain,(
% 3.00/0.78    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 3.00/0.78    inference(ennf_transformation,[],[f5])).
% 3.00/0.78  fof(f5,axiom,(
% 3.00/0.78    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) => r1_tarski(k4_xboole_0(X0,X1),X2))),
% 3.00/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).
% 3.00/0.78  fof(f85,plain,(
% 3.00/0.78    ( ! [X2,X1] : (~r2_hidden(X2,k4_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2))))) )),
% 3.00/0.78    inference(equality_resolution,[],[f83])).
% 3.00/0.78  fof(f83,plain,(
% 3.00/0.78    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k2_xboole_0(k2_tarski(X2,X2),k2_tarski(X2,X2))))) )),
% 3.00/0.78    inference(definition_unfolding,[],[f75,f81])).
% 3.00/0.78  fof(f81,plain,(
% 3.00/0.78    ( ! [X0] : (k1_tarski(X0) = k2_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X0))) )),
% 3.00/0.78    inference(definition_unfolding,[],[f52,f67])).
% 3.00/0.78  fof(f67,plain,(
% 3.00/0.78    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 3.00/0.78    inference(cnf_transformation,[],[f13])).
% 3.00/0.78  fof(f13,axiom,(
% 3.00/0.78    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 3.00/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 3.00/0.78  fof(f52,plain,(
% 3.00/0.78    ( ! [X0] : (k1_enumset1(X0,X0,X0) = k1_tarski(X0)) )),
% 3.00/0.78    inference(cnf_transformation,[],[f14])).
% 3.00/0.78  fof(f14,axiom,(
% 3.00/0.78    ! [X0] : k1_enumset1(X0,X0,X0) = k1_tarski(X0)),
% 3.00/0.78    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).
% 3.00/0.78  fof(f75,plain,(
% 3.00/0.78    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 3.00/0.78    inference(cnf_transformation,[],[f47])).
% 3.00/0.78  fof(f47,plain,(
% 3.00/0.78    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | X0 = X2 | ~r2_hidden(X0,X1)) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.00/0.78    inference(flattening,[],[f46])).
% 3.00/0.78  fof(f46,plain,(
% 3.00/0.78    ! [X0,X1,X2] : ((r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) | (X0 = X2 | ~r2_hidden(X0,X1))) & ((X0 != X2 & r2_hidden(X0,X1)) | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))))),
% 3.00/0.78    inference(nnf_transformation,[],[f16])).
% 3.00/0.80  fof(f16,axiom,(
% 3.00/0.80    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 3.00/0.80  fof(f3990,plain,(
% 3.00/0.80    r2_hidden(sK1(sK0,k1_xboole_0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)),
% 3.00/0.80    inference(forward_demodulation,[],[f3989,f3979])).
% 3.00/0.80  fof(f3979,plain,(
% 3.00/0.80    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.00/0.80    inference(superposition,[],[f65,f3977])).
% 3.00/0.80  fof(f3977,plain,(
% 3.00/0.80    ( ! [X12] : (k1_xboole_0 = sK2(k1_xboole_0,X12)) )),
% 3.00/0.80    inference(forward_demodulation,[],[f3976,f51])).
% 3.00/0.80  fof(f3976,plain,(
% 3.00/0.80    ( ! [X12] : (sK2(k1_xboole_0,X12) = k3_xboole_0(sK2(k1_xboole_0,X12),k1_xboole_0)) )),
% 3.00/0.80    inference(superposition,[],[f169,f3965])).
% 3.00/0.80  fof(f3965,plain,(
% 3.00/0.80    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 3.00/0.80    inference(resolution,[],[f3603,f162])).
% 3.00/0.80  fof(f162,plain,(
% 3.00/0.80    ( ! [X1] : (r1_xboole_0(k1_xboole_0,X1)) )),
% 3.00/0.80    inference(superposition,[],[f160,f96])).
% 3.00/0.80  fof(f96,plain,(
% 3.00/0.80    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 3.00/0.80    inference(resolution,[],[f61,f57])).
% 3.00/0.80  fof(f160,plain,(
% 3.00/0.80    ( ! [X0,X1] : (r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))) )),
% 3.00/0.80    inference(resolution,[],[f72,f115])).
% 3.00/0.80  fof(f115,plain,(
% 3.00/0.80    ( ! [X1] : (r1_tarski(k1_xboole_0,X1)) )),
% 3.00/0.80    inference(backward_demodulation,[],[f103,f108])).
% 3.00/0.80  fof(f72,plain,(
% 3.00/0.80    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,X2)) | r1_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 3.00/0.80    inference(cnf_transformation,[],[f45])).
% 3.00/0.80  fof(f45,plain,(
% 3.00/0.80    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | ~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 3.00/0.80    inference(flattening,[],[f44])).
% 3.00/0.80  fof(f44,plain,(
% 3.00/0.80    ! [X0,X1,X2] : ((r1_tarski(X0,k5_xboole_0(X1,X2)) | (~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,k2_xboole_0(X1,X2)))) & ((r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))) | ~r1_tarski(X0,k5_xboole_0(X1,X2))))),
% 3.00/0.80    inference(nnf_transformation,[],[f1])).
% 3.00/0.80  fof(f1,axiom,(
% 3.00/0.80    ! [X0,X1,X2] : (r1_tarski(X0,k5_xboole_0(X1,X2)) <=> (r1_xboole_0(X0,k3_xboole_0(X1,X2)) & r1_tarski(X0,k2_xboole_0(X1,X2))))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_xboole_1)).
% 3.00/0.80  fof(f3603,plain,(
% 3.00/0.80    ( ! [X6,X7] : (~r1_xboole_0(X6,X6) | k1_xboole_0 = k2_zfmisc_1(X6,X7)) )),
% 3.00/0.80    inference(resolution,[],[f3587,f79])).
% 3.00/0.80  fof(f79,plain,(
% 3.00/0.80    ( ! [X2,X0,X3,X1] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | ~r1_xboole_0(X0,X1)) )),
% 3.00/0.80    inference(cnf_transformation,[],[f35])).
% 3.00/0.80  fof(f35,plain,(
% 3.00/0.80    ! [X0,X1,X2,X3] : (r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) | (~r1_xboole_0(X2,X3) & ~r1_xboole_0(X0,X1)))),
% 3.00/0.80    inference(ennf_transformation,[],[f15])).
% 3.00/0.80  fof(f15,axiom,(
% 3.00/0.80    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) | r1_xboole_0(X0,X1)) => r1_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t127_zfmisc_1)).
% 3.00/0.80  fof(f3587,plain,(
% 3.00/0.80    ( ! [X1] : (~r1_xboole_0(X1,X1) | k1_xboole_0 = X1) )),
% 3.00/0.80    inference(forward_demodulation,[],[f3572,f108])).
% 3.00/0.80  fof(f3572,plain,(
% 3.00/0.80    ( ! [X1] : (k4_xboole_0(X1,X1) = X1 | ~r1_xboole_0(X1,X1)) )),
% 3.00/0.80    inference(superposition,[],[f62,f3537])).
% 3.00/0.80  fof(f3537,plain,(
% 3.00/0.80    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) )),
% 3.00/0.80    inference(superposition,[],[f3005,f96])).
% 3.00/0.80  fof(f3005,plain,(
% 3.00/0.80    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6) )),
% 3.00/0.80    inference(forward_demodulation,[],[f3004,f2855])).
% 3.00/0.80  fof(f2855,plain,(
% 3.00/0.80    ( ! [X20] : (k4_xboole_0(X20,k1_xboole_0) = X20) )),
% 3.00/0.80    inference(resolution,[],[f2697,f97])).
% 3.00/0.80  fof(f97,plain,(
% 3.00/0.80    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1)))) )),
% 3.00/0.80    inference(superposition,[],[f58,f96])).
% 3.00/0.80  fof(f58,plain,(
% 3.00/0.80    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 3.00/0.80    inference(cnf_transformation,[],[f11])).
% 3.00/0.80  fof(f11,axiom,(
% 3.00/0.80    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_xboole_1)).
% 3.00/0.80  fof(f2697,plain,(
% 3.00/0.80    ( ! [X2,X1] : (~r1_xboole_0(X1,X2) | k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 3.00/0.80    inference(resolution,[],[f2599,f99])).
% 3.00/0.80  fof(f99,plain,(
% 3.00/0.80    ( ! [X0,X1] : (r1_xboole_0(X1,k1_xboole_0) | ~r1_xboole_0(X1,X0)) )),
% 3.00/0.80    inference(superposition,[],[f78,f51])).
% 3.00/0.80  fof(f78,plain,(
% 3.00/0.80    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 3.00/0.80    inference(cnf_transformation,[],[f34])).
% 3.00/0.80  fof(f34,plain,(
% 3.00/0.80    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 3.00/0.80    inference(ennf_transformation,[],[f7])).
% 3.00/0.80  fof(f7,axiom,(
% 3.00/0.80    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 3.00/0.80  fof(f2599,plain,(
% 3.00/0.80    ( ! [X4] : (~r1_xboole_0(X4,k1_xboole_0) | k4_xboole_0(X4,k1_xboole_0) = X4) )),
% 3.00/0.80    inference(condensation,[],[f2573])).
% 3.00/0.80  fof(f2573,plain,(
% 3.00/0.80    ( ! [X4,X5] : (k4_xboole_0(X4,k1_xboole_0) = X4 | ~r1_xboole_0(X4,k1_xboole_0) | ~r1_xboole_0(X4,X5)) )),
% 3.00/0.80    inference(superposition,[],[f62,f2538])).
% 3.00/0.80  fof(f2538,plain,(
% 3.00/0.80    ( ! [X2,X1] : (k2_xboole_0(X1,k1_xboole_0) = X1 | ~r1_xboole_0(X1,X2)) )),
% 3.00/0.80    inference(resolution,[],[f2490,f99])).
% 3.00/0.80  fof(f2490,plain,(
% 3.00/0.80    ( ! [X0] : (~r1_xboole_0(X0,k1_xboole_0) | k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.00/0.80    inference(superposition,[],[f2435,f62])).
% 3.00/0.80  fof(f2435,plain,(
% 3.00/0.80    ( ! [X14] : (k4_xboole_0(X14,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X14,k1_xboole_0),k1_xboole_0)) )),
% 3.00/0.80    inference(forward_demodulation,[],[f2434,f354])).
% 3.00/0.80  fof(f354,plain,(
% 3.00/0.80    k1_xboole_0 = k2_xboole_0(k1_xboole_0,k1_xboole_0)),
% 3.00/0.80    inference(forward_demodulation,[],[f353,f139])).
% 3.00/0.80  fof(f139,plain,(
% 3.00/0.80    ( ! [X2] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X2)) )),
% 3.00/0.80    inference(superposition,[],[f124,f51])).
% 3.00/0.80  fof(f124,plain,(
% 3.00/0.80    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,X0) = k3_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) )),
% 3.00/0.80    inference(resolution,[],[f114,f61])).
% 3.00/0.80  fof(f114,plain,(
% 3.00/0.80    ( ! [X4,X3] : (r1_tarski(k4_xboole_0(k1_xboole_0,X3),X4)) )),
% 3.00/0.80    inference(backward_demodulation,[],[f105,f108])).
% 3.00/0.80  fof(f105,plain,(
% 3.00/0.80    ( ! [X4,X2,X3] : (r1_tarski(k4_xboole_0(k4_xboole_0(X2,X2),X3),X4)) )),
% 3.00/0.80    inference(resolution,[],[f103,f70])).
% 3.00/0.80  fof(f353,plain,(
% 3.00/0.80    ( ! [X10,X11] : (k2_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(X11,X10))) )),
% 3.00/0.80    inference(forward_demodulation,[],[f337,f139])).
% 3.00/0.80  fof(f337,plain,(
% 3.00/0.80    ( ! [X10,X11] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(X11,X10)) = k2_xboole_0(k4_xboole_0(k1_xboole_0,X11),k1_xboole_0)) )),
% 3.00/0.80    inference(superposition,[],[f68,f113])).
% 3.00/0.80  fof(f113,plain,(
% 3.00/0.80    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X1)) )),
% 3.00/0.80    inference(backward_demodulation,[],[f104,f108])).
% 3.00/0.80  fof(f68,plain,(
% 3.00/0.80    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 3.00/0.80    inference(cnf_transformation,[],[f6])).
% 3.00/0.80  fof(f6,axiom,(
% 3.00/0.80    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).
% 3.00/0.80  fof(f2434,plain,(
% 3.00/0.80    ( ! [X14] : (k4_xboole_0(X14,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X14,k2_xboole_0(k1_xboole_0,k1_xboole_0)),k1_xboole_0)) )),
% 3.00/0.80    inference(forward_demodulation,[],[f2395,f139])).
% 3.00/0.80  fof(f2395,plain,(
% 3.00/0.80    ( ! [X14] : (k4_xboole_0(X14,k1_xboole_0) = k2_xboole_0(k4_xboole_0(X14,k2_xboole_0(k4_xboole_0(k1_xboole_0,sK0),k1_xboole_0)),k1_xboole_0)) )),
% 3.00/0.80    inference(superposition,[],[f332,f2333])).
% 3.00/0.80  fof(f2333,plain,(
% 3.00/0.80    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),X1)) )),
% 3.00/0.80    inference(forward_demodulation,[],[f2317,f51])).
% 3.00/0.80  fof(f2317,plain,(
% 3.00/0.80    ( ! [X1] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),X1) = k3_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),X1),k1_xboole_0)) )),
% 3.00/0.80    inference(resolution,[],[f2300,f61])).
% 3.00/0.80  fof(f2300,plain,(
% 3.00/0.80    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK0),k1_xboole_0),X0),k1_xboole_0)) )),
% 3.00/0.80    inference(superposition,[],[f339,f2257])).
% 3.00/0.80  fof(f2257,plain,(
% 3.00/0.80    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),k4_xboole_0(X1,sK0))) )),
% 3.00/0.80    inference(forward_demodulation,[],[f2243,f51])).
% 3.00/0.80  fof(f2243,plain,(
% 3.00/0.80    ( ! [X1] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),k4_xboole_0(X1,sK0)) = k3_xboole_0(k4_xboole_0(k2_xboole_0(k4_xboole_0(X1,sK0),k1_xboole_0),k4_xboole_0(X1,sK0)),k1_xboole_0)) )),
% 3.00/0.80    inference(resolution,[],[f2210,f61])).
% 3.00/0.80  fof(f2210,plain,(
% 3.00/0.80    ( ! [X0] : (r1_tarski(k4_xboole_0(k2_xboole_0(k4_xboole_0(X0,sK0),k1_xboole_0),k4_xboole_0(X0,sK0)),k1_xboole_0)) )),
% 3.00/0.80    inference(resolution,[],[f2193,f70])).
% 3.00/0.80  fof(f2193,plain,(
% 3.00/0.80    ( ! [X20] : (r1_tarski(k2_xboole_0(k4_xboole_0(X20,sK0),k1_xboole_0),k2_xboole_0(k4_xboole_0(X20,sK0),k1_xboole_0))) )),
% 3.00/0.80    inference(forward_demodulation,[],[f1745,f332])).
% 3.00/0.80  fof(f1745,plain,(
% 3.00/0.80    ( ! [X20] : (r1_tarski(k4_xboole_0(X20,k4_xboole_0(sK0,k1_xboole_0)),k4_xboole_0(X20,k4_xboole_0(sK0,k1_xboole_0)))) )),
% 3.00/0.80    inference(superposition,[],[f339,f1561])).
% 3.00/0.80  fof(f1561,plain,(
% 3.00/0.80    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)),
% 3.00/0.80    inference(subsumption_resolution,[],[f1550,f429])).
% 3.00/0.80  fof(f429,plain,(
% 3.00/0.80    r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)),
% 3.00/0.80    inference(forward_demodulation,[],[f412,f108])).
% 3.00/0.80  fof(f412,plain,(
% 3.00/0.80    r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(sK0,k1_xboole_0)))),
% 3.00/0.80    inference(superposition,[],[f97,f404])).
% 3.00/0.80  fof(f404,plain,(
% 3.00/0.80    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),sK0)),
% 3.00/0.80    inference(superposition,[],[f338,f139])).
% 3.00/0.80  fof(f338,plain,(
% 3.00/0.80    ( ! [X12] : (k4_xboole_0(sK0,k4_xboole_0(X12,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))) = k2_xboole_0(k4_xboole_0(sK0,X12),sK0)) )),
% 3.00/0.80    inference(superposition,[],[f68,f167])).
% 3.00/0.80  fof(f167,plain,(
% 3.00/0.80    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 3.00/0.80    inference(resolution,[],[f53,f48])).
% 3.00/0.80  fof(f48,plain,(
% 3.00/0.80    v1_relat_1(sK0)),
% 3.00/0.80    inference(cnf_transformation,[],[f37])).
% 3.00/0.80  fof(f37,plain,(
% 3.00/0.80    ~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0)),
% 3.00/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f24,f36])).
% 3.00/0.80  fof(f36,plain,(
% 3.00/0.80    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (~v5_funct_1(k1_xboole_0,sK0) & v1_funct_1(sK0) & v1_relat_1(sK0))),
% 3.00/0.80    introduced(choice_axiom,[])).
% 3.00/0.80  fof(f24,plain,(
% 3.00/0.80    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & v1_funct_1(X0) & v1_relat_1(X0))),
% 3.00/0.80    inference(flattening,[],[f23])).
% 3.00/0.80  fof(f23,plain,(
% 3.00/0.80    ? [X0] : (~v5_funct_1(k1_xboole_0,X0) & (v1_funct_1(X0) & v1_relat_1(X0)))),
% 3.00/0.80    inference(ennf_transformation,[],[f22])).
% 3.00/0.80  fof(f22,negated_conjecture,(
% 3.00/0.80    ~! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 3.00/0.80    inference(negated_conjecture,[],[f21])).
% 3.00/0.80  fof(f21,conjecture,(
% 3.00/0.80    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => v5_funct_1(k1_xboole_0,X0))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_funct_1)).
% 3.00/0.80  fof(f53,plain,(
% 3.00/0.80    ( ! [X0] : (~v1_relat_1(X0) | k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0) )),
% 3.00/0.80    inference(cnf_transformation,[],[f25])).
% 3.00/0.80  fof(f25,plain,(
% 3.00/0.80    ! [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 3.00/0.80    inference(ennf_transformation,[],[f18])).
% 3.00/0.80  fof(f18,axiom,(
% 3.00/0.80    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 3.00/0.80  fof(f1550,plain,(
% 3.00/0.80    k4_xboole_0(sK0,k1_xboole_0) = k4_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0) | ~r1_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)),
% 3.00/0.80    inference(superposition,[],[f62,f1527])).
% 3.00/0.80  fof(f1527,plain,(
% 3.00/0.80    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k1_xboole_0)),
% 3.00/0.80    inference(superposition,[],[f1521,f51])).
% 3.00/0.80  fof(f1521,plain,(
% 3.00/0.80    ( ! [X1] : (k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k1_xboole_0),k3_xboole_0(sK0,X1))) )),
% 3.00/0.80    inference(forward_demodulation,[],[f1520,f402])).
% 3.00/0.80  fof(f402,plain,(
% 3.00/0.80    k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k1_xboole_0),k1_xboole_0)),sK0)),
% 3.00/0.80    inference(superposition,[],[f338,f242])).
% 3.00/0.80  fof(f242,plain,(
% 3.00/0.80    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0)) )),
% 3.00/0.80    inference(forward_demodulation,[],[f241,f51])).
% 3.00/0.80  fof(f241,plain,(
% 3.00/0.80    ( ! [X0] : (k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0) = k3_xboole_0(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0),k1_xboole_0)) )),
% 3.00/0.80    inference(resolution,[],[f229,f61])).
% 3.00/0.80  fof(f229,plain,(
% 3.00/0.80    ( ! [X0] : (r1_tarski(k4_xboole_0(k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0),X0),k1_xboole_0)) )),
% 3.00/0.80    inference(resolution,[],[f227,f70])).
% 3.00/0.80  fof(f227,plain,(
% 3.00/0.80    ( ! [X7] : (r1_tarski(k5_xboole_0(k5_xboole_0(X7,k1_xboole_0),k1_xboole_0),k2_xboole_0(X7,k1_xboole_0))) )),
% 3.00/0.80    inference(superposition,[],[f178,f170])).
% 3.00/0.80  fof(f170,plain,(
% 3.00/0.80    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k2_xboole_0(k5_xboole_0(X0,k1_xboole_0),k1_xboole_0)) )),
% 3.00/0.80    inference(superposition,[],[f59,f51])).
% 3.00/0.80  fof(f59,plain,(
% 3.00/0.80    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 3.00/0.80    inference(cnf_transformation,[],[f12])).
% 3.00/0.80  fof(f12,axiom,(
% 3.00/0.80    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 3.00/0.80  fof(f178,plain,(
% 3.00/0.80    ( ! [X12,X11] : (r1_tarski(k5_xboole_0(X11,X12),k2_xboole_0(X11,X12))) )),
% 3.00/0.80    inference(superposition,[],[f57,f59])).
% 3.00/0.80  fof(f1520,plain,(
% 3.00/0.80    ( ! [X1] : (k4_xboole_0(sK0,k1_xboole_0) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k1_xboole_0),k1_xboole_0)),sK0),k3_xboole_0(sK0,X1))) )),
% 3.00/0.80    inference(forward_demodulation,[],[f1504,f139])).
% 3.00/0.80  fof(f1504,plain,(
% 3.00/0.80    ( ! [X1] : (k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)),k1_xboole_0),k1_xboole_0)),sK0),k3_xboole_0(sK0,X1)) = k4_xboole_0(sK0,k4_xboole_0(k1_xboole_0,X1))) )),
% 3.00/0.80    inference(superposition,[],[f406,f242])).
% 3.00/0.80  fof(f406,plain,(
% 3.00/0.80    ( ! [X2,X1] : (k4_xboole_0(sK0,k4_xboole_0(k4_xboole_0(X1,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))),X2)) = k2_xboole_0(k2_xboole_0(k4_xboole_0(sK0,X1),sK0),k3_xboole_0(sK0,X2))) )),
% 3.00/0.80    inference(superposition,[],[f68,f338])).
% 3.00/0.80  fof(f339,plain,(
% 3.00/0.80    ( ! [X2,X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X1,X2)))) )),
% 3.00/0.80    inference(superposition,[],[f57,f68])).
% 3.00/0.80  fof(f332,plain,(
% 3.00/0.80    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,k1_xboole_0)) = k2_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) )),
% 3.00/0.80    inference(superposition,[],[f68,f51])).
% 3.00/0.80  fof(f3004,plain,(
% 3.00/0.80    ( ! [X6,X7] : (k4_xboole_0(X6,k1_xboole_0) = k2_xboole_0(X6,k3_xboole_0(X6,X7))) )),
% 3.00/0.80    inference(forward_demodulation,[],[f2960,f139])).
% 3.00/0.80  fof(f2960,plain,(
% 3.00/0.80    ( ! [X6,X7] : (k4_xboole_0(X6,k4_xboole_0(k1_xboole_0,X7)) = k2_xboole_0(X6,k3_xboole_0(X6,X7))) )),
% 3.00/0.80    inference(superposition,[],[f68,f2855])).
% 3.00/0.80  fof(f62,plain,(
% 3.00/0.80    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 3.00/0.80    inference(cnf_transformation,[],[f30])).
% 3.00/0.80  fof(f30,plain,(
% 3.00/0.80    ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 | ~r1_xboole_0(X0,X1))),
% 3.00/0.80    inference(ennf_transformation,[],[f10])).
% 3.00/0.80  fof(f10,axiom,(
% 3.00/0.80    ! [X0,X1] : (r1_xboole_0(X0,X1) => k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0)),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).
% 3.00/0.80  fof(f169,plain,(
% 3.00/0.80    ( ! [X2,X3] : (sK2(X2,X3) = k3_xboole_0(sK2(X2,X3),k2_zfmisc_1(X2,k2_relat_1(sK2(X2,X3))))) )),
% 3.00/0.80    inference(forward_demodulation,[],[f168,f65])).
% 3.00/0.80  fof(f168,plain,(
% 3.00/0.80    ( ! [X2,X3] : (sK2(X2,X3) = k3_xboole_0(sK2(X2,X3),k2_zfmisc_1(k1_relat_1(sK2(X2,X3)),k2_relat_1(sK2(X2,X3))))) )),
% 3.00/0.80    inference(resolution,[],[f53,f63])).
% 3.00/0.80  fof(f63,plain,(
% 3.00/0.80    ( ! [X0,X1] : (v1_relat_1(sK2(X0,X1))) )),
% 3.00/0.80    inference(cnf_transformation,[],[f43])).
% 3.00/0.80  fof(f43,plain,(
% 3.00/0.80    ! [X0,X1] : (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1)))),
% 3.00/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f31,f42])).
% 3.00/0.80  fof(f42,plain,(
% 3.00/0.80    ! [X1,X0] : (? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2)) => (! [X3] : (k1_funct_1(sK2(X0,X1),X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(sK2(X0,X1)) = X0 & v1_funct_1(sK2(X0,X1)) & v1_relat_1(sK2(X0,X1))))),
% 3.00/0.80    introduced(choice_axiom,[])).
% 3.00/0.80  fof(f31,plain,(
% 3.00/0.80    ! [X0,X1] : ? [X2] : (! [X3] : (k1_funct_1(X2,X3) = X1 | ~r2_hidden(X3,X0)) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.00/0.80    inference(ennf_transformation,[],[f20])).
% 3.00/0.80  fof(f20,axiom,(
% 3.00/0.80    ! [X0,X1] : ? [X2] : (! [X3] : (r2_hidden(X3,X0) => k1_funct_1(X2,X3) = X1) & k1_relat_1(X2) = X0 & v1_funct_1(X2) & v1_relat_1(X2))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',s3_funct_1__e2_24__funct_1)).
% 3.00/0.80  fof(f65,plain,(
% 3.00/0.80    ( ! [X0,X1] : (k1_relat_1(sK2(X0,X1)) = X0) )),
% 3.00/0.80    inference(cnf_transformation,[],[f43])).
% 3.00/0.80  fof(f3989,plain,(
% 3.00/0.80    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0)),
% 3.00/0.80    inference(subsumption_resolution,[],[f3988,f48])).
% 3.00/0.80  fof(f3988,plain,(
% 3.00/0.80    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(sK0)),
% 3.00/0.80    inference(subsumption_resolution,[],[f3987,f49])).
% 3.00/0.80  fof(f49,plain,(
% 3.00/0.80    v1_funct_1(sK0)),
% 3.00/0.80    inference(cnf_transformation,[],[f37])).
% 3.00/0.80  fof(f3987,plain,(
% 3.00/0.80    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 3.00/0.80    inference(subsumption_resolution,[],[f924,f3980])).
% 3.00/0.80  fof(f3980,plain,(
% 3.00/0.80    v1_funct_1(k1_xboole_0)),
% 3.00/0.80    inference(superposition,[],[f64,f3977])).
% 3.00/0.80  fof(f64,plain,(
% 3.00/0.80    ( ! [X0,X1] : (v1_funct_1(sK2(X0,X1))) )),
% 3.00/0.80    inference(cnf_transformation,[],[f43])).
% 3.00/0.80  fof(f924,plain,(
% 3.00/0.80    r2_hidden(sK1(sK0,k1_xboole_0),k1_relat_1(k1_xboole_0)) | ~v1_funct_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_funct_1(sK0) | ~v1_relat_1(sK0)),
% 3.00/0.80    inference(resolution,[],[f55,f50])).
% 3.00/0.80  fof(f50,plain,(
% 3.00/0.80    ~v5_funct_1(k1_xboole_0,sK0)),
% 3.00/0.80    inference(cnf_transformation,[],[f37])).
% 3.00/0.80  fof(f55,plain,(
% 3.00/0.80    ( ! [X0,X1] : (v5_funct_1(X1,X0) | r2_hidden(sK1(X0,X1),k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.00/0.80    inference(cnf_transformation,[],[f41])).
% 3.00/0.80  fof(f41,plain,(
% 3.00/0.80    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.80    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f39,f40])).
% 3.00/0.80  fof(f40,plain,(
% 3.00/0.80    ! [X1,X0] : (? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1))) => (~r2_hidden(k1_funct_1(X1,sK1(X0,X1)),k1_funct_1(X0,sK1(X0,X1))) & r2_hidden(sK1(X0,X1),k1_relat_1(X1))))),
% 3.00/0.80    introduced(choice_axiom,[])).
% 3.00/0.80  fof(f39,plain,(
% 3.00/0.80    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X3] : (r2_hidden(k1_funct_1(X1,X3),k1_funct_1(X0,X3)) | ~r2_hidden(X3,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.80    inference(rectify,[],[f38])).
% 3.00/0.80  fof(f38,plain,(
% 3.00/0.80    ! [X0] : (! [X1] : (((v5_funct_1(X1,X0) | ? [X2] : (~r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) & r2_hidden(X2,k1_relat_1(X1)))) & (! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v5_funct_1(X1,X0))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.80    inference(nnf_transformation,[],[f27])).
% 3.00/0.80  fof(f27,plain,(
% 3.00/0.80    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.00/0.80    inference(flattening,[],[f26])).
% 3.00/0.80  fof(f26,plain,(
% 3.00/0.80    ! [X0] : (! [X1] : ((v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2)) | ~r2_hidden(X2,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.00/0.80    inference(ennf_transformation,[],[f19])).
% 3.00/0.80  fof(f19,axiom,(
% 3.00/0.80    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v5_funct_1(X1,X0) <=> ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),k1_funct_1(X0,X2))))))),
% 3.00/0.80    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_funct_1)).
% 3.00/0.80  fof(f3981,plain,(
% 3.00/0.80    v1_relat_1(k1_xboole_0)),
% 3.00/0.80    inference(superposition,[],[f63,f3977])).
% 3.00/0.80  % SZS output end Proof for theBenchmark
% 3.00/0.80  % (6262)------------------------------
% 3.00/0.80  % (6262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.00/0.80  % (6262)Termination reason: Refutation
% 3.00/0.80  
% 3.00/0.80  % (6262)Memory used [KB]: 14072
% 3.00/0.80  % (6262)Time elapsed: 0.364 s
% 3.00/0.80  % (6262)------------------------------
% 3.00/0.80  % (6262)------------------------------
% 3.00/0.80  % (6258)Success in time 0.439 s
%------------------------------------------------------------------------------
