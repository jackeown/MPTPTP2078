%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:35 EST 2020

% Result     : Theorem 4.34s
% Output     : Refutation 4.87s
% Verified   : 
% Statistics : Number of formulae       :  120 (3442 expanded)
%              Number of leaves         :   15 ( 931 expanded)
%              Depth                    :   41
%              Number of atoms          :  262 (9104 expanded)
%              Number of equality atoms :  175 (7349 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4670,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4669,f4285])).

fof(f4285,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f4024])).

fof(f4024,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f46,f4022])).

fof(f4022,plain,(
    sK0 = sK2 ),
    inference(subsumption_resolution,[],[f3972,f48])).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f3972,plain,
    ( k1_xboole_0 != k5_xboole_0(sK2,sK2)
    | sK0 = sK2 ),
    inference(backward_demodulation,[],[f3864,f3892])).

fof(f3892,plain,(
    sK2 = k3_xboole_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f3883,f45])).

fof(f45,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] :
        ( ( X1 != X3
          | X0 != X2 )
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) )
   => ( ( sK1 != sK3
        | sK0 != sK2 )
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f3883,plain,
    ( k1_xboole_0 = sK1
    | sK2 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f3558,f265])).

fof(f265,plain,(
    ! [X12,X13,X11] :
      ( ~ r1_tarski(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X13,X12))
      | k1_xboole_0 = X12
      | k3_xboole_0(X11,X13) = X11 ) ),
    inference(resolution,[],[f73,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f3558,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3549,f48])).

fof(f3549,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f1197,f2525])).

fof(f2525,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f2524,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2524,plain,
    ( sK1 = k3_xboole_0(sK1,sK3)
    | ~ r1_tarski(k3_xboole_0(sK1,sK3),sK1) ),
    inference(subsumption_resolution,[],[f2515,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f34])).

fof(f2515,plain,
    ( k1_xboole_0 = sK0
    | sK1 = k3_xboole_0(sK1,sK3)
    | ~ r1_tarski(k3_xboole_0(sK1,sK3),sK1) ),
    inference(resolution,[],[f2478,f293])).

fof(f293,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(k2_zfmisc_1(X8,X9),k2_zfmisc_1(X8,X10))
      | k1_xboole_0 = X8
      | X9 = X10
      | ~ r1_tarski(X10,X9) ) ),
    inference(resolution,[],[f74,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X1,X2)
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f2478,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f2451,f50])).

fof(f50,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f2451,plain,(
    ! [X3] : r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(sK1,X3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f2450,f314])).

fof(f314,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5)) ),
    inference(superposition,[],[f75,f50])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f2450,plain,(
    ! [X3] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f2449,f43])).

fof(f43,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f2449,plain,(
    ! [X3] : r1_tarski(k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f2402,f75])).

fof(f2402,plain,(
    ! [X3] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,sK0),k3_xboole_0(sK3,X3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f113,f2349])).

fof(f2349,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f854,f314])).

fof(f854,plain,(
    ! [X9] : k2_zfmisc_1(k3_xboole_0(sK2,X9),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK3)) ),
    inference(superposition,[],[f321,f43])).

fof(f321,plain,(
    ! [X4,X5,X3] : k3_xboole_0(k2_zfmisc_1(X4,X3),k2_zfmisc_1(X5,X3)) = k2_zfmisc_1(k3_xboole_0(X4,X5),X3) ),
    inference(superposition,[],[f75,f50])).

fof(f113,plain,(
    ! [X4,X2,X3] : r1_tarski(k2_zfmisc_1(X2,k3_xboole_0(X3,X4)),k2_zfmisc_1(X2,X3)) ),
    inference(resolution,[],[f69,f51])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f1197,plain,(
    ! [X9] :
      ( k1_xboole_0 != k5_xboole_0(X9,k3_xboole_0(X9,sK3))
      | r1_tarski(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1)) ) ),
    inference(superposition,[],[f195,f43])).

fof(f195,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(resolution,[],[f82,f69])).

fof(f82,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f62,f54])).

fof(f54,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f3864,plain,
    ( sK0 = sK2
    | k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f3572,f82])).

fof(f3572,plain,
    ( ~ r1_tarski(sK2,sK0)
    | sK0 = sK2 ),
    inference(trivial_inequality_removal,[],[f3561])).

fof(f3561,plain,
    ( k1_xboole_0 != k1_xboole_0
    | sK0 = sK2
    | ~ r1_tarski(sK2,sK0) ),
    inference(superposition,[],[f197,f3475])).

fof(f3475,plain,(
    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f3425,f88])).

fof(f88,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f51,f47])).

fof(f47,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f3425,plain,
    ( ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)) ),
    inference(superposition,[],[f3347,f3265])).

fof(f3265,plain,(
    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1) ),
    inference(superposition,[],[f3191,f413])).

fof(f413,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f83,f50])).

fof(f83,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2)) ),
    inference(definition_unfolding,[],[f67,f54,f54])).

fof(f67,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f3191,plain,(
    ! [X5] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))),sK1) ),
    inference(forward_demodulation,[],[f3130,f87])).

fof(f87,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f3130,plain,(
    ! [X5] : k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))),sK1) ),
    inference(superposition,[],[f2679,f430])).

fof(f430,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(forward_demodulation,[],[f419,f48])).

fof(f419,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f83,f91])).

fof(f91,plain,(
    ! [X2,X1] : k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1) ),
    inference(resolution,[],[f56,f51])).

fof(f2679,plain,(
    ! [X9] : k2_zfmisc_1(k3_xboole_0(sK2,X9),sK3) = k2_zfmisc_1(k3_xboole_0(sK0,X9),sK1) ),
    inference(backward_demodulation,[],[f854,f2656])).

fof(f2656,plain,(
    ! [X4,X5] : k3_xboole_0(k2_zfmisc_1(X4,sK1),k2_zfmisc_1(X5,sK3)) = k2_zfmisc_1(k3_xboole_0(X4,X5),sK1) ),
    inference(superposition,[],[f75,f2525])).

fof(f3347,plain,(
    ! [X41] :
      ( ~ r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0)
      | k1_xboole_0 = X41 ) ),
    inference(subsumption_resolution,[],[f3346,f88])).

fof(f3346,plain,(
    ! [X41] :
      ( ~ r1_tarski(k1_xboole_0,X41)
      | k1_xboole_0 = X41
      | ~ r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f3345,f3325])).

fof(f3325,plain,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) ),
    inference(subsumption_resolution,[],[f3316,f45])).

fof(f3316,plain,(
    ! [X1] :
      ( k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,sK2)))
      | k1_xboole_0 = sK1 ) ),
    inference(trivial_inequality_removal,[],[f3268])).

fof(f3268,plain,(
    ! [X1] :
      ( k1_xboole_0 != k1_xboole_0
      | k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,sK2)))
      | k1_xboole_0 = sK1 ) ),
    inference(superposition,[],[f64,f3191])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3345,plain,(
    ! [X41,X40] :
      ( k1_xboole_0 = X41
      | ~ r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0)
      | ~ r1_tarski(k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))),X41) ) ),
    inference(forward_demodulation,[],[f3344,f3325])).

fof(f3344,plain,(
    ! [X41,X40] :
      ( ~ r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0)
      | k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))) = X41
      | ~ r1_tarski(k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))),X41) ) ),
    inference(subsumption_resolution,[],[f3284,f45])).

fof(f3284,plain,(
    ! [X41,X40] :
      ( ~ r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0)
      | k1_xboole_0 = sK1
      | k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))) = X41
      | ~ r1_tarski(k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))),X41) ) ),
    inference(superposition,[],[f264,f3191])).

fof(f264,plain,(
    ! [X10,X8,X9] :
      ( ~ r1_tarski(k2_zfmisc_1(X8,X9),k2_zfmisc_1(X10,X9))
      | k1_xboole_0 = X9
      | X8 = X10
      | ~ r1_tarski(X10,X8) ) ),
    inference(resolution,[],[f73,f59])).

fof(f197,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k5_xboole_0(X6,k3_xboole_0(X6,X7))
      | X6 = X7
      | ~ r1_tarski(X7,X6) ) ),
    inference(resolution,[],[f82,f59])).

fof(f46,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f34])).

fof(f4669,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f4630,f48])).

fof(f4630,plain,
    ( k1_xboole_0 != k5_xboole_0(sK3,sK3)
    | sK1 = sK3 ),
    inference(backward_demodulation,[],[f2792,f4624])).

fof(f4624,plain,(
    sK3 = k3_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f4615,f4623])).

fof(f4623,plain,(
    ! [X5] :
      ( sK3 = k3_xboole_0(sK3,sK1)
      | k1_xboole_0 = X5 ) ),
    inference(subsumption_resolution,[],[f4613,f84])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4613,plain,(
    ! [X5] :
      ( sK3 = k3_xboole_0(sK3,sK1)
      | k1_xboole_0 = X5
      | ~ r1_tarski(k2_zfmisc_1(X5,sK0),k2_zfmisc_1(X5,sK0)) ) ),
    inference(resolution,[],[f4299,f292])).

fof(f292,plain,(
    ! [X6,X4,X7,X5] :
      ( r1_tarski(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X7))
      | k1_xboole_0 = X4
      | ~ r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,X6)) ) ),
    inference(resolution,[],[f74,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f4299,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X9))
      | sK3 = k3_xboole_0(sK3,X9) ) ),
    inference(forward_demodulation,[],[f4298,f4022])).

fof(f4298,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9))
      | sK3 = k3_xboole_0(sK3,X9) ) ),
    inference(subsumption_resolution,[],[f4068,f44])).

fof(f4068,plain,(
    ! [X9] :
      ( k1_xboole_0 = sK0
      | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9))
      | sK3 = k3_xboole_0(sK3,X9) ) ),
    inference(backward_demodulation,[],[f1341,f4022])).

fof(f1341,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9))
      | k1_xboole_0 = sK2
      | sK3 = k3_xboole_0(sK3,X9) ) ),
    inference(superposition,[],[f294,f43])).

fof(f294,plain,(
    ! [X12,X13,X11] :
      ( ~ r1_tarski(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X11,X13))
      | k1_xboole_0 = X11
      | k3_xboole_0(X12,X13) = X12 ) ),
    inference(resolution,[],[f74,f56])).

fof(f4615,plain,
    ( sK3 = k3_xboole_0(sK3,sK1)
    | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK0)) ),
    inference(resolution,[],[f4299,f196])).

fof(f196,plain,(
    ! [X4,X5,X3] :
      ( r1_tarski(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X5))
      | k1_xboole_0 != k5_xboole_0(X3,k3_xboole_0(X3,X4)) ) ),
    inference(resolution,[],[f82,f68])).

fof(f2792,plain,
    ( k1_xboole_0 != k5_xboole_0(sK3,k3_xboole_0(sK3,sK1))
    | sK1 = sK3 ),
    inference(resolution,[],[f2756,f82])).

fof(f2756,plain,
    ( ~ r1_tarski(sK3,sK1)
    | sK1 = sK3 ),
    inference(subsumption_resolution,[],[f2664,f48])).

fof(f2664,plain,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | sK1 = sK3
    | ~ r1_tarski(sK3,sK1) ),
    inference(superposition,[],[f197,f2525])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:42:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (32207)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.50  % (32223)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (32204)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.51  % (32215)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (32201)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.52  % (32219)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (32220)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.52  % (32211)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (32223)Refutation not found, incomplete strategy% (32223)------------------------------
% 0.20/0.52  % (32223)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32223)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32223)Memory used [KB]: 6268
% 0.20/0.52  % (32223)Time elapsed: 0.106 s
% 0.20/0.52  % (32223)------------------------------
% 0.20/0.52  % (32223)------------------------------
% 0.20/0.52  % (32225)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (32209)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.52  % (32226)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (32216)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.52  % (32226)Refutation not found, incomplete strategy% (32226)------------------------------
% 0.20/0.52  % (32226)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (32226)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (32226)Memory used [KB]: 1663
% 0.20/0.52  % (32226)Time elapsed: 0.119 s
% 0.20/0.52  % (32226)------------------------------
% 0.20/0.52  % (32226)------------------------------
% 0.20/0.52  % (32197)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.52  % (32203)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (32202)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (32214)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.53  % (32198)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.53  % (32198)Refutation not found, incomplete strategy% (32198)------------------------------
% 0.20/0.53  % (32198)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (32198)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (32198)Memory used [KB]: 1663
% 0.20/0.53  % (32198)Time elapsed: 0.116 s
% 0.20/0.53  % (32198)------------------------------
% 0.20/0.53  % (32198)------------------------------
% 0.20/0.53  % (32208)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.20/0.53  % (32212)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.53  % (32224)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (32199)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (32210)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (32222)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.53  % (32205)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.53  % (32213)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.54  % (32218)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (32200)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.54  % (32221)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (32217)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.55  % (32206)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.56  % (32213)Refutation not found, incomplete strategy% (32213)------------------------------
% 0.20/0.56  % (32213)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (32213)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (32213)Memory used [KB]: 10618
% 0.20/0.56  % (32213)Time elapsed: 0.146 s
% 0.20/0.56  % (32213)------------------------------
% 0.20/0.56  % (32213)------------------------------
% 2.11/0.65  % (32229)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.11/0.65  % (32230)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.11/0.66  % (32228)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.11/0.66  % (32200)Refutation not found, incomplete strategy% (32200)------------------------------
% 2.11/0.66  % (32200)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.11/0.68  % (32200)Termination reason: Refutation not found, incomplete strategy
% 2.11/0.68  
% 2.11/0.68  % (32200)Memory used [KB]: 6268
% 2.11/0.68  % (32200)Time elapsed: 0.241 s
% 2.11/0.68  % (32200)------------------------------
% 2.11/0.68  % (32200)------------------------------
% 2.66/0.71  % (32231)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.17/0.79  % (32232)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 3.17/0.82  % (32221)Time limit reached!
% 3.17/0.82  % (32221)------------------------------
% 3.17/0.82  % (32221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.82  % (32221)Termination reason: Time limit
% 3.17/0.82  
% 3.17/0.82  % (32221)Memory used [KB]: 12920
% 3.17/0.82  % (32221)Time elapsed: 0.411 s
% 3.17/0.82  % (32221)------------------------------
% 3.17/0.82  % (32221)------------------------------
% 3.17/0.83  % (32199)Time limit reached!
% 3.17/0.83  % (32199)------------------------------
% 3.17/0.83  % (32199)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.17/0.83  % (32199)Termination reason: Time limit
% 3.17/0.83  % (32199)Termination phase: Saturation
% 3.17/0.83  
% 3.17/0.83  % (32199)Memory used [KB]: 6780
% 3.17/0.83  % (32199)Time elapsed: 0.400 s
% 3.17/0.83  % (32199)------------------------------
% 3.17/0.83  % (32199)------------------------------
% 4.34/0.95  % (32233)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.34/0.95  % (32211)Time limit reached!
% 4.34/0.95  % (32211)------------------------------
% 4.34/0.95  % (32211)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.95  % (32211)Termination reason: Time limit
% 4.34/0.95  
% 4.34/0.95  % (32211)Memory used [KB]: 5756
% 4.34/0.95  % (32211)Time elapsed: 0.513 s
% 4.34/0.95  % (32211)------------------------------
% 4.34/0.95  % (32211)------------------------------
% 4.34/0.95  % (32234)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.34/0.96  % (32203)Time limit reached!
% 4.34/0.96  % (32203)------------------------------
% 4.34/0.96  % (32203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.34/0.98  % (32203)Termination reason: Time limit
% 4.34/0.98  % (32203)Termination phase: Saturation
% 4.34/0.98  
% 4.34/0.98  % (32203)Memory used [KB]: 16375
% 4.34/0.98  % (32203)Time elapsed: 0.500 s
% 4.34/0.98  % (32203)------------------------------
% 4.34/0.98  % (32203)------------------------------
% 4.34/1.00  % (32219)Refutation found. Thanks to Tanya!
% 4.34/1.00  % SZS status Theorem for theBenchmark
% 4.34/1.00  % SZS output start Proof for theBenchmark
% 4.34/1.00  fof(f4670,plain,(
% 4.34/1.00    $false),
% 4.34/1.00    inference(subsumption_resolution,[],[f4669,f4285])).
% 4.34/1.00  fof(f4285,plain,(
% 4.34/1.00    sK1 != sK3),
% 4.34/1.00    inference(trivial_inequality_removal,[],[f4024])).
% 4.34/1.00  fof(f4024,plain,(
% 4.34/1.00    sK0 != sK0 | sK1 != sK3),
% 4.34/1.00    inference(backward_demodulation,[],[f46,f4022])).
% 4.34/1.00  fof(f4022,plain,(
% 4.34/1.00    sK0 = sK2),
% 4.34/1.00    inference(subsumption_resolution,[],[f3972,f48])).
% 4.34/1.00  fof(f48,plain,(
% 4.34/1.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.34/1.00    inference(cnf_transformation,[],[f14])).
% 4.34/1.00  fof(f14,axiom,(
% 4.34/1.00    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.34/1.00  fof(f3972,plain,(
% 4.34/1.00    k1_xboole_0 != k5_xboole_0(sK2,sK2) | sK0 = sK2),
% 4.34/1.00    inference(backward_demodulation,[],[f3864,f3892])).
% 4.34/1.00  fof(f3892,plain,(
% 4.34/1.00    sK2 = k3_xboole_0(sK2,sK0)),
% 4.34/1.00    inference(subsumption_resolution,[],[f3883,f45])).
% 4.34/1.00  fof(f45,plain,(
% 4.34/1.00    k1_xboole_0 != sK1),
% 4.34/1.00    inference(cnf_transformation,[],[f34])).
% 4.34/1.00  fof(f34,plain,(
% 4.34/1.00    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 4.34/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f33])).
% 4.34/1.00  fof(f33,plain,(
% 4.34/1.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 4.34/1.00    introduced(choice_axiom,[])).
% 4.34/1.00  fof(f25,plain,(
% 4.34/1.00    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 4.34/1.00    inference(flattening,[],[f24])).
% 4.34/1.00  fof(f24,plain,(
% 4.34/1.00    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 4.34/1.00    inference(ennf_transformation,[],[f22])).
% 4.34/1.00  fof(f22,negated_conjecture,(
% 4.34/1.00    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.34/1.00    inference(negated_conjecture,[],[f21])).
% 4.34/1.00  fof(f21,conjecture,(
% 4.34/1.00    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 4.34/1.00  fof(f3883,plain,(
% 4.34/1.00    k1_xboole_0 = sK1 | sK2 = k3_xboole_0(sK2,sK0)),
% 4.34/1.00    inference(resolution,[],[f3558,f265])).
% 4.34/1.00  fof(f265,plain,(
% 4.34/1.00    ( ! [X12,X13,X11] : (~r1_tarski(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X13,X12)) | k1_xboole_0 = X12 | k3_xboole_0(X11,X13) = X11) )),
% 4.34/1.00    inference(resolution,[],[f73,f56])).
% 4.34/1.00  fof(f56,plain,(
% 4.34/1.00    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 4.34/1.00    inference(cnf_transformation,[],[f27])).
% 4.34/1.00  fof(f27,plain,(
% 4.34/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.34/1.00    inference(ennf_transformation,[],[f9])).
% 4.34/1.00  fof(f9,axiom,(
% 4.34/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.34/1.00  fof(f73,plain,(
% 4.34/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | k1_xboole_0 = X0) )),
% 4.34/1.00    inference(cnf_transformation,[],[f31])).
% 4.34/1.00  fof(f31,plain,(
% 4.34/1.00    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 4.34/1.00    inference(ennf_transformation,[],[f17])).
% 4.34/1.00  fof(f17,axiom,(
% 4.34/1.00    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 4.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 4.34/1.00  fof(f3558,plain,(
% 4.34/1.00    r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))),
% 4.34/1.00    inference(subsumption_resolution,[],[f3549,f48])).
% 4.34/1.00  fof(f3549,plain,(
% 4.34/1.00    k1_xboole_0 != k5_xboole_0(sK1,sK1) | r1_tarski(k2_zfmisc_1(sK2,sK1),k2_zfmisc_1(sK0,sK1))),
% 4.34/1.00    inference(superposition,[],[f1197,f2525])).
% 4.34/1.00  fof(f2525,plain,(
% 4.34/1.00    sK1 = k3_xboole_0(sK1,sK3)),
% 4.34/1.00    inference(subsumption_resolution,[],[f2524,f51])).
% 4.34/1.00  fof(f51,plain,(
% 4.34/1.00    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 4.34/1.00    inference(cnf_transformation,[],[f6])).
% 4.34/1.00  fof(f6,axiom,(
% 4.34/1.00    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 4.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 4.34/1.00  fof(f2524,plain,(
% 4.34/1.00    sK1 = k3_xboole_0(sK1,sK3) | ~r1_tarski(k3_xboole_0(sK1,sK3),sK1)),
% 4.34/1.00    inference(subsumption_resolution,[],[f2515,f44])).
% 4.34/1.00  fof(f44,plain,(
% 4.34/1.00    k1_xboole_0 != sK0),
% 4.34/1.00    inference(cnf_transformation,[],[f34])).
% 4.34/1.00  fof(f2515,plain,(
% 4.34/1.00    k1_xboole_0 = sK0 | sK1 = k3_xboole_0(sK1,sK3) | ~r1_tarski(k3_xboole_0(sK1,sK3),sK1)),
% 4.34/1.00    inference(resolution,[],[f2478,f293])).
% 4.34/1.00  fof(f293,plain,(
% 4.34/1.00    ( ! [X10,X8,X9] : (~r1_tarski(k2_zfmisc_1(X8,X9),k2_zfmisc_1(X8,X10)) | k1_xboole_0 = X8 | X9 = X10 | ~r1_tarski(X10,X9)) )),
% 4.34/1.00    inference(resolution,[],[f74,f59])).
% 4.34/1.00  fof(f59,plain,(
% 4.34/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 4.34/1.00    inference(cnf_transformation,[],[f36])).
% 4.34/1.00  fof(f36,plain,(
% 4.34/1.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.34/1.00    inference(flattening,[],[f35])).
% 4.34/1.00  fof(f35,plain,(
% 4.34/1.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 4.34/1.00    inference(nnf_transformation,[],[f3])).
% 4.34/1.00  fof(f3,axiom,(
% 4.34/1.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 4.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 4.34/1.00  fof(f74,plain,(
% 4.34/1.00    ( ! [X2,X0,X1] : (r1_tarski(X1,X2) | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | k1_xboole_0 = X0) )),
% 4.34/1.00    inference(cnf_transformation,[],[f31])).
% 4.34/1.00  fof(f2478,plain,(
% 4.34/1.00    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 4.34/1.00    inference(superposition,[],[f2451,f50])).
% 4.34/1.00  fof(f50,plain,(
% 4.34/1.00    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 4.34/1.00    inference(cnf_transformation,[],[f23])).
% 4.34/1.00  fof(f23,plain,(
% 4.34/1.00    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 4.34/1.00    inference(rectify,[],[f2])).
% 4.34/1.00  fof(f2,axiom,(
% 4.34/1.00    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 4.34/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 4.34/1.00  fof(f2451,plain,(
% 4.34/1.00    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(sK1,X3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 4.34/1.00    inference(forward_demodulation,[],[f2450,f314])).
% 4.34/1.00  fof(f314,plain,(
% 4.34/1.00    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X3,X4),k2_zfmisc_1(X3,X5)) = k2_zfmisc_1(X3,k3_xboole_0(X4,X5))) )),
% 4.34/1.00    inference(superposition,[],[f75,f50])).
% 4.34/1.00  fof(f75,plain,(
% 4.34/1.00    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 4.34/1.00    inference(cnf_transformation,[],[f19])).
% 4.87/1.00  fof(f19,axiom,(
% 4.87/1.00    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 4.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 4.87/1.00  fof(f2450,plain,(
% 4.87/1.00    ( ! [X3] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 4.87/1.00    inference(forward_demodulation,[],[f2449,f43])).
% 4.87/1.00  fof(f43,plain,(
% 4.87/1.00    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 4.87/1.00    inference(cnf_transformation,[],[f34])).
% 4.87/1.00  fof(f2449,plain,(
% 4.87/1.00    ( ! [X3] : (r1_tarski(k3_xboole_0(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,X3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 4.87/1.00    inference(forward_demodulation,[],[f2402,f75])).
% 4.87/1.00  fof(f2402,plain,(
% 4.87/1.00    ( ! [X3] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,sK0),k3_xboole_0(sK3,X3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 4.87/1.00    inference(superposition,[],[f113,f2349])).
% 4.87/1.00  fof(f2349,plain,(
% 4.87/1.00    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3)),
% 4.87/1.00    inference(superposition,[],[f854,f314])).
% 4.87/1.00  fof(f854,plain,(
% 4.87/1.00    ( ! [X9] : (k2_zfmisc_1(k3_xboole_0(sK2,X9),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK3))) )),
% 4.87/1.00    inference(superposition,[],[f321,f43])).
% 4.87/1.00  fof(f321,plain,(
% 4.87/1.00    ( ! [X4,X5,X3] : (k3_xboole_0(k2_zfmisc_1(X4,X3),k2_zfmisc_1(X5,X3)) = k2_zfmisc_1(k3_xboole_0(X4,X5),X3)) )),
% 4.87/1.00    inference(superposition,[],[f75,f50])).
% 4.87/1.00  fof(f113,plain,(
% 4.87/1.00    ( ! [X4,X2,X3] : (r1_tarski(k2_zfmisc_1(X2,k3_xboole_0(X3,X4)),k2_zfmisc_1(X2,X3))) )),
% 4.87/1.00    inference(resolution,[],[f69,f51])).
% 4.87/1.00  fof(f69,plain,(
% 4.87/1.00    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 4.87/1.00    inference(cnf_transformation,[],[f28])).
% 4.87/1.00  fof(f28,plain,(
% 4.87/1.00    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 4.87/1.00    inference(ennf_transformation,[],[f18])).
% 4.87/1.00  fof(f18,axiom,(
% 4.87/1.00    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 4.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 4.87/1.00  fof(f1197,plain,(
% 4.87/1.00    ( ! [X9] : (k1_xboole_0 != k5_xboole_0(X9,k3_xboole_0(X9,sK3)) | r1_tarski(k2_zfmisc_1(sK2,X9),k2_zfmisc_1(sK0,sK1))) )),
% 4.87/1.00    inference(superposition,[],[f195,f43])).
% 4.87/1.00  fof(f195,plain,(
% 4.87/1.00    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.87/1.00    inference(resolution,[],[f82,f69])).
% 4.87/1.00  fof(f82,plain,(
% 4.87/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.87/1.00    inference(definition_unfolding,[],[f62,f54])).
% 4.87/1.00  fof(f54,plain,(
% 4.87/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.87/1.00    inference(cnf_transformation,[],[f5])).
% 4.87/1.00  fof(f5,axiom,(
% 4.87/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.87/1.00  fof(f62,plain,(
% 4.87/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 4.87/1.00    inference(cnf_transformation,[],[f38])).
% 4.87/1.00  fof(f38,plain,(
% 4.87/1.00    ! [X0,X1] : ((k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)))),
% 4.87/1.00    inference(nnf_transformation,[],[f4])).
% 4.87/1.00  fof(f4,axiom,(
% 4.87/1.00    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 4.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 4.87/1.00  fof(f3864,plain,(
% 4.87/1.00    sK0 = sK2 | k1_xboole_0 != k5_xboole_0(sK2,k3_xboole_0(sK2,sK0))),
% 4.87/1.00    inference(resolution,[],[f3572,f82])).
% 4.87/1.00  fof(f3572,plain,(
% 4.87/1.00    ~r1_tarski(sK2,sK0) | sK0 = sK2),
% 4.87/1.00    inference(trivial_inequality_removal,[],[f3561])).
% 4.87/1.00  fof(f3561,plain,(
% 4.87/1.00    k1_xboole_0 != k1_xboole_0 | sK0 = sK2 | ~r1_tarski(sK2,sK0)),
% 4.87/1.00    inference(superposition,[],[f197,f3475])).
% 4.87/1.00  fof(f3475,plain,(
% 4.87/1.00    k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 4.87/1.00    inference(subsumption_resolution,[],[f3425,f88])).
% 4.87/1.00  fof(f88,plain,(
% 4.87/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.87/1.00    inference(superposition,[],[f51,f47])).
% 4.87/1.00  fof(f47,plain,(
% 4.87/1.00    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 4.87/1.00    inference(cnf_transformation,[],[f10])).
% 4.87/1.00  fof(f10,axiom,(
% 4.87/1.00    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 4.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 4.87/1.00  fof(f3425,plain,(
% 4.87/1.00    ~r1_tarski(k1_xboole_0,k1_xboole_0) | k1_xboole_0 = k5_xboole_0(sK0,k3_xboole_0(sK0,sK2))),
% 4.87/1.00    inference(superposition,[],[f3347,f3265])).
% 4.87/1.00  fof(f3265,plain,(
% 4.87/1.00    k1_xboole_0 = k2_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK2)),sK1)),
% 4.87/1.00    inference(superposition,[],[f3191,f413])).
% 4.87/1.00  fof(f413,plain,(
% 4.87/1.00    ( ! [X2,X3] : (k5_xboole_0(X2,k3_xboole_0(X2,X3)) = k3_xboole_0(X2,k5_xboole_0(X2,k3_xboole_0(X2,X3)))) )),
% 4.87/1.00    inference(superposition,[],[f83,f50])).
% 4.87/1.00  fof(f83,plain,(
% 4.87/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X2))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(k3_xboole_0(X0,X1),X2))) )),
% 4.87/1.00    inference(definition_unfolding,[],[f67,f54,f54])).
% 4.87/1.00  fof(f67,plain,(
% 4.87/1.00    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 4.87/1.00    inference(cnf_transformation,[],[f11])).
% 4.87/1.00  fof(f11,axiom,(
% 4.87/1.00    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 4.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 4.87/1.00  fof(f3191,plain,(
% 4.87/1.00    ( ! [X5] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))),sK1)) )),
% 4.87/1.00    inference(forward_demodulation,[],[f3130,f87])).
% 4.87/1.00  fof(f87,plain,(
% 4.87/1.00    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 4.87/1.00    inference(equality_resolution,[],[f65])).
% 4.87/1.00  fof(f65,plain,(
% 4.87/1.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 4.87/1.00    inference(cnf_transformation,[],[f40])).
% 4.87/1.00  fof(f40,plain,(
% 4.87/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.87/1.00    inference(flattening,[],[f39])).
% 4.87/1.00  fof(f39,plain,(
% 4.87/1.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 4.87/1.00    inference(nnf_transformation,[],[f16])).
% 4.87/1.00  fof(f16,axiom,(
% 4.87/1.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 4.87/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 4.87/1.00  fof(f3130,plain,(
% 4.87/1.00    ( ! [X5] : (k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(X5,k3_xboole_0(X5,sK2))),sK1)) )),
% 4.87/1.00    inference(superposition,[],[f2679,f430])).
% 4.87/1.00  fof(f430,plain,(
% 4.87/1.00    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 4.87/1.00    inference(forward_demodulation,[],[f419,f48])).
% 4.87/1.00  fof(f419,plain,(
% 4.87/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) = k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.87/1.00    inference(superposition,[],[f83,f91])).
% 4.87/1.00  fof(f91,plain,(
% 4.87/1.00    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k3_xboole_0(k3_xboole_0(X1,X2),X1)) )),
% 4.87/1.00    inference(resolution,[],[f56,f51])).
% 4.87/1.00  fof(f2679,plain,(
% 4.87/1.00    ( ! [X9] : (k2_zfmisc_1(k3_xboole_0(sK2,X9),sK3) = k2_zfmisc_1(k3_xboole_0(sK0,X9),sK1)) )),
% 4.87/1.00    inference(backward_demodulation,[],[f854,f2656])).
% 4.87/1.00  fof(f2656,plain,(
% 4.87/1.00    ( ! [X4,X5] : (k3_xboole_0(k2_zfmisc_1(X4,sK1),k2_zfmisc_1(X5,sK3)) = k2_zfmisc_1(k3_xboole_0(X4,X5),sK1)) )),
% 4.87/1.00    inference(superposition,[],[f75,f2525])).
% 4.87/1.00  fof(f3347,plain,(
% 4.87/1.00    ( ! [X41] : (~r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0) | k1_xboole_0 = X41) )),
% 4.87/1.00    inference(subsumption_resolution,[],[f3346,f88])).
% 4.87/1.00  fof(f3346,plain,(
% 4.87/1.00    ( ! [X41] : (~r1_tarski(k1_xboole_0,X41) | k1_xboole_0 = X41 | ~r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0)) )),
% 4.87/1.00    inference(forward_demodulation,[],[f3345,f3325])).
% 4.87/1.00  fof(f3325,plain,(
% 4.87/1.00    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,sK2)))) )),
% 4.87/1.00    inference(subsumption_resolution,[],[f3316,f45])).
% 4.87/1.00  fof(f3316,plain,(
% 4.87/1.00    ( ! [X1] : (k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) | k1_xboole_0 = sK1) )),
% 4.87/1.00    inference(trivial_inequality_removal,[],[f3268])).
% 4.87/1.00  fof(f3268,plain,(
% 4.87/1.00    ( ! [X1] : (k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k3_xboole_0(sK0,k5_xboole_0(X1,k3_xboole_0(X1,sK2))) | k1_xboole_0 = sK1) )),
% 4.87/1.00    inference(superposition,[],[f64,f3191])).
% 4.87/1.00  fof(f64,plain,(
% 4.87/1.00    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 4.87/1.00    inference(cnf_transformation,[],[f40])).
% 4.87/1.00  fof(f3345,plain,(
% 4.87/1.00    ( ! [X41,X40] : (k1_xboole_0 = X41 | ~r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0) | ~r1_tarski(k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))),X41)) )),
% 4.87/1.00    inference(forward_demodulation,[],[f3344,f3325])).
% 4.87/1.00  fof(f3344,plain,(
% 4.87/1.00    ( ! [X41,X40] : (~r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0) | k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))) = X41 | ~r1_tarski(k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))),X41)) )),
% 4.87/1.00    inference(subsumption_resolution,[],[f3284,f45])).
% 4.87/1.00  fof(f3284,plain,(
% 4.87/1.00    ( ! [X41,X40] : (~r1_tarski(k2_zfmisc_1(X41,sK1),k1_xboole_0) | k1_xboole_0 = sK1 | k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))) = X41 | ~r1_tarski(k3_xboole_0(sK0,k5_xboole_0(X40,k3_xboole_0(X40,sK2))),X41)) )),
% 4.87/1.00    inference(superposition,[],[f264,f3191])).
% 4.87/1.00  fof(f264,plain,(
% 4.87/1.00    ( ! [X10,X8,X9] : (~r1_tarski(k2_zfmisc_1(X8,X9),k2_zfmisc_1(X10,X9)) | k1_xboole_0 = X9 | X8 = X10 | ~r1_tarski(X10,X8)) )),
% 4.87/1.00    inference(resolution,[],[f73,f59])).
% 4.87/1.00  fof(f197,plain,(
% 4.87/1.00    ( ! [X6,X7] : (k1_xboole_0 != k5_xboole_0(X6,k3_xboole_0(X6,X7)) | X6 = X7 | ~r1_tarski(X7,X6)) )),
% 4.87/1.00    inference(resolution,[],[f82,f59])).
% 4.87/1.00  fof(f46,plain,(
% 4.87/1.00    sK1 != sK3 | sK0 != sK2),
% 4.87/1.00    inference(cnf_transformation,[],[f34])).
% 4.87/1.00  fof(f4669,plain,(
% 4.87/1.00    sK1 = sK3),
% 4.87/1.00    inference(subsumption_resolution,[],[f4630,f48])).
% 4.87/1.00  fof(f4630,plain,(
% 4.87/1.00    k1_xboole_0 != k5_xboole_0(sK3,sK3) | sK1 = sK3),
% 4.87/1.00    inference(backward_demodulation,[],[f2792,f4624])).
% 4.87/1.00  fof(f4624,plain,(
% 4.87/1.00    sK3 = k3_xboole_0(sK3,sK1)),
% 4.87/1.00    inference(subsumption_resolution,[],[f4615,f4623])).
% 4.87/1.00  fof(f4623,plain,(
% 4.87/1.00    ( ! [X5] : (sK3 = k3_xboole_0(sK3,sK1) | k1_xboole_0 = X5) )),
% 4.87/1.00    inference(subsumption_resolution,[],[f4613,f84])).
% 4.87/1.00  fof(f84,plain,(
% 4.87/1.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 4.87/1.00    inference(equality_resolution,[],[f58])).
% 4.87/1.00  fof(f58,plain,(
% 4.87/1.00    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 4.87/1.00    inference(cnf_transformation,[],[f36])).
% 4.87/1.00  fof(f4613,plain,(
% 4.87/1.00    ( ! [X5] : (sK3 = k3_xboole_0(sK3,sK1) | k1_xboole_0 = X5 | ~r1_tarski(k2_zfmisc_1(X5,sK0),k2_zfmisc_1(X5,sK0))) )),
% 4.87/1.00    inference(resolution,[],[f4299,f292])).
% 4.87/1.00  fof(f292,plain,(
% 4.87/1.00    ( ! [X6,X4,X7,X5] : (r1_tarski(k2_zfmisc_1(X5,X7),k2_zfmisc_1(X6,X7)) | k1_xboole_0 = X4 | ~r1_tarski(k2_zfmisc_1(X4,X5),k2_zfmisc_1(X4,X6))) )),
% 4.87/1.00    inference(resolution,[],[f74,f68])).
% 4.87/1.00  fof(f68,plain,(
% 4.87/1.00    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 4.87/1.00    inference(cnf_transformation,[],[f28])).
% 4.87/1.00  fof(f4299,plain,(
% 4.87/1.00    ( ! [X9] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X9)) | sK3 = k3_xboole_0(sK3,X9)) )),
% 4.87/1.00    inference(forward_demodulation,[],[f4298,f4022])).
% 4.87/1.00  fof(f4298,plain,(
% 4.87/1.00    ( ! [X9] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9)) | sK3 = k3_xboole_0(sK3,X9)) )),
% 4.87/1.00    inference(subsumption_resolution,[],[f4068,f44])).
% 4.87/1.00  fof(f4068,plain,(
% 4.87/1.00    ( ! [X9] : (k1_xboole_0 = sK0 | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9)) | sK3 = k3_xboole_0(sK3,X9)) )),
% 4.87/1.00    inference(backward_demodulation,[],[f1341,f4022])).
% 4.87/1.00  fof(f1341,plain,(
% 4.87/1.00    ( ! [X9] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X9)) | k1_xboole_0 = sK2 | sK3 = k3_xboole_0(sK3,X9)) )),
% 4.87/1.00    inference(superposition,[],[f294,f43])).
% 4.87/1.00  fof(f294,plain,(
% 4.87/1.00    ( ! [X12,X13,X11] : (~r1_tarski(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X11,X13)) | k1_xboole_0 = X11 | k3_xboole_0(X12,X13) = X12) )),
% 4.87/1.00    inference(resolution,[],[f74,f56])).
% 4.87/1.00  fof(f4615,plain,(
% 4.87/1.00    sK3 = k3_xboole_0(sK3,sK1) | k1_xboole_0 != k5_xboole_0(sK0,k3_xboole_0(sK0,sK0))),
% 4.87/1.00    inference(resolution,[],[f4299,f196])).
% 4.87/1.00  fof(f196,plain,(
% 4.87/1.00    ( ! [X4,X5,X3] : (r1_tarski(k2_zfmisc_1(X3,X5),k2_zfmisc_1(X4,X5)) | k1_xboole_0 != k5_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 4.87/1.00    inference(resolution,[],[f82,f68])).
% 4.87/1.00  fof(f2792,plain,(
% 4.87/1.00    k1_xboole_0 != k5_xboole_0(sK3,k3_xboole_0(sK3,sK1)) | sK1 = sK3),
% 4.87/1.00    inference(resolution,[],[f2756,f82])).
% 4.87/1.00  fof(f2756,plain,(
% 4.87/1.00    ~r1_tarski(sK3,sK1) | sK1 = sK3),
% 4.87/1.00    inference(subsumption_resolution,[],[f2664,f48])).
% 4.87/1.00  fof(f2664,plain,(
% 4.87/1.00    k1_xboole_0 != k5_xboole_0(sK1,sK1) | sK1 = sK3 | ~r1_tarski(sK3,sK1)),
% 4.87/1.00    inference(superposition,[],[f197,f2525])).
% 4.87/1.00  % SZS output end Proof for theBenchmark
% 4.87/1.00  % (32219)------------------------------
% 4.87/1.00  % (32219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.87/1.00  % (32219)Termination reason: Refutation
% 4.87/1.00  
% 4.87/1.00  % (32219)Memory used [KB]: 10874
% 4.87/1.00  % (32219)Time elapsed: 0.555 s
% 4.87/1.00  % (32219)------------------------------
% 4.87/1.00  % (32219)------------------------------
% 4.87/1.01  % (32196)Success in time 0.645 s
%------------------------------------------------------------------------------
