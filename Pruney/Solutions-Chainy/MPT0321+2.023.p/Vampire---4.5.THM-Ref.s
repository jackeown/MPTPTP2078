%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:32 EST 2020

% Result     : Theorem 5.33s
% Output     : Refutation 5.33s
% Verified   : 
% Statistics : Number of formulae       :  171 (3446 expanded)
%              Number of leaves         :   19 ( 898 expanded)
%              Depth                    :   57
%              Number of atoms          :  262 (10435 expanded)
%              Number of equality atoms :  235 (10103 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9020,plain,(
    $false ),
    inference(subsumption_resolution,[],[f9019,f8354])).

fof(f8354,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f7839])).

fof(f7839,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f45,f7837])).

fof(f7837,plain,(
    sK0 = sK2 ),
    inference(forward_demodulation,[],[f7809,f56])).

fof(f56,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f7809,plain,(
    sK2 = k2_xboole_0(sK0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f5970,f7808])).

fof(f7808,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f7776,f78])).

fof(f78,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f7776,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0)
    | k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(backward_demodulation,[],[f467,f7761])).

fof(f7761,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f7760,f43])).

fof(f43,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f36])).

fof(f36,plain,
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

fof(f31,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f27])).

fof(f27,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f7760,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f7747])).

fof(f7747,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f52,f7366])).

fof(f7366,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f7365,f78])).

fof(f7365,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f7364,f3166])).

fof(f3166,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(subsumption_resolution,[],[f3165,f43])).

fof(f3165,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(trivial_inequality_removal,[],[f3152])).

fof(f3152,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(superposition,[],[f52,f2937])).

fof(f2937,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f2557,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).

fof(f2557,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f2524,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f2524,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f2469,f2473])).

fof(f2473,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f2459,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f2459,plain,(
    r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2458,f860])).

fof(f860,plain,(
    ! [X4] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X4)),sK3) ),
    inference(forward_demodulation,[],[f827,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f827,plain,(
    ! [X4] : k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X4)),sK3) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X4,sK3)) ),
    inference(backward_demodulation,[],[f187,f814])).

fof(f814,plain,(
    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f813,f79])).

fof(f79,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f813,plain,(
    k2_zfmisc_1(k1_xboole_0,sK3) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f782,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f782,plain,(
    k2_zfmisc_1(k3_xboole_0(sK2,k1_xboole_0),sK3) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f96,f79])).

fof(f96,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3) ),
    inference(superposition,[],[f81,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f81,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) ),
    inference(superposition,[],[f60,f42])).

fof(f42,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f187,plain,(
    ! [X4] : k4_xboole_0(k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(X4,sK3)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X4)),sK3) ),
    inference(forward_demodulation,[],[f172,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f172,plain,(
    ! [X4] : k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X4),sK3) = k4_xboole_0(k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(X4,sK3)) ),
    inference(superposition,[],[f62,f138])).

fof(f138,plain,(
    k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f82,f79])).

fof(f82,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f60,f42])).

fof(f62,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f26])).

fof(f2458,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK2)),sK3)
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2441,f69])).

fof(f2441,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2),sK3) ),
    inference(superposition,[],[f350,f815])).

fof(f815,plain,(
    k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) ),
    inference(backward_demodulation,[],[f138,f814])).

fof(f350,plain,(
    ! [X2] :
      ( r1_tarski(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X2,sK2),sK3) ) ),
    inference(superposition,[],[f50,f86])).

fof(f86,plain,(
    ! [X5] : k2_zfmisc_1(k4_xboole_0(X5,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f62,f42])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f2469,plain,(
    r1_tarski(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2468,f79])).

fof(f2468,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3)
    | r1_tarski(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2467,f58])).

fof(f2467,plain,
    ( k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(k1_xboole_0,sK2),sK3)
    | r1_tarski(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f2452,f71])).

fof(f71,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f2452,plain,
    ( r1_tarski(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(k2_xboole_0(k1_xboole_0,sK2),sK2),sK3) ),
    inference(superposition,[],[f350,f585])).

fof(f585,plain,(
    k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f90,f79])).

fof(f90,plain,(
    ! [X9] : k2_zfmisc_1(k2_xboole_0(X9,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f64,f42])).

fof(f64,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f7364,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f7363,f63])).

fof(f7363,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f7338,f262])).

fof(f262,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f85,f63])).

fof(f85,plain,(
    ! [X4] : k2_zfmisc_1(k4_xboole_0(sK2,X4),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3)) ),
    inference(superposition,[],[f62,f42])).

fof(f7338,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f85,f6437])).

fof(f6437,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f6436,f77])).

fof(f77,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f6436,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,sK3) ),
    inference(forward_demodulation,[],[f6396,f6010])).

fof(f6010,plain,(
    k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f113,f6004])).

fof(f6004,plain,(
    sK0 = k3_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f73,f5969])).

fof(f5969,plain,(
    sK2 = k2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f5881,f67])).

fof(f5881,plain,(
    r1_tarski(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f5878])).

fof(f5878,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f50,f5561])).

fof(f5561,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(trivial_inequality_removal,[],[f5528])).

fof(f5528,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f412,f5454])).

fof(f5454,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    inference(backward_demodulation,[],[f388,f5436])).

fof(f5436,plain,(
    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) ),
    inference(superposition,[],[f3911,f77])).

fof(f3911,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK0,sK2)),sK1) ),
    inference(backward_demodulation,[],[f401,f3910])).

fof(f3910,plain,(
    ! [X2,X3] : k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,k4_xboole_0(sK3,sK1))) ),
    inference(forward_demodulation,[],[f3902,f78])).

fof(f3902,plain,(
    ! [X2,X3] : k2_zfmisc_1(k3_xboole_0(X2,X3),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,k4_xboole_0(sK3,sK1))) ),
    inference(superposition,[],[f59,f3872])).

fof(f3872,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)) ),
    inference(subsumption_resolution,[],[f3871,f43])).

fof(f3871,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)) ),
    inference(trivial_inequality_removal,[],[f3858])).

fof(f3858,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f52,f2997])).

fof(f2997,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) ),
    inference(backward_demodulation,[],[f354,f2996])).

fof(f2996,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK2,sK2)),sK3) ),
    inference(forward_demodulation,[],[f2950,f57])).

fof(f2950,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK2,sK2)),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k1_xboole_0) ),
    inference(backward_demodulation,[],[f324,f2937])).

fof(f324,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK2,sK2)),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f60,f272])).

fof(f272,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f261,f63])).

fof(f261,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f85,f42])).

fof(f354,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(sK2,sK2)),sK3) ),
    inference(forward_demodulation,[],[f353,f69])).

fof(f353,plain,(
    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) ),
    inference(forward_demodulation,[],[f352,f69])).

fof(f352,plain,(
    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK1)) ),
    inference(forward_demodulation,[],[f340,f63])).

fof(f340,plain,(
    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f86,f113])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f401,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))) ),
    inference(superposition,[],[f60,f388])).

fof(f388,plain,(
    k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f87,f62])).

fof(f87,plain,(
    ! [X6] : k2_zfmisc_1(sK2,k4_xboole_0(sK3,X6)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6)) ),
    inference(superposition,[],[f63,f42])).

fof(f412,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))
    | k1_xboole_0 = k4_xboole_0(sK0,sK2) ),
    inference(subsumption_resolution,[],[f399,f44])).

fof(f44,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f37])).

fof(f399,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))
    | k1_xboole_0 = k4_xboole_0(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f52,f388])).

fof(f73,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f113,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    inference(forward_demodulation,[],[f95,f76])).

fof(f95,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f81,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f24])).

fof(f6396,plain,(
    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f6118,f42])).

fof(f6118,plain,(
    ! [X2] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X2)) ),
    inference(backward_demodulation,[],[f83,f6117])).

fof(f6117,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X2)) ),
    inference(forward_demodulation,[],[f6116,f61])).

fof(f6116,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X2)) ),
    inference(forward_demodulation,[],[f6033,f6023])).

fof(f6023,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f207,f6004])).

fof(f207,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f191,f76])).

fof(f191,plain,(
    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f83,f60])).

fof(f6033,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,X2)) ),
    inference(backward_demodulation,[],[f227,f6004])).

fof(f227,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2)) ),
    inference(forward_demodulation,[],[f226,f83])).

fof(f226,plain,(
    ! [X2] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2)) ),
    inference(forward_demodulation,[],[f214,f59])).

fof(f214,plain,(
    ! [X2] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X2)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2)) ),
    inference(superposition,[],[f61,f207])).

fof(f83,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) ),
    inference(superposition,[],[f61,f42])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f467,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3))
    | k1_xboole_0 = k4_xboole_0(sK2,sK0) ),
    inference(subsumption_resolution,[],[f454,f44])).

fof(f454,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3))
    | k1_xboole_0 = k4_xboole_0(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(superposition,[],[f52,f416])).

fof(f416,plain,(
    k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f88,f62])).

fof(f88,plain,(
    ! [X7] : k2_zfmisc_1(sK2,k4_xboole_0(X7,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,X7),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f63,f42])).

fof(f5970,plain,(
    sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0)) ),
    inference(resolution,[],[f5881,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

fof(f45,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f37])).

fof(f9019,plain,(
    sK1 = sK3 ),
    inference(forward_demodulation,[],[f9015,f7136])).

fof(f7136,plain,(
    sK1 = k2_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f74,f6463])).

fof(f6463,plain,(
    sK3 = k3_xboole_0(sK1,sK3) ),
    inference(superposition,[],[f5996,f76])).

fof(f5996,plain,(
    sK3 = k3_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f73,f5799])).

fof(f5799,plain,(
    sK1 = k2_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f5797,f67])).

fof(f5797,plain,(
    r1_tarski(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f5794])).

fof(f5794,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK3,sK1) ),
    inference(superposition,[],[f50,f5715])).

fof(f5715,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(subsumption_resolution,[],[f5714,f43])).

fof(f5714,plain,
    ( k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(trivial_inequality_removal,[],[f5701])).

fof(f5701,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK3,sK1) ),
    inference(superposition,[],[f52,f5597])).

fof(f5597,plain,(
    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) ),
    inference(forward_demodulation,[],[f5562,f79])).

fof(f5562,plain,(
    k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) ),
    inference(backward_demodulation,[],[f346,f5561])).

fof(f346,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK3) ),
    inference(superposition,[],[f86,f63])).

fof(f74,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f9015,plain,(
    sK3 = k2_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f9014,f67])).

fof(f9014,plain,(
    r1_tarski(sK1,sK3) ),
    inference(trivial_inequality_removal,[],[f9011])).

fof(f9011,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK1,sK3) ),
    inference(superposition,[],[f50,f7761])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:12:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.52  % (17191)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.54  % (17203)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (17181)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (17182)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (17180)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (17183)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (17192)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (17184)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (17188)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (17206)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.54  % (17197)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.54  % (17208)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (17179)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (17189)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (17208)Refutation not found, incomplete strategy% (17208)------------------------------
% 0.22/0.55  % (17208)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17208)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17208)Memory used [KB]: 1663
% 0.22/0.55  % (17208)Time elapsed: 0.137 s
% 0.22/0.55  % (17208)------------------------------
% 0.22/0.55  % (17208)------------------------------
% 0.22/0.55  % (17194)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (17193)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.55  % (17187)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.55  % (17202)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (17198)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (17207)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (17200)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (17204)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.48/0.56  % (17190)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.48/0.56  % (17201)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.48/0.56  % (17195)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.48/0.56  % (17195)Refutation not found, incomplete strategy% (17195)------------------------------
% 1.48/0.56  % (17195)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (17195)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (17195)Memory used [KB]: 10618
% 1.48/0.56  % (17195)Time elapsed: 0.143 s
% 1.48/0.56  % (17195)------------------------------
% 1.48/0.56  % (17195)------------------------------
% 1.48/0.56  % (17199)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.48/0.56  % (17185)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.48/0.56  % (17186)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.48/0.57  % (17205)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.57  % (17196)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.63/0.73  % (17220)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.63/0.73  % (17219)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.81/0.81  % (17203)Time limit reached!
% 2.81/0.81  % (17203)------------------------------
% 2.81/0.81  % (17203)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.81  % (17203)Termination reason: Time limit
% 2.81/0.81  
% 2.81/0.81  % (17203)Memory used [KB]: 13560
% 2.81/0.81  % (17203)Time elapsed: 0.407 s
% 2.81/0.81  % (17203)------------------------------
% 2.81/0.81  % (17203)------------------------------
% 2.81/0.81  % (17181)Time limit reached!
% 2.81/0.81  % (17181)------------------------------
% 2.81/0.81  % (17181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.81  % (17181)Termination reason: Time limit
% 2.81/0.81  
% 2.81/0.81  % (17181)Memory used [KB]: 6524
% 2.81/0.81  % (17181)Time elapsed: 0.403 s
% 2.81/0.81  % (17181)------------------------------
% 2.81/0.81  % (17181)------------------------------
% 3.84/0.94  % (17221)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 3.84/0.95  % (17222)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 4.33/0.96  % (17185)Time limit reached!
% 4.33/0.96  % (17185)------------------------------
% 4.33/0.96  % (17185)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.33/0.96  % (17185)Termination reason: Time limit
% 4.33/0.96  % (17185)Termination phase: Saturation
% 4.33/0.96  
% 4.33/0.96  % (17185)Memory used [KB]: 15735
% 4.33/0.96  % (17185)Time elapsed: 0.500 s
% 4.33/0.96  % (17185)------------------------------
% 4.33/0.96  % (17185)------------------------------
% 4.40/0.97  % (17193)Time limit reached!
% 4.40/0.97  % (17193)------------------------------
% 4.40/0.97  % (17193)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.40/0.97  % (17193)Termination reason: Time limit
% 4.40/0.97  
% 4.40/0.97  % (17193)Memory used [KB]: 6140
% 4.40/0.97  % (17193)Time elapsed: 0.524 s
% 4.40/0.97  % (17193)------------------------------
% 4.40/0.97  % (17193)------------------------------
% 5.33/1.06  % (17186)Time limit reached!
% 5.33/1.06  % (17186)------------------------------
% 5.33/1.06  % (17186)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.33/1.06  % (17186)Termination reason: Time limit
% 5.33/1.06  
% 5.33/1.06  % (17186)Memory used [KB]: 7419
% 5.33/1.06  % (17186)Time elapsed: 0.629 s
% 5.33/1.06  % (17186)------------------------------
% 5.33/1.06  % (17186)------------------------------
% 5.33/1.10  % (17224)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 5.33/1.12  % (17223)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 5.33/1.13  % (17197)Refutation found. Thanks to Tanya!
% 5.33/1.13  % SZS status Theorem for theBenchmark
% 5.33/1.13  % SZS output start Proof for theBenchmark
% 5.33/1.13  fof(f9020,plain,(
% 5.33/1.13    $false),
% 5.33/1.13    inference(subsumption_resolution,[],[f9019,f8354])).
% 5.33/1.13  fof(f8354,plain,(
% 5.33/1.13    sK1 != sK3),
% 5.33/1.13    inference(trivial_inequality_removal,[],[f7839])).
% 5.33/1.13  fof(f7839,plain,(
% 5.33/1.13    sK0 != sK0 | sK1 != sK3),
% 5.33/1.13    inference(backward_demodulation,[],[f45,f7837])).
% 5.33/1.13  fof(f7837,plain,(
% 5.33/1.13    sK0 = sK2),
% 5.33/1.13    inference(forward_demodulation,[],[f7809,f56])).
% 5.33/1.13  fof(f56,plain,(
% 5.33/1.13    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 5.33/1.13    inference(cnf_transformation,[],[f9])).
% 5.33/1.13  fof(f9,axiom,(
% 5.33/1.13    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 5.33/1.13  fof(f7809,plain,(
% 5.33/1.13    sK2 = k2_xboole_0(sK0,k1_xboole_0)),
% 5.33/1.13    inference(backward_demodulation,[],[f5970,f7808])).
% 5.33/1.13  fof(f7808,plain,(
% 5.33/1.13    k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 5.33/1.13    inference(subsumption_resolution,[],[f7776,f78])).
% 5.33/1.13  fof(f78,plain,(
% 5.33/1.13    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 5.33/1.13    inference(equality_resolution,[],[f54])).
% 5.33/1.13  fof(f54,plain,(
% 5.33/1.13    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 5.33/1.13    inference(cnf_transformation,[],[f41])).
% 5.33/1.13  fof(f41,plain,(
% 5.33/1.13    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 5.33/1.13    inference(flattening,[],[f40])).
% 5.33/1.13  fof(f40,plain,(
% 5.33/1.13    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 5.33/1.13    inference(nnf_transformation,[],[f21])).
% 5.33/1.13  fof(f21,axiom,(
% 5.33/1.13    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 5.33/1.13  fof(f7776,plain,(
% 5.33/1.13    k1_xboole_0 != k2_zfmisc_1(sK2,k1_xboole_0) | k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 5.33/1.13    inference(backward_demodulation,[],[f467,f7761])).
% 5.33/1.13  fof(f7761,plain,(
% 5.33/1.13    k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 5.33/1.13    inference(subsumption_resolution,[],[f7760,f43])).
% 5.33/1.13  fof(f43,plain,(
% 5.33/1.13    k1_xboole_0 != sK0),
% 5.33/1.13    inference(cnf_transformation,[],[f37])).
% 5.33/1.13  fof(f37,plain,(
% 5.33/1.13    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 5.33/1.13    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f31,f36])).
% 5.33/1.13  fof(f36,plain,(
% 5.33/1.13    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 5.33/1.13    introduced(choice_axiom,[])).
% 5.33/1.13  fof(f31,plain,(
% 5.33/1.13    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 5.33/1.13    inference(flattening,[],[f30])).
% 5.33/1.13  fof(f30,plain,(
% 5.33/1.13    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 5.33/1.13    inference(ennf_transformation,[],[f28])).
% 5.33/1.13  fof(f28,negated_conjecture,(
% 5.33/1.13    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 5.33/1.13    inference(negated_conjecture,[],[f27])).
% 5.33/1.13  fof(f27,conjecture,(
% 5.33/1.13    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 5.33/1.13  fof(f7760,plain,(
% 5.33/1.13    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 5.33/1.13    inference(trivial_inequality_removal,[],[f7747])).
% 5.33/1.13  fof(f7747,plain,(
% 5.33/1.13    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK3)),
% 5.33/1.13    inference(superposition,[],[f52,f7366])).
% 5.33/1.13  fof(f7366,plain,(
% 5.33/1.13    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 5.33/1.13    inference(forward_demodulation,[],[f7365,f78])).
% 5.33/1.13  fof(f7365,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k1_xboole_0)),
% 5.33/1.13    inference(forward_demodulation,[],[f7364,f3166])).
% 5.33/1.13  fof(f3166,plain,(
% 5.33/1.13    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 5.33/1.13    inference(subsumption_resolution,[],[f3165,f43])).
% 5.33/1.13  fof(f3165,plain,(
% 5.33/1.13    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 5.33/1.13    inference(trivial_inequality_removal,[],[f3152])).
% 5.33/1.13  fof(f3152,plain,(
% 5.33/1.13    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 5.33/1.13    inference(superposition,[],[f52,f2937])).
% 5.33/1.13  fof(f2937,plain,(
% 5.33/1.13    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1))),
% 5.33/1.13    inference(superposition,[],[f2557,f63])).
% 5.33/1.13  fof(f63,plain,(
% 5.33/1.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 5.33/1.13    inference(cnf_transformation,[],[f26])).
% 5.33/1.13  fof(f26,axiom,(
% 5.33/1.13    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k4_xboole_0(X0,X1)) = k4_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_zfmisc_1)).
% 5.33/1.13  fof(f2557,plain,(
% 5.33/1.13    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(resolution,[],[f2524,f51])).
% 5.33/1.13  fof(f51,plain,(
% 5.33/1.13    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,X1) = k1_xboole_0) )),
% 5.33/1.13    inference(cnf_transformation,[],[f39])).
% 5.33/1.13  fof(f39,plain,(
% 5.33/1.13    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 5.33/1.13    inference(nnf_transformation,[],[f3])).
% 5.33/1.13  fof(f3,axiom,(
% 5.33/1.13    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 5.33/1.13  fof(f2524,plain,(
% 5.33/1.13    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(backward_demodulation,[],[f2469,f2473])).
% 5.33/1.13  fof(f2473,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(resolution,[],[f2459,f67])).
% 5.33/1.13  fof(f67,plain,(
% 5.33/1.13    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 5.33/1.13    inference(cnf_transformation,[],[f34])).
% 5.33/1.13  fof(f34,plain,(
% 5.33/1.13    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 5.33/1.13    inference(ennf_transformation,[],[f7])).
% 5.33/1.13  fof(f7,axiom,(
% 5.33/1.13    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 5.33/1.13  fof(f2459,plain,(
% 5.33/1.13    r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(subsumption_resolution,[],[f2458,f860])).
% 5.33/1.13  fof(f860,plain,(
% 5.33/1.13    ( ! [X4] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X4)),sK3)) )),
% 5.33/1.13    inference(forward_demodulation,[],[f827,f58])).
% 5.33/1.13  fof(f58,plain,(
% 5.33/1.13    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 5.33/1.13    inference(cnf_transformation,[],[f20])).
% 5.33/1.13  fof(f20,axiom,(
% 5.33/1.13    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 5.33/1.13  fof(f827,plain,(
% 5.33/1.13    ( ! [X4] : (k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X4)),sK3) = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(X4,sK3))) )),
% 5.33/1.13    inference(backward_demodulation,[],[f187,f814])).
% 5.33/1.13  fof(f814,plain,(
% 5.33/1.13    k1_xboole_0 = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(forward_demodulation,[],[f813,f79])).
% 5.33/1.13  fof(f79,plain,(
% 5.33/1.13    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 5.33/1.13    inference(equality_resolution,[],[f53])).
% 5.33/1.13  fof(f53,plain,(
% 5.33/1.13    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 5.33/1.13    inference(cnf_transformation,[],[f41])).
% 5.33/1.13  fof(f813,plain,(
% 5.33/1.13    k2_zfmisc_1(k1_xboole_0,sK3) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(forward_demodulation,[],[f782,f57])).
% 5.33/1.13  fof(f57,plain,(
% 5.33/1.13    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 5.33/1.13    inference(cnf_transformation,[],[f12])).
% 5.33/1.13  fof(f12,axiom,(
% 5.33/1.13    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 5.33/1.13  fof(f782,plain,(
% 5.33/1.13    k2_zfmisc_1(k3_xboole_0(sK2,k1_xboole_0),sK3) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(superposition,[],[f96,f79])).
% 5.33/1.13  fof(f96,plain,(
% 5.33/1.13    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k3_xboole_0(sK2,X1),sK3)) )),
% 5.33/1.13    inference(superposition,[],[f81,f76])).
% 5.33/1.13  fof(f76,plain,(
% 5.33/1.13    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 5.33/1.13    inference(cnf_transformation,[],[f1])).
% 5.33/1.13  fof(f1,axiom,(
% 5.33/1.13    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 5.33/1.13  fof(f81,plain,(
% 5.33/1.13    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))) )),
% 5.33/1.13    inference(superposition,[],[f60,f42])).
% 5.33/1.13  fof(f42,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 5.33/1.13    inference(cnf_transformation,[],[f37])).
% 5.33/1.13  fof(f60,plain,(
% 5.33/1.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 5.33/1.13    inference(cnf_transformation,[],[f24])).
% 5.33/1.13  fof(f24,axiom,(
% 5.33/1.13    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 5.33/1.13  fof(f187,plain,(
% 5.33/1.13    ( ! [X4] : (k4_xboole_0(k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(X4,sK3)) = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k4_xboole_0(sK2,X4)),sK3)) )),
% 5.33/1.13    inference(forward_demodulation,[],[f172,f69])).
% 5.33/1.13  fof(f69,plain,(
% 5.33/1.13    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 5.33/1.13    inference(cnf_transformation,[],[f19])).
% 5.33/1.13  fof(f19,axiom,(
% 5.33/1.13    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 5.33/1.13  fof(f172,plain,(
% 5.33/1.13    ( ! [X4] : (k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k1_xboole_0,sK2),X4),sK3) = k4_xboole_0(k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(X4,sK3))) )),
% 5.33/1.13    inference(superposition,[],[f62,f138])).
% 5.33/1.13  fof(f138,plain,(
% 5.33/1.13    k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3) = k3_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(superposition,[],[f82,f79])).
% 5.33/1.13  fof(f82,plain,(
% 5.33/1.13    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 5.33/1.13    inference(superposition,[],[f60,f42])).
% 5.33/1.13  fof(f62,plain,(
% 5.33/1.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 5.33/1.13    inference(cnf_transformation,[],[f26])).
% 5.33/1.13  fof(f2458,plain,(
% 5.33/1.13    k1_xboole_0 != k2_zfmisc_1(k3_xboole_0(k1_xboole_0,k4_xboole_0(sK2,sK2)),sK3) | r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(forward_demodulation,[],[f2441,f69])).
% 5.33/1.13  fof(f2441,plain,(
% 5.33/1.13    r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(k3_xboole_0(k1_xboole_0,sK2),sK2),sK3)),
% 5.33/1.13    inference(superposition,[],[f350,f815])).
% 5.33/1.13  fof(f815,plain,(
% 5.33/1.13    k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(k1_xboole_0,sK2),sK3)),
% 5.33/1.13    inference(backward_demodulation,[],[f138,f814])).
% 5.33/1.13  fof(f350,plain,(
% 5.33/1.13    ( ! [X2] : (r1_tarski(k2_zfmisc_1(X2,sK3),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(X2,sK2),sK3)) )),
% 5.33/1.13    inference(superposition,[],[f50,f86])).
% 5.33/1.13  fof(f86,plain,(
% 5.33/1.13    ( ! [X5] : (k2_zfmisc_1(k4_xboole_0(X5,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 5.33/1.13    inference(superposition,[],[f62,f42])).
% 5.33/1.13  fof(f50,plain,(
% 5.33/1.13    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 5.33/1.13    inference(cnf_transformation,[],[f39])).
% 5.33/1.13  fof(f2469,plain,(
% 5.33/1.13    r1_tarski(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(subsumption_resolution,[],[f2468,f79])).
% 5.33/1.13  fof(f2468,plain,(
% 5.33/1.13    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK3) | r1_tarski(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(forward_demodulation,[],[f2467,f58])).
% 5.33/1.13  fof(f2467,plain,(
% 5.33/1.13    k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(k1_xboole_0,sK2),sK3) | r1_tarski(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(forward_demodulation,[],[f2452,f71])).
% 5.33/1.13  fof(f71,plain,(
% 5.33/1.13    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 5.33/1.13    inference(cnf_transformation,[],[f16])).
% 5.33/1.13  fof(f16,axiom,(
% 5.33/1.13    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 5.33/1.13  fof(f2452,plain,(
% 5.33/1.13    r1_tarski(k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 != k2_zfmisc_1(k4_xboole_0(k2_xboole_0(k1_xboole_0,sK2),sK2),sK3)),
% 5.33/1.13    inference(superposition,[],[f350,f585])).
% 5.33/1.13  fof(f585,plain,(
% 5.33/1.13    k2_zfmisc_1(k2_xboole_0(k1_xboole_0,sK2),sK3) = k2_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(superposition,[],[f90,f79])).
% 5.33/1.13  fof(f90,plain,(
% 5.33/1.13    ( ! [X9] : (k2_zfmisc_1(k2_xboole_0(X9,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X9,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 5.33/1.13    inference(superposition,[],[f64,f42])).
% 5.33/1.13  fof(f64,plain,(
% 5.33/1.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 5.33/1.13    inference(cnf_transformation,[],[f23])).
% 5.33/1.13  fof(f23,axiom,(
% 5.33/1.13    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 5.33/1.13  fof(f7364,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1))),
% 5.33/1.13    inference(forward_demodulation,[],[f7363,f63])).
% 5.33/1.13  fof(f7363,plain,(
% 5.33/1.13    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3))),
% 5.33/1.13    inference(forward_demodulation,[],[f7338,f262])).
% 5.33/1.13  fof(f262,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK3)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 5.33/1.13    inference(superposition,[],[f85,f63])).
% 5.33/1.13  fof(f85,plain,(
% 5.33/1.13    ( ! [X4] : (k2_zfmisc_1(k4_xboole_0(sK2,X4),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X4,sK3))) )),
% 5.33/1.13    inference(superposition,[],[f62,f42])).
% 5.33/1.13  fof(f7338,plain,(
% 5.33/1.13    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK3)),
% 5.33/1.13    inference(superposition,[],[f85,f6437])).
% 5.33/1.13  fof(f6437,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,sK3)),
% 5.33/1.13    inference(forward_demodulation,[],[f6436,f77])).
% 5.33/1.13  fof(f77,plain,(
% 5.33/1.13    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 5.33/1.13    inference(cnf_transformation,[],[f29])).
% 5.33/1.13  fof(f29,plain,(
% 5.33/1.13    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 5.33/1.13    inference(rectify,[],[f2])).
% 5.33/1.13  fof(f2,axiom,(
% 5.33/1.13    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 5.33/1.13  fof(f6436,plain,(
% 5.33/1.13    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,sK3)),
% 5.33/1.13    inference(forward_demodulation,[],[f6396,f6010])).
% 5.33/1.13  fof(f6010,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 5.33/1.13    inference(backward_demodulation,[],[f113,f6004])).
% 5.33/1.13  fof(f6004,plain,(
% 5.33/1.13    sK0 = k3_xboole_0(sK0,sK2)),
% 5.33/1.13    inference(superposition,[],[f73,f5969])).
% 5.33/1.13  fof(f5969,plain,(
% 5.33/1.13    sK2 = k2_xboole_0(sK0,sK2)),
% 5.33/1.13    inference(resolution,[],[f5881,f67])).
% 5.33/1.13  fof(f5881,plain,(
% 5.33/1.13    r1_tarski(sK0,sK2)),
% 5.33/1.13    inference(trivial_inequality_removal,[],[f5878])).
% 5.33/1.13  fof(f5878,plain,(
% 5.33/1.13    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK0,sK2)),
% 5.33/1.13    inference(superposition,[],[f50,f5561])).
% 5.33/1.13  fof(f5561,plain,(
% 5.33/1.13    k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 5.33/1.13    inference(trivial_inequality_removal,[],[f5528])).
% 5.33/1.13  fof(f5528,plain,(
% 5.33/1.13    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 5.33/1.13    inference(superposition,[],[f412,f5454])).
% 5.33/1.13  fof(f5454,plain,(
% 5.33/1.13    k1_xboole_0 = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 5.33/1.13    inference(backward_demodulation,[],[f388,f5436])).
% 5.33/1.13  fof(f5436,plain,(
% 5.33/1.13    k1_xboole_0 = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1)),
% 5.33/1.13    inference(superposition,[],[f3911,f77])).
% 5.33/1.13  fof(f3911,plain,(
% 5.33/1.13    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK0,sK2)),sK1)) )),
% 5.33/1.13    inference(backward_demodulation,[],[f401,f3910])).
% 5.33/1.13  fof(f3910,plain,(
% 5.33/1.13    ( ! [X2,X3] : (k1_xboole_0 = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,k4_xboole_0(sK3,sK1)))) )),
% 5.33/1.13    inference(forward_demodulation,[],[f3902,f78])).
% 5.33/1.13  fof(f3902,plain,(
% 5.33/1.13    ( ! [X2,X3] : (k2_zfmisc_1(k3_xboole_0(X2,X3),k1_xboole_0) = k3_xboole_0(k2_zfmisc_1(X2,sK1),k2_zfmisc_1(X3,k4_xboole_0(sK3,sK1)))) )),
% 5.33/1.13    inference(superposition,[],[f59,f3872])).
% 5.33/1.13  fof(f3872,plain,(
% 5.33/1.13    k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),
% 5.33/1.13    inference(subsumption_resolution,[],[f3871,f43])).
% 5.33/1.13  fof(f3871,plain,(
% 5.33/1.13    k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),
% 5.33/1.13    inference(trivial_inequality_removal,[],[f3858])).
% 5.33/1.13  fof(f3858,plain,(
% 5.33/1.13    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))),
% 5.33/1.13    inference(superposition,[],[f52,f2997])).
% 5.33/1.13  fof(f2997,plain,(
% 5.33/1.13    k1_xboole_0 = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)))),
% 5.33/1.13    inference(backward_demodulation,[],[f354,f2996])).
% 5.33/1.13  fof(f2996,plain,(
% 5.33/1.13    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK2,sK2)),sK3)) )),
% 5.33/1.13    inference(forward_demodulation,[],[f2950,f57])).
% 5.33/1.13  fof(f2950,plain,(
% 5.33/1.13    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK2,sK2)),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k1_xboole_0)) )),
% 5.33/1.13    inference(backward_demodulation,[],[f324,f2937])).
% 5.33/1.13  fof(f324,plain,(
% 5.33/1.13    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK2,sK2)),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1)))) )),
% 5.33/1.13    inference(superposition,[],[f60,f272])).
% 5.33/1.13  fof(f272,plain,(
% 5.33/1.13    k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,sK1))),
% 5.33/1.13    inference(forward_demodulation,[],[f261,f63])).
% 5.33/1.13  fof(f261,plain,(
% 5.33/1.13    k2_zfmisc_1(k4_xboole_0(sK2,sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(superposition,[],[f85,f42])).
% 5.33/1.13  fof(f354,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1))) = k2_zfmisc_1(k3_xboole_0(sK0,k4_xboole_0(sK2,sK2)),sK3)),
% 5.33/1.13    inference(forward_demodulation,[],[f353,f69])).
% 5.33/1.13  fof(f353,plain,(
% 5.33/1.13    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,k4_xboole_0(sK3,sK1)))),
% 5.33/1.13    inference(forward_demodulation,[],[f352,f69])).
% 5.33/1.13  fof(f352,plain,(
% 5.33/1.13    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k2_zfmisc_1(sK0,k4_xboole_0(k3_xboole_0(sK1,sK3),sK1))),
% 5.33/1.13    inference(forward_demodulation,[],[f340,f63])).
% 5.33/1.13  fof(f340,plain,(
% 5.33/1.13    k2_zfmisc_1(k4_xboole_0(k3_xboole_0(sK0,sK2),sK2),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK1))),
% 5.33/1.13    inference(superposition,[],[f86,f113])).
% 5.33/1.13  fof(f59,plain,(
% 5.33/1.13    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 5.33/1.13    inference(cnf_transformation,[],[f25])).
% 5.33/1.13  fof(f25,axiom,(
% 5.33/1.13    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 5.33/1.13  fof(f401,plain,(
% 5.33/1.13    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,k4_xboole_0(sK0,sK2)),sK1) = k3_xboole_0(k2_zfmisc_1(X1,sK1),k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)))) )),
% 5.33/1.13    inference(superposition,[],[f60,f388])).
% 5.33/1.13  fof(f388,plain,(
% 5.33/1.13    k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1))),
% 5.33/1.13    inference(superposition,[],[f87,f62])).
% 5.33/1.13  fof(f87,plain,(
% 5.33/1.13    ( ! [X6] : (k2_zfmisc_1(sK2,k4_xboole_0(sK3,X6)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6))) )),
% 5.33/1.13    inference(superposition,[],[f63,f42])).
% 5.33/1.13  fof(f412,plain,(
% 5.33/1.13    k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) | k1_xboole_0 = k4_xboole_0(sK0,sK2)),
% 5.33/1.13    inference(subsumption_resolution,[],[f399,f44])).
% 5.33/1.13  fof(f44,plain,(
% 5.33/1.13    k1_xboole_0 != sK1),
% 5.33/1.13    inference(cnf_transformation,[],[f37])).
% 5.33/1.13  fof(f399,plain,(
% 5.33/1.13    k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK3,sK1)) | k1_xboole_0 = k4_xboole_0(sK0,sK2) | k1_xboole_0 = sK1),
% 5.33/1.13    inference(superposition,[],[f52,f388])).
% 5.33/1.13  fof(f73,plain,(
% 5.33/1.13    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 5.33/1.13    inference(cnf_transformation,[],[f10])).
% 5.33/1.13  fof(f10,axiom,(
% 5.33/1.13    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).
% 5.33/1.13  fof(f113,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 5.33/1.13    inference(forward_demodulation,[],[f95,f76])).
% 5.33/1.13  fof(f95,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3)),
% 5.33/1.13    inference(superposition,[],[f81,f61])).
% 5.33/1.13  fof(f61,plain,(
% 5.33/1.13    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 5.33/1.13    inference(cnf_transformation,[],[f24])).
% 5.33/1.13  fof(f6396,plain,(
% 5.33/1.13    k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 5.33/1.13    inference(superposition,[],[f6118,f42])).
% 5.33/1.13  fof(f6118,plain,(
% 5.33/1.13    ( ! [X2] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X2))) )),
% 5.33/1.13    inference(backward_demodulation,[],[f83,f6117])).
% 5.33/1.13  fof(f6117,plain,(
% 5.33/1.13    ( ! [X2] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,X2))) )),
% 5.33/1.13    inference(forward_demodulation,[],[f6116,f61])).
% 5.33/1.13  fof(f6116,plain,(
% 5.33/1.13    ( ! [X2] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X2))) )),
% 5.33/1.13    inference(forward_demodulation,[],[f6033,f6023])).
% 5.33/1.13  fof(f6023,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 5.33/1.13    inference(backward_demodulation,[],[f207,f6004])).
% 5.33/1.13  fof(f207,plain,(
% 5.33/1.13    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3))),
% 5.33/1.13    inference(forward_demodulation,[],[f191,f76])).
% 5.33/1.13  fof(f191,plain,(
% 5.33/1.13    k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k3_xboole_0(sK3,sK1))),
% 5.33/1.13    inference(superposition,[],[f83,f60])).
% 5.33/1.13  fof(f6033,plain,(
% 5.33/1.13    ( ! [X2] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,X2))) )),
% 5.33/1.13    inference(backward_demodulation,[],[f227,f6004])).
% 5.33/1.13  fof(f227,plain,(
% 5.33/1.13    ( ! [X2] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2))) )),
% 5.33/1.13    inference(forward_demodulation,[],[f226,f83])).
% 5.33/1.13  fof(f226,plain,(
% 5.33/1.13    ( ! [X2] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2))) )),
% 5.33/1.13    inference(forward_demodulation,[],[f214,f59])).
% 5.33/1.13  fof(f214,plain,(
% 5.33/1.13    ( ! [X2] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,X2)) = k3_xboole_0(k2_zfmisc_1(sK2,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(k3_xboole_0(sK0,sK2),X2))) )),
% 5.33/1.13    inference(superposition,[],[f61,f207])).
% 5.33/1.13  fof(f83,plain,(
% 5.33/1.13    ( ! [X2] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2))) )),
% 5.33/1.13    inference(superposition,[],[f61,f42])).
% 5.33/1.13  fof(f52,plain,(
% 5.33/1.13    ( ! [X0,X1] : (k1_xboole_0 != k2_zfmisc_1(X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 = X1) )),
% 5.33/1.13    inference(cnf_transformation,[],[f41])).
% 5.33/1.13  fof(f467,plain,(
% 5.33/1.13    k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3)) | k1_xboole_0 = k4_xboole_0(sK2,sK0)),
% 5.33/1.13    inference(subsumption_resolution,[],[f454,f44])).
% 5.33/1.13  fof(f454,plain,(
% 5.33/1.13    k1_xboole_0 != k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3)) | k1_xboole_0 = k4_xboole_0(sK2,sK0) | k1_xboole_0 = sK1),
% 5.33/1.13    inference(superposition,[],[f52,f416])).
% 5.33/1.13  fof(f416,plain,(
% 5.33/1.13    k2_zfmisc_1(k4_xboole_0(sK2,sK0),sK1) = k2_zfmisc_1(sK2,k4_xboole_0(sK1,sK3))),
% 5.33/1.13    inference(superposition,[],[f88,f62])).
% 5.33/1.13  fof(f88,plain,(
% 5.33/1.13    ( ! [X7] : (k2_zfmisc_1(sK2,k4_xboole_0(X7,sK3)) = k4_xboole_0(k2_zfmisc_1(sK2,X7),k2_zfmisc_1(sK0,sK1))) )),
% 5.33/1.13    inference(superposition,[],[f63,f42])).
% 5.33/1.13  fof(f5970,plain,(
% 5.33/1.13    sK2 = k2_xboole_0(sK0,k4_xboole_0(sK2,sK0))),
% 5.33/1.13    inference(resolution,[],[f5881,f66])).
% 5.33/1.13  fof(f66,plain,(
% 5.33/1.13    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1) )),
% 5.33/1.13    inference(cnf_transformation,[],[f33])).
% 5.33/1.13  fof(f33,plain,(
% 5.33/1.13    ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1 | ~r1_tarski(X0,X1))),
% 5.33/1.13    inference(ennf_transformation,[],[f17])).
% 5.33/1.13  fof(f17,axiom,(
% 5.33/1.13    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,k4_xboole_0(X1,X0)) = X1)),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).
% 5.33/1.13  fof(f45,plain,(
% 5.33/1.13    sK1 != sK3 | sK0 != sK2),
% 5.33/1.13    inference(cnf_transformation,[],[f37])).
% 5.33/1.13  fof(f9019,plain,(
% 5.33/1.13    sK1 = sK3),
% 5.33/1.13    inference(forward_demodulation,[],[f9015,f7136])).
% 5.33/1.13  fof(f7136,plain,(
% 5.33/1.13    sK1 = k2_xboole_0(sK1,sK3)),
% 5.33/1.13    inference(superposition,[],[f74,f6463])).
% 5.33/1.13  fof(f6463,plain,(
% 5.33/1.13    sK3 = k3_xboole_0(sK1,sK3)),
% 5.33/1.13    inference(superposition,[],[f5996,f76])).
% 5.33/1.13  fof(f5996,plain,(
% 5.33/1.13    sK3 = k3_xboole_0(sK3,sK1)),
% 5.33/1.13    inference(superposition,[],[f73,f5799])).
% 5.33/1.13  fof(f5799,plain,(
% 5.33/1.13    sK1 = k2_xboole_0(sK3,sK1)),
% 5.33/1.13    inference(resolution,[],[f5797,f67])).
% 5.33/1.13  fof(f5797,plain,(
% 5.33/1.13    r1_tarski(sK3,sK1)),
% 5.33/1.13    inference(trivial_inequality_removal,[],[f5794])).
% 5.33/1.13  fof(f5794,plain,(
% 5.33/1.13    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK3,sK1)),
% 5.33/1.13    inference(superposition,[],[f50,f5715])).
% 5.33/1.13  fof(f5715,plain,(
% 5.33/1.13    k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 5.33/1.13    inference(subsumption_resolution,[],[f5714,f43])).
% 5.33/1.13  fof(f5714,plain,(
% 5.33/1.13    k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 5.33/1.13    inference(trivial_inequality_removal,[],[f5701])).
% 5.33/1.13  fof(f5701,plain,(
% 5.33/1.13    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK3,sK1)),
% 5.33/1.13    inference(superposition,[],[f52,f5597])).
% 5.33/1.13  fof(f5597,plain,(
% 5.33/1.13    k1_xboole_0 = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))),
% 5.33/1.13    inference(forward_demodulation,[],[f5562,f79])).
% 5.33/1.13  fof(f5562,plain,(
% 5.33/1.13    k2_zfmisc_1(k1_xboole_0,sK3) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1))),
% 5.33/1.13    inference(backward_demodulation,[],[f346,f5561])).
% 5.33/1.13  fof(f346,plain,(
% 5.33/1.13    k2_zfmisc_1(sK0,k4_xboole_0(sK3,sK1)) = k2_zfmisc_1(k4_xboole_0(sK0,sK2),sK3)),
% 5.33/1.13    inference(superposition,[],[f86,f63])).
% 5.33/1.13  fof(f74,plain,(
% 5.33/1.13    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 5.33/1.13    inference(cnf_transformation,[],[f11])).
% 5.33/1.13  fof(f11,axiom,(
% 5.33/1.13    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 5.33/1.13    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 5.33/1.13  fof(f9015,plain,(
% 5.33/1.13    sK3 = k2_xboole_0(sK1,sK3)),
% 5.33/1.13    inference(resolution,[],[f9014,f67])).
% 5.33/1.13  fof(f9014,plain,(
% 5.33/1.13    r1_tarski(sK1,sK3)),
% 5.33/1.13    inference(trivial_inequality_removal,[],[f9011])).
% 5.33/1.13  fof(f9011,plain,(
% 5.33/1.13    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK1,sK3)),
% 5.33/1.13    inference(superposition,[],[f50,f7761])).
% 5.33/1.13  % SZS output end Proof for theBenchmark
% 5.33/1.13  % (17197)------------------------------
% 5.33/1.13  % (17197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.33/1.13  % (17197)Termination reason: Refutation
% 5.33/1.13  
% 5.33/1.13  % (17197)Memory used [KB]: 6396
% 5.33/1.13  % (17197)Time elapsed: 0.707 s
% 5.33/1.13  % (17197)------------------------------
% 5.33/1.13  % (17197)------------------------------
% 5.33/1.14  % (17170)Success in time 0.761 s
%------------------------------------------------------------------------------
