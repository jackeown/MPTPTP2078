%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:32 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  116 (3938 expanded)
%              Number of leaves         :   12 (1085 expanded)
%              Depth                    :   40
%              Number of atoms          :  207 (12708 expanded)
%              Number of equality atoms :  110 (10867 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2588,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2587,f160])).

fof(f160,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK1)) ),
    inference(unit_resulting_resolution,[],[f148,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f148,plain,(
    r1_tarski(sK1,sK1) ),
    inference(unit_resulting_resolution,[],[f26,f133,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f133,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f130,f25])).

fof(f25,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ( sK1 != sK3
      | sK0 != sK2 )
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f23])).

fof(f23,plain,
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

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
       => ( ( X1 = X3
            & X0 = X2 )
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)
     => ( ( X1 = X3
          & X0 = X2 )
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).

fof(f130,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f61,f29])).

fof(f29,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f61,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f30,f47])).

fof(f47,plain,(
    ! [X5] :
      ( r1_tarski(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1))
      | ~ r1_tarski(X5,sK2) ) ),
    inference(superposition,[],[f37,f25])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f26,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f2587,plain,(
    ~ r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(forward_demodulation,[],[f2584,f1863])).

fof(f1863,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f1133,f1774])).

fof(f1774,plain,(
    k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1773,f1704])).

fof(f1704,plain,
    ( k1_xboole_0 = sK2
    | sK0 = sK2 ),
    inference(subsumption_resolution,[],[f1701,f939])).

fof(f939,plain,(
    ~ r2_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f894,f91])).

fof(f91,plain,
    ( ~ r1_tarski(sK1,sK3)
    | ~ r2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f87,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f87,plain,
    ( r1_tarski(sK2,sK0)
    | ~ r1_tarski(sK1,sK3) ),
    inference(subsumption_resolution,[],[f82,f27])).

fof(f27,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,
    ( ~ r1_tarski(sK1,sK3)
    | r1_tarski(sK2,sK0)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f49,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    ! [X7] :
      ( r1_tarski(k2_zfmisc_1(sK2,X7),k2_zfmisc_1(sK0,sK1))
      | ~ r1_tarski(X7,sK3) ) ),
    inference(superposition,[],[f38,f25])).

fof(f894,plain,(
    r1_tarski(sK1,sK3) ),
    inference(backward_demodulation,[],[f572,f878])).

fof(f878,plain,(
    sK1 = k3_xboole_0(sK1,sK3) ),
    inference(unit_resulting_resolution,[],[f30,f873,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( X0 != X1
        & r1_tarski(X0,X1) )
     => r2_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f873,plain,(
    ~ r2_xboole_0(k3_xboole_0(sK1,sK3),sK1) ),
    inference(unit_resulting_resolution,[],[f762,f34])).

fof(f762,plain,(
    r1_tarski(sK1,k3_xboole_0(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f26,f726,f40])).

fof(f726,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f725,f25])).

fof(f725,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f724,f29])).

fof(f724,plain,(
    r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f723,f42])).

fof(f42,plain,(
    ! [X0] : k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) ),
    inference(superposition,[],[f35,f25])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).

fof(f723,plain,(
    r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f721,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f721,plain,(
    r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f584,f107])).

fof(f107,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3) ),
    inference(forward_demodulation,[],[f96,f31])).

fof(f31,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f96,plain,(
    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f42,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f584,plain,(
    ! [X0] : r1_tarski(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,sK3)) ),
    inference(unit_resulting_resolution,[],[f572,f38])).

fof(f572,plain,(
    r1_tarski(k3_xboole_0(sK1,sK3),sK3) ),
    inference(unit_resulting_resolution,[],[f26,f443,f40])).

fof(f443,plain,(
    r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK3)) ),
    inference(superposition,[],[f118,f107])).

fof(f118,plain,(
    ! [X8] : r1_tarski(k2_zfmisc_1(k3_xboole_0(X8,sK2),sK3),k2_zfmisc_1(X8,sK3)) ),
    inference(superposition,[],[f30,f43])).

fof(f43,plain,(
    ! [X1] : k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f35,f25])).

fof(f1701,plain,
    ( k1_xboole_0 = sK2
    | sK0 = sK2
    | r2_xboole_0(sK0,sK2) ),
    inference(resolution,[],[f1661,f33])).

fof(f1661,plain,
    ( r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f1642,f74])).

fof(f74,plain,
    ( ~ r1_tarski(sK3,sK1)
    | r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f69,f27])).

fof(f69,plain,
    ( ~ r1_tarski(sK3,sK1)
    | r1_tarski(sK0,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f48,f39])).

fof(f48,plain,(
    ! [X6] :
      ( r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6))
      | ~ r1_tarski(sK3,X6) ) ),
    inference(superposition,[],[f38,f25])).

fof(f1642,plain,
    ( r1_tarski(sK3,sK1)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1621,f133])).

fof(f1621,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK3,sK1)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f52,f1133])).

fof(f52,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X10))
      | r1_tarski(sK3,X10)
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f40,f25])).

fof(f1773,plain,
    ( sK0 != sK2
    | k1_xboole_0 = sK2 ),
    inference(trivial_inequality_removal,[],[f1717])).

fof(f1717,plain,
    ( sK1 != sK1
    | sK0 != sK2
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f28,f1666])).

fof(f1666,plain,
    ( sK1 = sK3
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f1664,f897])).

fof(f897,plain,(
    ~ r2_xboole_0(sK3,sK1) ),
    inference(backward_demodulation,[],[f585,f878])).

fof(f585,plain,(
    ~ r2_xboole_0(sK3,k3_xboole_0(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f572,f34])).

fof(f1664,plain,
    ( k1_xboole_0 = sK2
    | sK1 = sK3
    | r2_xboole_0(sK3,sK1) ),
    inference(resolution,[],[f1642,f33])).

fof(f28,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f24])).

fof(f1133,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f1127,f29])).

fof(f1127,plain,(
    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK1)) ),
    inference(superposition,[],[f1005,f910])).

fof(f910,plain,(
    sK1 = k3_xboole_0(sK3,sK1) ),
    inference(backward_demodulation,[],[f727,f878])).

fof(f727,plain,(
    k3_xboole_0(sK1,sK3) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK3)) ),
    inference(superposition,[],[f586,f31])).

fof(f586,plain,(
    k3_xboole_0(sK1,sK3) = k3_xboole_0(k3_xboole_0(sK1,sK3),sK3) ),
    inference(unit_resulting_resolution,[],[f572,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1005,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k2_zfmisc_1(sK0,k3_xboole_0(X2,sK1)) ),
    inference(backward_demodulation,[],[f44,f984])).

fof(f984,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1)) ),
    inference(backward_demodulation,[],[f169,f983])).

fof(f983,plain,(
    ! [X3] : k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1)) ),
    inference(backward_demodulation,[],[f45,f966])).

fof(f966,plain,(
    ! [X3] : k3_xboole_0(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1)) ),
    inference(backward_demodulation,[],[f792,f938])).

fof(f938,plain,(
    sK2 = k3_xboole_0(sK0,sK2) ),
    inference(unit_resulting_resolution,[],[f894,f94])).

fof(f94,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK2 = k3_xboole_0(sK0,sK2) ),
    inference(forward_demodulation,[],[f93,f31])).

fof(f93,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK2 = k3_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f87,f32])).

fof(f792,plain,(
    ! [X3] : k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f479,f766])).

fof(f766,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) ),
    inference(unit_resulting_resolution,[],[f605,f726,f33])).

fof(f605,plain,(
    ~ r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f347,f107])).

fof(f347,plain,(
    ! [X0] : ~ r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3)) ),
    inference(superposition,[],[f125,f31])).

fof(f125,plain,(
    ! [X0] : ~ r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3)) ),
    inference(unit_resulting_resolution,[],[f61,f34])).

fof(f479,plain,(
    ! [X3] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1)) ),
    inference(forward_demodulation,[],[f478,f36])).

fof(f478,plain,(
    ! [X3] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f477,f25])).

fof(f477,plain,(
    ! [X3] : k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK2,sK3)) ),
    inference(forward_demodulation,[],[f458,f41])).

fof(f458,plain,(
    ! [X3] : k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X3,sK3)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f36,f107])).

fof(f45,plain,(
    ! [X3] : k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f36,f25])).

fof(f169,plain,(
    ! [X1] : k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3)) ),
    inference(superposition,[],[f45,f31])).

fof(f44,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) ),
    inference(superposition,[],[f36,f25])).

fof(f2584,plain,(
    ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k1_xboole_0,sK1)) ),
    inference(unit_resulting_resolution,[],[f27,f2573,f39])).

fof(f2573,plain,(
    ~ r1_tarski(sK0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f26,f2038,f33])).

fof(f2038,plain,(
    ~ r2_xboole_0(sK0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f1799,f894])).

fof(f1799,plain,
    ( ~ r2_xboole_0(sK0,k1_xboole_0)
    | ~ r1_tarski(sK1,sK3) ),
    inference(backward_demodulation,[],[f91,f1774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:10:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (28475)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (28484)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (28470)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (28476)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (28474)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (28483)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (28478)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  % (28481)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (28486)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (28473)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (28471)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (28472)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (28469)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (28480)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (28479)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (28482)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (28477)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (28488)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (28489)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (28487)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (28485)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (28489)Refutation not found, incomplete strategy% (28489)------------------------------
% 0.21/0.52  % (28489)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (28489)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (28489)Memory used [KB]: 10490
% 0.21/0.52  % (28489)Time elapsed: 0.121 s
% 0.21/0.52  % (28489)------------------------------
% 0.21/0.52  % (28489)------------------------------
% 1.93/0.60  % (28484)Refutation found. Thanks to Tanya!
% 1.93/0.60  % SZS status Theorem for theBenchmark
% 1.93/0.60  % SZS output start Proof for theBenchmark
% 1.93/0.60  fof(f2588,plain,(
% 1.93/0.60    $false),
% 1.93/0.60    inference(subsumption_resolution,[],[f2587,f160])).
% 1.93/0.60  fof(f160,plain,(
% 1.93/0.60    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,sK1),k2_zfmisc_1(X0,sK1))) )),
% 1.93/0.60    inference(unit_resulting_resolution,[],[f148,f38])).
% 1.93/0.60  fof(f38,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f21])).
% 1.93/0.60  fof(f21,plain,(
% 1.93/0.60    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 1.93/0.60    inference(ennf_transformation,[],[f8])).
% 1.93/0.60  fof(f8,axiom,(
% 1.93/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 1.93/0.60  fof(f148,plain,(
% 1.93/0.60    r1_tarski(sK1,sK1)),
% 1.93/0.60    inference(unit_resulting_resolution,[],[f26,f133,f40])).
% 1.93/0.60  fof(f40,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 1.93/0.60    inference(cnf_transformation,[],[f22])).
% 1.93/0.60  fof(f22,plain,(
% 1.93/0.60    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 1.93/0.60    inference(ennf_transformation,[],[f7])).
% 1.93/0.60  fof(f7,axiom,(
% 1.93/0.60    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 1.93/0.60  fof(f133,plain,(
% 1.93/0.60    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 1.93/0.60    inference(forward_demodulation,[],[f130,f25])).
% 1.93/0.60  fof(f25,plain,(
% 1.93/0.60    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 1.93/0.60    inference(cnf_transformation,[],[f24])).
% 1.93/0.60  fof(f24,plain,(
% 1.93/0.60    (sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 1.93/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f23])).
% 1.93/0.60  fof(f23,plain,(
% 1.93/0.60    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3)) => ((sK1 != sK3 | sK0 != sK2) & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3))),
% 1.93/0.60    introduced(choice_axiom,[])).
% 1.93/0.60  fof(f16,plain,(
% 1.93/0.60    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.93/0.60    inference(flattening,[],[f15])).
% 1.93/0.60  fof(f15,plain,(
% 1.93/0.60    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 1.93/0.60    inference(ennf_transformation,[],[f12])).
% 1.93/0.60  fof(f12,negated_conjecture,(
% 1.93/0.60    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.93/0.60    inference(negated_conjecture,[],[f11])).
% 1.93/0.60  fof(f11,conjecture,(
% 1.93/0.60    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 1.93/0.60  fof(f130,plain,(
% 1.93/0.60    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,sK1))),
% 1.93/0.60    inference(superposition,[],[f61,f29])).
% 1.93/0.60  fof(f29,plain,(
% 1.93/0.60    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.93/0.60    inference(cnf_transformation,[],[f13])).
% 1.93/0.60  fof(f13,plain,(
% 1.93/0.60    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.93/0.60    inference(rectify,[],[f3])).
% 1.93/0.60  fof(f3,axiom,(
% 1.93/0.60    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.93/0.60  fof(f61,plain,(
% 1.93/0.60    ( ! [X0] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3),k2_zfmisc_1(sK0,sK1))) )),
% 1.93/0.60    inference(unit_resulting_resolution,[],[f30,f47])).
% 1.93/0.60  fof(f47,plain,(
% 1.93/0.60    ( ! [X5] : (r1_tarski(k2_zfmisc_1(X5,sK3),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X5,sK2)) )),
% 1.93/0.60    inference(superposition,[],[f37,f25])).
% 1.93/0.60  fof(f37,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f21])).
% 1.93/0.60  fof(f30,plain,(
% 1.93/0.60    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f4])).
% 1.93/0.60  fof(f4,axiom,(
% 1.93/0.60    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.93/0.60  fof(f26,plain,(
% 1.93/0.60    k1_xboole_0 != sK0),
% 1.93/0.60    inference(cnf_transformation,[],[f24])).
% 1.93/0.60  fof(f2587,plain,(
% 1.93/0.60    ~r1_tarski(k2_zfmisc_1(k1_xboole_0,sK1),k2_zfmisc_1(k1_xboole_0,sK1))),
% 1.93/0.60    inference(forward_demodulation,[],[f2584,f1863])).
% 1.93/0.60  fof(f1863,plain,(
% 1.93/0.60    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.93/0.60    inference(backward_demodulation,[],[f1133,f1774])).
% 1.93/0.60  fof(f1774,plain,(
% 1.93/0.60    k1_xboole_0 = sK2),
% 1.93/0.60    inference(subsumption_resolution,[],[f1773,f1704])).
% 1.93/0.60  fof(f1704,plain,(
% 1.93/0.60    k1_xboole_0 = sK2 | sK0 = sK2),
% 1.93/0.60    inference(subsumption_resolution,[],[f1701,f939])).
% 1.93/0.60  fof(f939,plain,(
% 1.93/0.60    ~r2_xboole_0(sK0,sK2)),
% 1.93/0.60    inference(unit_resulting_resolution,[],[f894,f91])).
% 1.93/0.60  fof(f91,plain,(
% 1.93/0.60    ~r1_tarski(sK1,sK3) | ~r2_xboole_0(sK0,sK2)),
% 1.93/0.60    inference(resolution,[],[f87,f34])).
% 1.93/0.60  fof(f34,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f20])).
% 1.93/0.60  fof(f20,plain,(
% 1.93/0.60    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 1.93/0.60    inference(ennf_transformation,[],[f6])).
% 1.93/0.60  fof(f6,axiom,(
% 1.93/0.60    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 1.93/0.60  fof(f87,plain,(
% 1.93/0.60    r1_tarski(sK2,sK0) | ~r1_tarski(sK1,sK3)),
% 1.93/0.60    inference(subsumption_resolution,[],[f82,f27])).
% 1.93/0.60  fof(f27,plain,(
% 1.93/0.60    k1_xboole_0 != sK1),
% 1.93/0.60    inference(cnf_transformation,[],[f24])).
% 1.93/0.60  fof(f82,plain,(
% 1.93/0.60    ~r1_tarski(sK1,sK3) | r1_tarski(sK2,sK0) | k1_xboole_0 = sK1),
% 1.93/0.60    inference(resolution,[],[f49,f39])).
% 1.93/0.60  fof(f39,plain,(
% 1.93/0.60    ( ! [X2,X0,X1] : (~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2) | k1_xboole_0 = X0) )),
% 1.93/0.60    inference(cnf_transformation,[],[f22])).
% 1.93/0.60  fof(f49,plain,(
% 1.93/0.60    ( ! [X7] : (r1_tarski(k2_zfmisc_1(sK2,X7),k2_zfmisc_1(sK0,sK1)) | ~r1_tarski(X7,sK3)) )),
% 1.93/0.60    inference(superposition,[],[f38,f25])).
% 1.93/0.60  fof(f894,plain,(
% 1.93/0.60    r1_tarski(sK1,sK3)),
% 1.93/0.60    inference(backward_demodulation,[],[f572,f878])).
% 1.93/0.60  fof(f878,plain,(
% 1.93/0.60    sK1 = k3_xboole_0(sK1,sK3)),
% 1.93/0.60    inference(unit_resulting_resolution,[],[f30,f873,f33])).
% 1.93/0.60  fof(f33,plain,(
% 1.93/0.60    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.93/0.60    inference(cnf_transformation,[],[f19])).
% 1.93/0.60  fof(f19,plain,(
% 1.93/0.60    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 1.93/0.60    inference(flattening,[],[f18])).
% 1.93/0.60  fof(f18,plain,(
% 1.93/0.60    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 1.93/0.60    inference(ennf_transformation,[],[f14])).
% 1.93/0.60  fof(f14,plain,(
% 1.93/0.60    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 1.93/0.60    inference(unused_predicate_definition_removal,[],[f2])).
% 1.93/0.60  fof(f2,axiom,(
% 1.93/0.60    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.93/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.93/0.61  fof(f873,plain,(
% 1.93/0.61    ~r2_xboole_0(k3_xboole_0(sK1,sK3),sK1)),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f762,f34])).
% 1.93/0.61  fof(f762,plain,(
% 1.93/0.61    r1_tarski(sK1,k3_xboole_0(sK1,sK3))),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f26,f726,f40])).
% 1.93/0.61  fof(f726,plain,(
% 1.93/0.61    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 1.93/0.61    inference(forward_demodulation,[],[f725,f25])).
% 1.93/0.61  fof(f725,plain,(
% 1.93/0.61    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 1.93/0.61    inference(forward_demodulation,[],[f724,f29])).
% 1.93/0.61  fof(f724,plain,(
% 1.93/0.61    r1_tarski(k2_zfmisc_1(k3_xboole_0(sK2,sK2),sK3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 1.93/0.61    inference(forward_demodulation,[],[f723,f42])).
% 1.93/0.61  fof(f42,plain,(
% 1.93/0.61    ( ! [X0] : (k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))) )),
% 1.93/0.61    inference(superposition,[],[f35,f25])).
% 1.93/0.61  fof(f35,plain,(
% 1.93/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f9])).
% 1.93/0.61  fof(f9,axiom,(
% 1.93/0.61    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k3_xboole_0(X0,X1),X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 1.93/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t122_zfmisc_1)).
% 1.93/0.61  fof(f723,plain,(
% 1.93/0.61    r1_tarski(k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 1.93/0.61    inference(forward_demodulation,[],[f721,f41])).
% 1.93/0.61  fof(f41,plain,(
% 1.93/0.61    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f10])).
% 1.93/0.61  fof(f10,axiom,(
% 1.93/0.61    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 1.93/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 1.93/0.61  fof(f721,plain,(
% 1.93/0.61    r1_tarski(k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 1.93/0.61    inference(superposition,[],[f584,f107])).
% 1.93/0.61  fof(f107,plain,(
% 1.93/0.61    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK0,sK2),sK3)),
% 1.93/0.61    inference(forward_demodulation,[],[f96,f31])).
% 1.93/0.61  fof(f31,plain,(
% 1.93/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.93/0.61    inference(cnf_transformation,[],[f1])).
% 1.93/0.61  fof(f1,axiom,(
% 1.93/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.93/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.93/0.61  fof(f96,plain,(
% 1.93/0.61    k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)) = k2_zfmisc_1(k3_xboole_0(sK2,sK0),sK3)),
% 1.93/0.61    inference(superposition,[],[f42,f36])).
% 1.93/0.61  fof(f36,plain,(
% 1.93/0.61    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 1.93/0.61    inference(cnf_transformation,[],[f9])).
% 1.93/0.61  fof(f584,plain,(
% 1.93/0.61    ( ! [X0] : (r1_tarski(k2_zfmisc_1(X0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(X0,sK3))) )),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f572,f38])).
% 1.93/0.61  fof(f572,plain,(
% 1.93/0.61    r1_tarski(k3_xboole_0(sK1,sK3),sK3)),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f26,f443,f40])).
% 1.93/0.61  fof(f443,plain,(
% 1.93/0.61    r1_tarski(k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)),k2_zfmisc_1(sK0,sK3))),
% 1.93/0.61    inference(superposition,[],[f118,f107])).
% 1.93/0.61  fof(f118,plain,(
% 1.93/0.61    ( ! [X8] : (r1_tarski(k2_zfmisc_1(k3_xboole_0(X8,sK2),sK3),k2_zfmisc_1(X8,sK3))) )),
% 1.93/0.61    inference(superposition,[],[f30,f43])).
% 1.93/0.61  fof(f43,plain,(
% 1.93/0.61    ( ! [X1] : (k2_zfmisc_1(k3_xboole_0(X1,sK2),sK3) = k3_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 1.93/0.61    inference(superposition,[],[f35,f25])).
% 1.93/0.61  fof(f1701,plain,(
% 1.93/0.61    k1_xboole_0 = sK2 | sK0 = sK2 | r2_xboole_0(sK0,sK2)),
% 1.93/0.61    inference(resolution,[],[f1661,f33])).
% 1.93/0.61  fof(f1661,plain,(
% 1.93/0.61    r1_tarski(sK0,sK2) | k1_xboole_0 = sK2),
% 1.93/0.61    inference(resolution,[],[f1642,f74])).
% 1.93/0.61  fof(f74,plain,(
% 1.93/0.61    ~r1_tarski(sK3,sK1) | r1_tarski(sK0,sK2)),
% 1.93/0.61    inference(subsumption_resolution,[],[f69,f27])).
% 1.93/0.61  fof(f69,plain,(
% 1.93/0.61    ~r1_tarski(sK3,sK1) | r1_tarski(sK0,sK2) | k1_xboole_0 = sK1),
% 1.93/0.61    inference(resolution,[],[f48,f39])).
% 1.93/0.61  fof(f48,plain,(
% 1.93/0.61    ( ! [X6] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X6)) | ~r1_tarski(sK3,X6)) )),
% 1.93/0.61    inference(superposition,[],[f38,f25])).
% 1.93/0.61  fof(f1642,plain,(
% 1.93/0.61    r1_tarski(sK3,sK1) | k1_xboole_0 = sK2),
% 1.93/0.61    inference(subsumption_resolution,[],[f1621,f133])).
% 1.93/0.61  fof(f1621,plain,(
% 1.93/0.61    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK3,sK1) | k1_xboole_0 = sK2),
% 1.93/0.61    inference(superposition,[],[f52,f1133])).
% 1.93/0.61  fof(f52,plain,(
% 1.93/0.61    ( ! [X10] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X10)) | r1_tarski(sK3,X10) | k1_xboole_0 = sK2) )),
% 1.93/0.61    inference(superposition,[],[f40,f25])).
% 1.93/0.61  fof(f1773,plain,(
% 1.93/0.61    sK0 != sK2 | k1_xboole_0 = sK2),
% 1.93/0.61    inference(trivial_inequality_removal,[],[f1717])).
% 1.93/0.61  fof(f1717,plain,(
% 1.93/0.61    sK1 != sK1 | sK0 != sK2 | k1_xboole_0 = sK2),
% 1.93/0.61    inference(superposition,[],[f28,f1666])).
% 1.93/0.61  fof(f1666,plain,(
% 1.93/0.61    sK1 = sK3 | k1_xboole_0 = sK2),
% 1.93/0.61    inference(subsumption_resolution,[],[f1664,f897])).
% 1.93/0.61  fof(f897,plain,(
% 1.93/0.61    ~r2_xboole_0(sK3,sK1)),
% 1.93/0.61    inference(backward_demodulation,[],[f585,f878])).
% 1.93/0.61  fof(f585,plain,(
% 1.93/0.61    ~r2_xboole_0(sK3,k3_xboole_0(sK1,sK3))),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f572,f34])).
% 1.93/0.61  fof(f1664,plain,(
% 1.93/0.61    k1_xboole_0 = sK2 | sK1 = sK3 | r2_xboole_0(sK3,sK1)),
% 1.93/0.61    inference(resolution,[],[f1642,f33])).
% 1.93/0.61  fof(f28,plain,(
% 1.93/0.61    sK1 != sK3 | sK0 != sK2),
% 1.93/0.61    inference(cnf_transformation,[],[f24])).
% 1.93/0.61  fof(f1133,plain,(
% 1.93/0.61    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 1.93/0.61    inference(forward_demodulation,[],[f1127,f29])).
% 1.93/0.61  fof(f1127,plain,(
% 1.93/0.61    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK1))),
% 1.93/0.61    inference(superposition,[],[f1005,f910])).
% 1.93/0.61  fof(f910,plain,(
% 1.93/0.61    sK1 = k3_xboole_0(sK3,sK1)),
% 1.93/0.61    inference(backward_demodulation,[],[f727,f878])).
% 1.93/0.61  fof(f727,plain,(
% 1.93/0.61    k3_xboole_0(sK1,sK3) = k3_xboole_0(sK3,k3_xboole_0(sK1,sK3))),
% 1.93/0.61    inference(superposition,[],[f586,f31])).
% 1.93/0.61  fof(f586,plain,(
% 1.93/0.61    k3_xboole_0(sK1,sK3) = k3_xboole_0(k3_xboole_0(sK1,sK3),sK3)),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f572,f32])).
% 1.93/0.61  fof(f32,plain,(
% 1.93/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 1.93/0.61    inference(cnf_transformation,[],[f17])).
% 1.93/0.61  fof(f17,plain,(
% 1.93/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.93/0.61    inference(ennf_transformation,[],[f5])).
% 1.93/0.61  fof(f5,axiom,(
% 1.93/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.93/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.93/0.61  fof(f1005,plain,(
% 1.93/0.61    ( ! [X2] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k2_zfmisc_1(sK0,k3_xboole_0(X2,sK1))) )),
% 1.93/0.61    inference(backward_demodulation,[],[f44,f984])).
% 1.93/0.61  fof(f984,plain,(
% 1.93/0.61    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK0,k3_xboole_0(X1,sK1))) )),
% 1.93/0.61    inference(backward_demodulation,[],[f169,f983])).
% 1.93/0.61  fof(f983,plain,(
% 1.93/0.61    ( ! [X3] : (k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3)) = k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1))) )),
% 1.93/0.61    inference(backward_demodulation,[],[f45,f966])).
% 1.93/0.61  fof(f966,plain,(
% 1.93/0.61    ( ! [X3] : (k3_xboole_0(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1))) )),
% 1.93/0.61    inference(backward_demodulation,[],[f792,f938])).
% 1.93/0.61  fof(f938,plain,(
% 1.93/0.61    sK2 = k3_xboole_0(sK0,sK2)),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f894,f94])).
% 1.93/0.61  fof(f94,plain,(
% 1.93/0.61    ~r1_tarski(sK1,sK3) | sK2 = k3_xboole_0(sK0,sK2)),
% 1.93/0.61    inference(forward_demodulation,[],[f93,f31])).
% 1.93/0.61  fof(f93,plain,(
% 1.93/0.61    ~r1_tarski(sK1,sK3) | sK2 = k3_xboole_0(sK2,sK0)),
% 1.93/0.61    inference(resolution,[],[f87,f32])).
% 1.93/0.61  fof(f792,plain,(
% 1.93/0.61    ( ! [X3] : (k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,sK1))) )),
% 1.93/0.61    inference(backward_demodulation,[],[f479,f766])).
% 1.93/0.61  fof(f766,plain,(
% 1.93/0.61    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f605,f726,f33])).
% 1.93/0.61  fof(f605,plain,(
% 1.93/0.61    ~r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))),
% 1.93/0.61    inference(superposition,[],[f347,f107])).
% 1.93/0.61  fof(f347,plain,(
% 1.93/0.61    ( ! [X0] : (~r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(X0,sK2),sK3))) )),
% 1.93/0.61    inference(superposition,[],[f125,f31])).
% 1.93/0.61  fof(f125,plain,(
% 1.93/0.61    ( ! [X0] : (~r2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k3_xboole_0(sK2,X0),sK3))) )),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f61,f34])).
% 1.93/0.61  fof(f479,plain,(
% 1.93/0.61    ( ! [X3] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k2_zfmisc_1(sK0,k3_xboole_0(X3,sK1))) )),
% 1.93/0.61    inference(forward_demodulation,[],[f478,f36])).
% 1.93/0.61  fof(f478,plain,(
% 1.93/0.61    ( ! [X3] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK0,sK1))) )),
% 1.93/0.61    inference(forward_demodulation,[],[f477,f25])).
% 1.93/0.61  fof(f477,plain,(
% 1.93/0.61    ( ! [X3] : (k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3))) = k3_xboole_0(k2_zfmisc_1(sK0,X3),k2_zfmisc_1(sK2,sK3))) )),
% 1.93/0.61    inference(forward_demodulation,[],[f458,f41])).
% 1.93/0.61  fof(f458,plain,(
% 1.93/0.61    ( ! [X3] : (k2_zfmisc_1(k3_xboole_0(sK0,sK2),k3_xboole_0(X3,sK3)) = k3_xboole_0(k2_zfmisc_1(k3_xboole_0(sK0,sK2),X3),k2_zfmisc_1(sK0,k3_xboole_0(sK1,sK3)))) )),
% 1.93/0.61    inference(superposition,[],[f36,f107])).
% 1.93/0.61  fof(f45,plain,(
% 1.93/0.61    ( ! [X3] : (k2_zfmisc_1(sK2,k3_xboole_0(X3,sK3)) = k3_xboole_0(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1))) )),
% 1.93/0.61    inference(superposition,[],[f36,f25])).
% 1.93/0.61  fof(f169,plain,(
% 1.93/0.61    ( ! [X1] : (k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X1)) = k2_zfmisc_1(sK2,k3_xboole_0(X1,sK3))) )),
% 1.93/0.61    inference(superposition,[],[f45,f31])).
% 1.93/0.61  fof(f44,plain,(
% 1.93/0.61    ( ! [X2] : (k2_zfmisc_1(sK2,k3_xboole_0(sK3,X2)) = k3_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2))) )),
% 1.93/0.61    inference(superposition,[],[f36,f25])).
% 1.93/0.61  fof(f2584,plain,(
% 1.93/0.61    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k1_xboole_0,sK1))),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f27,f2573,f39])).
% 1.93/0.61  fof(f2573,plain,(
% 1.93/0.61    ~r1_tarski(sK0,k1_xboole_0)),
% 1.93/0.61    inference(unit_resulting_resolution,[],[f26,f2038,f33])).
% 1.93/0.61  fof(f2038,plain,(
% 1.93/0.61    ~r2_xboole_0(sK0,k1_xboole_0)),
% 1.93/0.61    inference(subsumption_resolution,[],[f1799,f894])).
% 1.93/0.61  fof(f1799,plain,(
% 1.93/0.61    ~r2_xboole_0(sK0,k1_xboole_0) | ~r1_tarski(sK1,sK3)),
% 1.93/0.61    inference(backward_demodulation,[],[f91,f1774])).
% 1.93/0.61  % SZS output end Proof for theBenchmark
% 1.93/0.61  % (28484)------------------------------
% 1.93/0.61  % (28484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.61  % (28484)Termination reason: Refutation
% 1.93/0.61  
% 1.93/0.61  % (28484)Memory used [KB]: 7803
% 1.93/0.61  % (28484)Time elapsed: 0.127 s
% 1.93/0.61  % (28484)------------------------------
% 1.93/0.61  % (28484)------------------------------
% 1.93/0.61  % (28468)Success in time 0.242 s
%------------------------------------------------------------------------------
