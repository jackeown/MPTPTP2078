%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:28 EST 2020

% Result     : Theorem 11.71s
% Output     : Refutation 12.32s
% Verified   : 
% Statistics : Number of formulae       :  319 (955527 expanded)
%              Number of leaves         :   21 (244751 expanded)
%              Depth                    :   81
%              Number of atoms          :  515 (2297936 expanded)
%              Number of equality atoms :  295 (1849628 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21652,plain,(
    $false ),
    inference(subsumption_resolution,[],[f21651,f19081])).

fof(f19081,plain,(
    sK1 = sK3 ),
    inference(subsumption_resolution,[],[f19077,f18815])).

fof(f18815,plain,(
    r1_tarski(sK1,sK3) ),
    inference(superposition,[],[f40,f18589])).

fof(f18589,plain,(
    sK3 = k2_xboole_0(sK1,sK3) ),
    inference(subsumption_resolution,[],[f18584,f1453])).

fof(f1453,plain,(
    r1_tarski(sK3,k2_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f1438,f34])).

fof(f34,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ( X1 != X3
        | X0 != X2 )
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f1438,plain,
    ( k1_xboole_0 = sK0
    | r1_tarski(sK3,k2_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f1401,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X1,X2)
      | ( ~ r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
        & ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_tarski(X1,X2)
        & ( r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2))
          | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).

fof(f1401,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f226,f138])).

fof(f138,plain,(
    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3) ),
    inference(forward_demodulation,[],[f126,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f126,plain,(
    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK2,sK0),sK3) ),
    inference(superposition,[],[f96,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f96,plain,(
    ! [X0] : k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) ),
    inference(superposition,[],[f59,f33])).

fof(f33,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f26])).

fof(f59,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f226,plain,(
    ! [X3] : r1_tarski(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(k2_xboole_0(X3,sK2),sK3)) ),
    inference(superposition,[],[f40,f97])).

fof(f97,plain,(
    ! [X1] : k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f59,f33])).

fof(f18584,plain,
    ( ~ r1_tarski(sK3,k2_xboole_0(sK1,sK3))
    | sK3 = k2_xboole_0(sK1,sK3) ),
    inference(resolution,[],[f18563,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f18563,plain,(
    r1_tarski(k2_xboole_0(sK1,sK3),sK3) ),
    inference(subsumption_resolution,[],[f18562,f3148])).

fof(f3148,plain,(
    k1_xboole_0 != sK2 ),
    inference(superposition,[],[f3142,f2527])).

fof(f2527,plain,(
    sK2 = k4_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f74,f2472])).

fof(f2472,plain,(
    k1_xboole_0 = k4_xboole_0(sK2,sK2) ),
    inference(forward_demodulation,[],[f2471,f302])).

fof(f302,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f266,f85])).

fof(f85,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f266,plain,(
    ! [X4] : k2_zfmisc_1(X4,sK3) = k4_xboole_0(k2_zfmisc_1(X4,sK3),k1_xboole_0) ),
    inference(forward_demodulation,[],[f251,f248])).

fof(f248,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3)) ),
    inference(resolution,[],[f226,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f251,plain,(
    ! [X4] : k2_zfmisc_1(X4,sK3) = k4_xboole_0(k2_zfmisc_1(X4,sK3),k4_xboole_0(k2_zfmisc_1(X4,sK3),k2_zfmisc_1(k2_xboole_0(X4,sK2),sK3))) ),
    inference(resolution,[],[f226,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f48,f44])).

fof(f44,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f2471,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(sK2,sK2) ),
    inference(subsumption_resolution,[],[f2469,f2354])).

fof(f2354,plain,(
    k1_xboole_0 != sK3 ),
    inference(superposition,[],[f2348,f1474])).

fof(f1474,plain,(
    sK3 = k4_xboole_0(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1471,f1468])).

fof(f1468,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f1453,f54])).

fof(f1471,plain,(
    sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK1,sK3))) ),
    inference(resolution,[],[f1453,f78])).

fof(f2348,plain,(
    k1_xboole_0 != k4_xboole_0(sK3,k1_xboole_0) ),
    inference(forward_demodulation,[],[f2346,f1491])).

fof(f1491,plain,(
    k1_xboole_0 = k4_xboole_0(sK3,sK3) ),
    inference(superposition,[],[f73,f1474])).

fof(f73,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f36,f44])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f2346,plain,(
    k1_xboole_0 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK3)) ),
    inference(resolution,[],[f2345,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f52,f44])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2345,plain,(
    ~ r1_xboole_0(sK3,sK3) ),
    inference(subsumption_resolution,[],[f2337,f35])).

fof(f35,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f26])).

fof(f2337,plain,
    ( ~ r1_xboole_0(sK3,sK3)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f2311,f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f2311,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r1_xboole_0(sK3,sK3) ) ),
    inference(subsumption_resolution,[],[f2303,f34])).

fof(f2303,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK3,sK3)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f1990,f38])).

fof(f1990,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r1_xboole_0(sK3,sK3)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f1926,f87])).

fof(f87,plain,(
    ! [X4,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | r2_hidden(k4_tarski(X4,X5),X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f1926,plain,(
    ! [X17] :
      ( ~ r2_hidden(X17,k2_zfmisc_1(sK0,sK1))
      | ~ r1_xboole_0(sK3,sK3) ) ),
    inference(superposition,[],[f1553,f33])).

fof(f1553,plain,(
    ! [X8,X9] :
      ( ~ r2_hidden(X9,k2_zfmisc_1(X8,sK3))
      | ~ r1_xboole_0(sK3,sK3) ) ),
    inference(resolution,[],[f1527,f89])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1527,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK3)
      | ~ r1_xboole_0(sK3,sK3) ) ),
    inference(forward_demodulation,[],[f1519,f1474])).

fof(f1519,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK3,k1_xboole_0))
      | ~ r1_xboole_0(sK3,sK3) ) ),
    inference(superposition,[],[f77,f1491])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f44])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f2469,plain,
    ( k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(sK2,sK2)
    | k1_xboole_0 = sK3 ),
    inference(backward_demodulation,[],[f2126,f2468])).

fof(f2468,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(forward_demodulation,[],[f2467,f37])).

fof(f37,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f2467,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK2) ),
    inference(subsumption_resolution,[],[f2451,f2354])).

fof(f2451,plain,
    ( k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f72,f2039])).

fof(f2039,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f2035,f78])).

fof(f2035,plain,
    ( r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(subsumption_resolution,[],[f2025,f670])).

fof(f670,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f655,f37])).

fof(f655,plain,(
    k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f72,f198])).

fof(f198,plain,(
    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f188,f184])).

fof(f184,plain,(
    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f73,f156])).

fof(f156,plain,(
    k2_zfmisc_1(sK0,sK1) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f143,f140])).

fof(f140,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3)) ),
    inference(resolution,[],[f134,f54])).

fof(f134,plain,(
    ! [X3] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X3),sK3)) ),
    inference(superposition,[],[f40,f96])).

fof(f143,plain,(
    ! [X3] : k2_zfmisc_1(sK0,sK1) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X3),sK3))) ),
    inference(resolution,[],[f134,f78])).

fof(f188,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f75,f156])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f42,f44,f44])).

fof(f42,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2025,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(k1_xboole_0,sK2)
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f881,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | k1_xboole_0 != k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f881,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK3
    | r1_tarski(k1_xboole_0,sK2) ),
    inference(superposition,[],[f105,f85])).

fof(f105,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_zfmisc_1(X10,sK3),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK3
      | r1_tarski(X10,sK2) ) ),
    inference(superposition,[],[f69,f33])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f43,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f2126,plain,
    ( k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2))
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f75,f2104])).

fof(f2104,plain,
    ( sK2 = k4_xboole_0(sK2,k1_xboole_0)
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f74,f2081])).

fof(f2081,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | k1_xboole_0 = sK3 ),
    inference(duplicate_literal_removal,[],[f2075])).

fof(f2075,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,sK2)
    | k1_xboole_0 = sK3
    | k1_xboole_0 = sK3 ),
    inference(superposition,[],[f732,f2040])).

fof(f2040,plain,
    ( sK2 = k2_xboole_0(k1_xboole_0,sK2)
    | k1_xboole_0 = sK3 ),
    inference(resolution,[],[f2035,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f732,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(X0,sK2))
      | k1_xboole_0 = sK3 ) ),
    inference(resolution,[],[f691,f54])).

fof(f691,plain,(
    ! [X1] :
      ( r1_tarski(sK2,k2_xboole_0(X1,sK2))
      | k1_xboole_0 = sK3 ) ),
    inference(resolution,[],[f104,f150])).

fof(f150,plain,(
    ! [X1] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3)) ),
    inference(superposition,[],[f134,f41])).

fof(f104,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK3))
      | k1_xboole_0 = sK3
      | r1_tarski(sK2,X9) ) ),
    inference(superposition,[],[f69,f33])).

fof(f74,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f39,f44])).

fof(f39,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f3142,plain,(
    k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3140,f2472])).

fof(f3140,plain,(
    k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2)) ),
    inference(resolution,[],[f3139,f80])).

fof(f3139,plain,(
    ~ r1_xboole_0(sK2,sK2) ),
    inference(subsumption_resolution,[],[f3131,f35])).

fof(f3131,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | k1_xboole_0 = sK1 ),
    inference(resolution,[],[f3130,f38])).

fof(f3130,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | ~ r1_xboole_0(sK2,sK2) ) ),
    inference(subsumption_resolution,[],[f3122,f34])).

fof(f3122,plain,(
    ! [X0] :
      ( ~ r1_xboole_0(sK2,sK2)
      | ~ r2_hidden(X0,sK1)
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f2984,f38])).

fof(f2984,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK0)
      | ~ r1_xboole_0(sK2,sK2)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f2853,f87])).

fof(f2853,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k2_zfmisc_1(sK0,sK1))
      | ~ r1_xboole_0(sK2,sK2) ) ),
    inference(superposition,[],[f2660,f33])).

fof(f2660,plain,(
    ! [X6,X7] :
      ( ~ r2_hidden(X7,k2_zfmisc_1(sK2,X6))
      | ~ r1_xboole_0(sK2,sK2) ) ),
    inference(resolution,[],[f2558,f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
      | ~ r2_hidden(X3,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(sK7(X0,X1,X3),X0)
      | ~ r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2558,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r1_xboole_0(sK2,sK2) ) ),
    inference(subsumption_resolution,[],[f2546,f2354])).

fof(f2546,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2)
      | ~ r1_xboole_0(sK2,sK2)
      | k1_xboole_0 = sK3 ) ),
    inference(backward_demodulation,[],[f2108,f2527])).

fof(f2108,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k4_xboole_0(sK2,k1_xboole_0))
      | ~ r1_xboole_0(sK2,sK2)
      | k1_xboole_0 = sK3 ) ),
    inference(superposition,[],[f77,f2081])).

fof(f18562,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(k2_xboole_0(sK1,sK3),sK3) ),
    inference(subsumption_resolution,[],[f18484,f83])).

fof(f83,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f18484,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | r1_tarski(k2_xboole_0(sK1,sK3),sK3) ),
    inference(superposition,[],[f107,f18012])).

fof(f18012,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(backward_demodulation,[],[f397,f17972])).

fof(f17972,plain,(
    sK0 = k2_xboole_0(sK0,sK2) ),
    inference(superposition,[],[f17942,f41])).

fof(f17942,plain,(
    sK0 = k2_xboole_0(sK2,sK0) ),
    inference(resolution,[],[f17937,f47])).

fof(f17937,plain,(
    r1_tarski(sK2,sK0) ),
    inference(trivial_inequality_removal,[],[f17933])).

fof(f17933,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_tarski(sK2,sK0) ),
    inference(superposition,[],[f17814,f184])).

fof(f17814,plain,(
    ! [X6] :
      ( k1_xboole_0 != k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X6,sK1))
      | r1_tarski(sK2,X6) ) ),
    inference(subsumption_resolution,[],[f17810,f2354])).

fof(f17810,plain,(
    ! [X6] :
      ( k1_xboole_0 != k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X6,sK1))
      | r1_tarski(sK2,X6)
      | k1_xboole_0 = sK3 ) ),
    inference(backward_demodulation,[],[f694,f17809])).

fof(f17809,plain,(
    ! [X0] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1)) ),
    inference(forward_demodulation,[],[f17791,f13101])).

fof(f13101,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X3)) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X4)),X3)) ),
    inference(superposition,[],[f72,f12172])).

fof(f12172,plain,(
    ! [X14,X15,X16] : k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),X14) = k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,X14))) ),
    inference(forward_demodulation,[],[f12167,f12121])).

fof(f12121,plain,(
    ! [X3] : k4_xboole_0(X3,k1_xboole_0) = X3 ),
    inference(forward_demodulation,[],[f12113,f12110])).

fof(f12110,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK0,sK2),X0)) ),
    inference(resolution,[],[f12106,f54])).

fof(f12106,plain,(
    ! [X0] : r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK0,sK2),X0)) ),
    inference(subsumption_resolution,[],[f12080,f2354])).

fof(f12080,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK3
      | r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK0,sK2),X0)) ) ),
    inference(resolution,[],[f12066,f69])).

fof(f12066,plain,(
    ! [X1] : r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k2_xboole_0(k2_xboole_0(sK0,sK2),X1),sK3)) ),
    inference(superposition,[],[f11972,f41])).

fof(f11972,plain,(
    ! [X3] : r1_tarski(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(k2_xboole_0(X3,k2_xboole_0(sK0,sK2)),sK3)) ),
    inference(superposition,[],[f40,f1416])).

fof(f1416,plain,(
    ! [X1] : k2_zfmisc_1(k2_xboole_0(X1,k2_xboole_0(sK0,sK2)),sK3) = k2_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f59,f138])).

fof(f12113,plain,(
    ! [X3] : k4_xboole_0(X3,k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(sK0,sK2),X3))) = X3 ),
    inference(resolution,[],[f12106,f78])).

fof(f12167,plain,(
    ! [X14,X15,X16] : k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X14,k1_xboole_0)) = k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,X14))) ),
    inference(superposition,[],[f81,f12122])).

fof(f12122,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f73,f12121])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) ),
    inference(definition_unfolding,[],[f71,f44,f44,f44])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f17791,plain,(
    ! [X0] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK1)) ),
    inference(backward_demodulation,[],[f17017,f17788])).

fof(f17788,plain,(
    ! [X23] : k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X23)),sK3) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X23)),sK1) ),
    inference(forward_demodulation,[],[f17780,f8040])).

fof(f8040,plain,(
    ! [X4,X3] : k4_xboole_0(k2_zfmisc_1(X3,sK1),k4_xboole_0(k2_zfmisc_1(X3,sK1),k2_zfmisc_1(X4,sK1))) = k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X4)),sK1) ),
    inference(forward_demodulation,[],[f8035,f8026])).

fof(f8026,plain,(
    sK1 = k4_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f74,f8004])).

fof(f8004,plain,(
    k1_xboole_0 = k4_xboole_0(sK1,sK1) ),
    inference(backward_demodulation,[],[f7971,f7977])).

fof(f7977,plain,(
    sK1 = k2_xboole_0(sK1,sK1) ),
    inference(subsumption_resolution,[],[f7972,f40])).

fof(f7972,plain,
    ( ~ r1_tarski(sK1,k2_xboole_0(sK1,sK1))
    | sK1 = k2_xboole_0(sK1,sK1) ),
    inference(resolution,[],[f7954,f51])).

fof(f7954,plain,(
    r1_tarski(k2_xboole_0(sK1,sK1),sK1) ),
    inference(resolution,[],[f5163,f83])).

fof(f5163,plain,(
    ! [X11] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X11))
      | r1_tarski(k2_xboole_0(sK1,sK1),X11) ) ),
    inference(subsumption_resolution,[],[f5154,f34])).

fof(f5154,plain,(
    ! [X11] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X11))
      | k1_xboole_0 = sK0
      | r1_tarski(k2_xboole_0(sK1,sK1),X11) ) ),
    inference(superposition,[],[f70,f4967])).

fof(f4967,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f4952,f33])).

fof(f4952,plain,(
    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)) ),
    inference(backward_demodulation,[],[f393,f4951])).

fof(f4951,plain,(
    sK3 = k2_xboole_0(sK3,sK3) ),
    inference(subsumption_resolution,[],[f4934,f3148])).

fof(f4934,plain,
    ( sK3 = k2_xboole_0(sK3,sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f4895,f2330])).

fof(f2330,plain,
    ( sK3 = k2_xboole_0(k1_xboole_0,sK3)
    | k1_xboole_0 = sK2 ),
    inference(resolution,[],[f2325,f47])).

fof(f2325,plain,
    ( r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f2315,f670])).

fof(f2315,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(k1_xboole_0,sK3)
    | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f1117,f55])).

fof(f1117,plain,
    ( ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | r1_tarski(k1_xboole_0,sK3) ),
    inference(superposition,[],[f107,f84])).

fof(f84,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X1
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f4895,plain,(
    sK3 = k2_xboole_0(k2_xboole_0(k1_xboole_0,sK3),sK3) ),
    inference(resolution,[],[f4890,f47])).

fof(f4890,plain,(
    r1_tarski(k2_xboole_0(k1_xboole_0,sK3),sK3) ),
    inference(forward_demodulation,[],[f4889,f41])).

fof(f4889,plain,(
    r1_tarski(k2_xboole_0(sK3,k1_xboole_0),sK3) ),
    inference(subsumption_resolution,[],[f4887,f3148])).

fof(f4887,plain,
    ( r1_tarski(k2_xboole_0(sK3,k1_xboole_0),sK3)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f4867,f2330])).

fof(f4867,plain,(
    ! [X0] : r1_tarski(k2_xboole_0(sK3,X0),k2_xboole_0(X0,sK3)) ),
    inference(subsumption_resolution,[],[f4839,f3148])).

fof(f4839,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | r1_tarski(k2_xboole_0(sK3,X0),k2_xboole_0(X0,sK3)) ) ),
    inference(resolution,[],[f4224,f70])).

fof(f4224,plain,(
    ! [X8] : r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X8)),k2_zfmisc_1(sK2,k2_xboole_0(X8,sK3))) ),
    inference(forward_demodulation,[],[f4223,f4207])).

fof(f4207,plain,(
    ! [X7] : k2_zfmisc_1(sK2,k2_xboole_0(X7,sK3)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(X7,sK3))) ),
    inference(forward_demodulation,[],[f4206,f4201])).

fof(f4201,plain,(
    ! [X3] : k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X3))) ),
    inference(forward_demodulation,[],[f4126,f482])).

fof(f482,plain,(
    ! [X4] : k2_zfmisc_1(sK2,k2_xboole_0(X4,sK3)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X4,sK3))) ),
    inference(resolution,[],[f471,f47])).

fof(f471,plain,(
    ! [X1] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X1,sK3))) ),
    inference(superposition,[],[f392,f41])).

fof(f392,plain,(
    ! [X3] : r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X3))) ),
    inference(superposition,[],[f40,f98])).

fof(f98,plain,(
    ! [X2] : k2_zfmisc_1(sK2,k2_xboole_0(sK3,X2)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) ),
    inference(superposition,[],[f60,f33])).

fof(f4126,plain,(
    ! [X3] : k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X3))) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3))) ),
    inference(superposition,[],[f98,f2749])).

fof(f2749,plain,(
    ! [X1] : k2_zfmisc_1(sK2,k2_xboole_0(sK3,X1)) = k2_zfmisc_1(sK2,k2_xboole_0(X1,sK3)) ),
    inference(superposition,[],[f508,f98])).

fof(f508,plain,(
    ! [X2] : k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) = k2_zfmisc_1(sK2,k2_xboole_0(X2,sK3)) ),
    inference(superposition,[],[f99,f41])).

fof(f99,plain,(
    ! [X3] : k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f60,f33])).

fof(f4206,plain,(
    ! [X7] : k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(X7,sK3))) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X7))) ),
    inference(forward_demodulation,[],[f4205,f41])).

fof(f4205,plain,(
    ! [X7] : k2_zfmisc_1(sK2,k2_xboole_0(k2_xboole_0(sK3,X7),sK3)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(X7,sK3))) ),
    inference(forward_demodulation,[],[f4130,f98])).

fof(f4130,plain,(
    ! [X7] : k2_zfmisc_1(sK2,k2_xboole_0(k2_xboole_0(sK3,X7),sK3)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X7,sK3))) ),
    inference(superposition,[],[f508,f2749])).

fof(f4223,plain,(
    ! [X8] : r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X8)),k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(X8,sK3)))) ),
    inference(forward_demodulation,[],[f4170,f2749])).

fof(f4170,plain,(
    ! [X8] : r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X8)),k2_zfmisc_1(sK2,k2_xboole_0(k2_xboole_0(X8,sK3),sK3))) ),
    inference(superposition,[],[f515,f2749])).

fof(f515,plain,(
    ! [X3] : r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3))) ),
    inference(superposition,[],[f40,f99])).

fof(f393,plain,(
    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK3)) ),
    inference(forward_demodulation,[],[f380,f60])).

fof(f380,plain,(
    k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK3)) ),
    inference(superposition,[],[f98,f33])).

fof(f7971,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK1),sK1) ),
    inference(resolution,[],[f7954,f54])).

fof(f8035,plain,(
    ! [X4,X3] : k4_xboole_0(k2_zfmisc_1(X3,sK1),k4_xboole_0(k2_zfmisc_1(X3,sK1),k2_zfmisc_1(X4,sK1))) = k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(superposition,[],[f81,f8004])).

fof(f17780,plain,(
    ! [X23] : k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X23)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,sK1))) ),
    inference(backward_demodulation,[],[f17748,f17764])).

fof(f17764,plain,(
    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(subsumption_resolution,[],[f17756,f17739])).

fof(f17739,plain,(
    r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(subsumption_resolution,[],[f17697,f83])).

fof(f17697,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(superposition,[],[f7987,f17077])).

fof(f17077,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) ),
    inference(forward_demodulation,[],[f17076,f75])).

fof(f17076,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) ),
    inference(forward_demodulation,[],[f17075,f17053])).

fof(f17053,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3) ),
    inference(forward_demodulation,[],[f17052,f12121])).

fof(f17052,plain,(
    k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),sK1) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3) ),
    inference(forward_demodulation,[],[f17051,f12122])).

fof(f17051,plain,(
    k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)),sK1) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3) ),
    inference(forward_demodulation,[],[f17050,f12158])).

fof(f12158,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,k2_xboole_0(X14,sK3)))) = k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),X14) ),
    inference(subsumption_resolution,[],[f12140,f3148])).

fof(f12140,plain,(
    ! [X14,X15,X16] :
      ( k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,k2_xboole_0(X14,sK3)))) = k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),X14)
      | k1_xboole_0 = sK2 ) ),
    inference(backward_demodulation,[],[f1137,f12121])).

fof(f1137,plain,(
    ! [X14,X15,X16] :
      ( k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X14,k1_xboole_0)) = k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,k2_xboole_0(X14,sK3))))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f81,f1056])).

fof(f1056,plain,(
    ! [X1] :
      ( k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,sK3))
      | k1_xboole_0 = sK2 ) ),
    inference(superposition,[],[f564,f41])).

fof(f564,plain,(
    ! [X0] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(sK3,X0))
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f542,f54])).

fof(f542,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_xboole_0(sK3,X0))
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f534,f70])).

fof(f534,plain,(
    ! [X1] : r1_tarski(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X1))) ),
    inference(superposition,[],[f515,f41])).

fof(f17050,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3) ),
    inference(forward_demodulation,[],[f17049,f75])).

fof(f17049,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) ),
    inference(forward_demodulation,[],[f16999,f13127])).

fof(f13127,plain,(
    ! [X21] : k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,k2_xboole_0(sK0,sK2))),sK3) = k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,sK0)),sK3) ),
    inference(forward_demodulation,[],[f13078,f1617])).

fof(f1617,plain,(
    ! [X4,X3] : k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X4)),sK3) = k4_xboole_0(k2_zfmisc_1(X3,sK3),k4_xboole_0(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(X4,k2_xboole_0(sK1,sK3)))) ),
    inference(forward_demodulation,[],[f1612,f1474])).

fof(f1612,plain,(
    ! [X4,X3] : k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(k2_zfmisc_1(X3,sK3),k4_xboole_0(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(X4,k2_xboole_0(sK1,sK3)))) ),
    inference(superposition,[],[f81,f1468])).

fof(f13078,plain,(
    ! [X21] : k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,k2_xboole_0(sK0,sK2))),sK3) = k4_xboole_0(k2_zfmisc_1(X21,sK3),k4_xboole_0(k2_zfmisc_1(X21,sK3),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) ),
    inference(superposition,[],[f12172,f138])).

fof(f16999,plain,(
    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK2))),sK3) ),
    inference(superposition,[],[f13069,f138])).

fof(f13069,plain,(
    ! [X33] : k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X33)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X33,sK3))) ),
    inference(superposition,[],[f12172,f33])).

fof(f17075,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3) ),
    inference(forward_demodulation,[],[f17007,f75])).

fof(f17007,plain,(
    k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3) ),
    inference(superposition,[],[f13069,f12842])).

fof(f12842,plain,(
    ! [X10,X11,X9] : k4_xboole_0(k2_zfmisc_1(X9,X11),k4_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X9,X10))) = k2_zfmisc_1(X9,k4_xboole_0(X10,k4_xboole_0(X10,X11))) ),
    inference(superposition,[],[f12171,f75])).

fof(f12171,plain,(
    ! [X12,X13,X11] : k2_zfmisc_1(X11,k4_xboole_0(X12,k4_xboole_0(X12,X13))) = k4_xboole_0(k2_zfmisc_1(X11,X12),k4_xboole_0(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X11,X13))) ),
    inference(forward_demodulation,[],[f12166,f12121])).

fof(f12166,plain,(
    ! [X12,X13,X11] : k2_zfmisc_1(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(X12,k4_xboole_0(X12,X13))) = k4_xboole_0(k2_zfmisc_1(X11,X12),k4_xboole_0(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X11,X13))) ),
    inference(superposition,[],[f81,f12122])).

fof(f7987,plain,(
    ! [X11] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X11))
      | r1_tarski(sK1,X11) ) ),
    inference(backward_demodulation,[],[f5163,f7977])).

fof(f17756,plain,
    ( ~ r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))
    | sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)) ),
    inference(resolution,[],[f17738,f51])).

fof(f17738,plain,(
    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),sK1) ),
    inference(subsumption_resolution,[],[f17696,f83])).

fof(f17696,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),sK1) ),
    inference(superposition,[],[f7988,f17077])).

fof(f7988,plain,(
    ! [X12] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(X12,sK1) ) ),
    inference(backward_demodulation,[],[f5164,f7977])).

fof(f5164,plain,(
    ! [X12] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(X12,k2_xboole_0(sK1,sK1)) ) ),
    inference(subsumption_resolution,[],[f5155,f34])).

fof(f5155,plain,(
    ! [X12] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK0
      | r1_tarski(X12,k2_xboole_0(sK1,sK1)) ) ),
    inference(superposition,[],[f70,f4967])).

fof(f17748,plain,(
    ! [X23] : k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X23)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))))) ),
    inference(forward_demodulation,[],[f17747,f13069])).

fof(f17747,plain,(
    ! [X23] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,sK3))) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))))) ),
    inference(forward_demodulation,[],[f17719,f81])).

fof(f17719,plain,(
    ! [X23] : k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X23)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))))) ),
    inference(superposition,[],[f12172,f17077])).

fof(f17017,plain,(
    ! [X0] : k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK3)) ),
    inference(superposition,[],[f72,f13069])).

fof(f694,plain,(
    ! [X6] :
      ( k1_xboole_0 != k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X6,sK3))
      | r1_tarski(sK2,X6)
      | k1_xboole_0 = sK3 ) ),
    inference(resolution,[],[f104,f55])).

fof(f397,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3)) ),
    inference(forward_demodulation,[],[f387,f41])).

fof(f387,plain,(
    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK1)) ),
    inference(superposition,[],[f98,f59])).

fof(f107,plain,(
    ! [X12] :
      ( ~ r1_tarski(k2_zfmisc_1(sK2,X12),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = sK2
      | r1_tarski(X12,sK3) ) ),
    inference(superposition,[],[f70,f33])).

fof(f40,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f19077,plain,
    ( ~ r1_tarski(sK1,sK3)
    | sK1 = sK3 ),
    inference(resolution,[],[f18941,f51])).

fof(f18941,plain,(
    r1_tarski(sK3,sK1) ),
    inference(subsumption_resolution,[],[f18940,f3148])).

fof(f18940,plain,
    ( k1_xboole_0 = sK2
    | r1_tarski(sK3,sK1) ),
    inference(subsumption_resolution,[],[f18864,f83])).

fof(f18864,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK2
    | r1_tarski(sK3,sK1) ),
    inference(superposition,[],[f106,f17860])).

fof(f17860,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1) ),
    inference(forward_demodulation,[],[f17859,f12121])).

fof(f17859,plain,(
    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k1_xboole_0)) ),
    inference(forward_demodulation,[],[f17833,f12122])).

fof(f17833,plain,(
    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f17409,f17764])).

fof(f17409,plain,(
    ! [X33] : k2_zfmisc_1(sK2,k4_xboole_0(X33,k4_xboole_0(X33,sK3))) = k2_zfmisc_1(sK0,k4_xboole_0(X33,k4_xboole_0(X33,sK1))) ),
    inference(backward_demodulation,[],[f12828,f17395])).

fof(f17395,plain,(
    ! [X29] : k2_zfmisc_1(sK0,k4_xboole_0(X29,k4_xboole_0(X29,sK1))) = k4_xboole_0(k2_zfmisc_1(sK2,X29),k4_xboole_0(k2_zfmisc_1(sK2,X29),k2_zfmisc_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f17255,f17376])).

fof(f17376,plain,(
    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(subsumption_resolution,[],[f17368,f17231])).

fof(f17231,plain,(
    r1_tarski(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f17230,f2354])).

fof(f17230,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(subsumption_resolution,[],[f17149,f83])).

fof(f17149,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK3
    | r1_tarski(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(superposition,[],[f104,f17053])).

fof(f17368,plain,
    ( ~ r1_tarski(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)) ),
    inference(resolution,[],[f17233,f51])).

fof(f17233,plain,(
    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f17232,f2354])).

fof(f17232,plain,
    ( k1_xboole_0 = sK3
    | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK2) ),
    inference(subsumption_resolution,[],[f17150,f83])).

fof(f17150,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | k1_xboole_0 = sK3
    | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK2) ),
    inference(superposition,[],[f105,f17053])).

fof(f17255,plain,(
    ! [X29] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k2_zfmisc_1(sK0,sK1))) = k2_zfmisc_1(sK0,k4_xboole_0(X29,k4_xboole_0(X29,sK1))) ),
    inference(forward_demodulation,[],[f17254,f9226])).

fof(f9226,plain,(
    ! [X2,X1] : k4_xboole_0(k2_zfmisc_1(sK0,X1),k4_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK0,X2))) = k2_zfmisc_1(sK0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(forward_demodulation,[],[f9221,f9213])).

fof(f9213,plain,(
    sK0 = k4_xboole_0(sK0,k1_xboole_0) ),
    inference(superposition,[],[f74,f9189])).

fof(f9189,plain,(
    k1_xboole_0 = k4_xboole_0(sK0,sK0) ),
    inference(backward_demodulation,[],[f9172,f9178])).

fof(f9178,plain,(
    sK0 = k2_xboole_0(sK0,sK0) ),
    inference(subsumption_resolution,[],[f9173,f40])).

fof(f9173,plain,
    ( ~ r1_tarski(sK0,k2_xboole_0(sK0,sK0))
    | sK0 = k2_xboole_0(sK0,sK0) ),
    inference(resolution,[],[f9167,f51])).

fof(f9167,plain,(
    r1_tarski(k2_xboole_0(sK0,sK0),sK0) ),
    inference(subsumption_resolution,[],[f9148,f83])).

fof(f9148,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(k2_xboole_0(sK0,sK0),sK0) ),
    inference(superposition,[],[f8008,f9138])).

fof(f9138,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(sK0,sK0),sK1) ),
    inference(superposition,[],[f4986,f59])).

fof(f4986,plain,(
    k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1339,f4967])).

fof(f1339,plain,(
    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1))) ),
    inference(resolution,[],[f1325,f47])).

fof(f1325,plain,(
    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1))) ),
    inference(forward_demodulation,[],[f1293,f33])).

fof(f1293,plain,(
    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1))) ),
    inference(superposition,[],[f260,f137])).

fof(f137,plain,(
    k2_zfmisc_1(k2_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)) ),
    inference(forward_demodulation,[],[f125,f60])).

fof(f125,plain,(
    k2_zfmisc_1(k2_xboole_0(sK2,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) ),
    inference(superposition,[],[f96,f33])).

fof(f260,plain,(
    ! [X1] : r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3)) ),
    inference(superposition,[],[f226,f41])).

fof(f8008,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_zfmisc_1(X10,sK1),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(X10,sK0) ) ),
    inference(forward_demodulation,[],[f8007,f7977])).

fof(f8007,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_zfmisc_1(X10,k2_xboole_0(sK1,sK1)),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(X10,sK0) ) ),
    inference(subsumption_resolution,[],[f7983,f35])).

fof(f7983,plain,(
    ! [X10] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_zfmisc_1(X10,k2_xboole_0(sK1,sK1)),k2_zfmisc_1(sK0,sK1))
      | r1_tarski(X10,sK0) ) ),
    inference(backward_demodulation,[],[f5153,f7977])).

fof(f5153,plain,(
    ! [X10] :
      ( ~ r1_tarski(k2_zfmisc_1(X10,k2_xboole_0(sK1,sK1)),k2_zfmisc_1(sK0,sK1))
      | k1_xboole_0 = k2_xboole_0(sK1,sK1)
      | r1_tarski(X10,sK0) ) ),
    inference(superposition,[],[f69,f4967])).

fof(f9172,plain,(
    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK0),sK0) ),
    inference(resolution,[],[f9167,f54])).

fof(f9221,plain,(
    ! [X2,X1] : k4_xboole_0(k2_zfmisc_1(sK0,X1),k4_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK0,X2))) = k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,X2))) ),
    inference(superposition,[],[f81,f9189])).

fof(f17254,plain,(
    ! [X29] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(sK0,X29),k4_xboole_0(k2_zfmisc_1(sK0,X29),k2_zfmisc_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f17253,f33])).

fof(f17253,plain,(
    ! [X29] : k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(sK0,X29),k4_xboole_0(k2_zfmisc_1(sK0,X29),k2_zfmisc_1(sK2,sK3))) ),
    inference(forward_demodulation,[],[f17205,f81])).

fof(f17205,plain,(
    ! [X29] : k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(X29,k4_xboole_0(X29,sK3))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f12171,f17053])).

fof(f12828,plain,(
    ! [X33] : k2_zfmisc_1(sK2,k4_xboole_0(X33,k4_xboole_0(X33,sK3))) = k4_xboole_0(k2_zfmisc_1(sK2,X33),k4_xboole_0(k2_zfmisc_1(sK2,X33),k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f12171,f33])).

fof(f106,plain,(
    ! [X11] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X11))
      | k1_xboole_0 = sK2
      | r1_tarski(sK3,X11) ) ),
    inference(superposition,[],[f70,f33])).

fof(f21651,plain,(
    sK1 != sK3 ),
    inference(trivial_inequality_removal,[],[f20630])).

fof(f20630,plain,
    ( sK0 != sK0
    | sK1 != sK3 ),
    inference(backward_demodulation,[],[f32,f20624])).

fof(f20624,plain,(
    sK0 = sK2 ),
    inference(resolution,[],[f18944,f17939])).

fof(f17939,plain,
    ( ~ r1_tarski(sK0,sK2)
    | sK0 = sK2 ),
    inference(resolution,[],[f17937,f51])).

fof(f18944,plain,(
    r1_tarski(sK0,sK2) ),
    inference(subsumption_resolution,[],[f18896,f83])).

fof(f18896,plain,
    ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))
    | r1_tarski(sK0,sK2) ),
    inference(superposition,[],[f8006,f17860])).

fof(f8006,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK1))
      | r1_tarski(sK0,X9) ) ),
    inference(forward_demodulation,[],[f8005,f7977])).

fof(f8005,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,k2_xboole_0(sK1,sK1)))
      | r1_tarski(sK0,X9) ) ),
    inference(subsumption_resolution,[],[f7982,f35])).

fof(f7982,plain,(
    ! [X9] :
      ( k1_xboole_0 = sK1
      | ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,k2_xboole_0(sK1,sK1)))
      | r1_tarski(sK0,X9) ) ),
    inference(backward_demodulation,[],[f5152,f7977])).

fof(f5152,plain,(
    ! [X9] :
      ( ~ r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,k2_xboole_0(sK1,sK1)))
      | k1_xboole_0 = k2_xboole_0(sK1,sK1)
      | r1_tarski(sK0,X9) ) ),
    inference(superposition,[],[f69,f4967])).

fof(f32,plain,
    ( sK1 != sK3
    | sK0 != sK2 ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:22:09 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (8385)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (8374)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (8396)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (8375)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (8400)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (8371)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (8388)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (8376)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (8388)Refutation not found, incomplete strategy% (8388)------------------------------
% 0.21/0.52  % (8388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (8388)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (8388)Memory used [KB]: 10618
% 0.21/0.52  % (8388)Time elapsed: 0.102 s
% 0.21/0.52  % (8388)------------------------------
% 0.21/0.52  % (8388)------------------------------
% 0.21/0.52  % (8373)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (8379)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (8395)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (8384)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (8383)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.34/0.54  % (8401)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.34/0.54  % (8377)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.34/0.54  % (8394)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.34/0.54  % (8401)Refutation not found, incomplete strategy% (8401)------------------------------
% 1.34/0.54  % (8401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.54  % (8401)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.54  
% 1.34/0.54  % (8401)Memory used [KB]: 1663
% 1.34/0.54  % (8401)Time elapsed: 0.128 s
% 1.34/0.54  % (8401)------------------------------
% 1.34/0.54  % (8401)------------------------------
% 1.34/0.54  % (8378)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.34/0.54  % (8393)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.34/0.54  % (8397)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.34/0.54  % (8392)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.34/0.55  % (8372)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.34/0.55  % (8372)Refutation not found, incomplete strategy% (8372)------------------------------
% 1.34/0.55  % (8372)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.34/0.55  % (8372)Termination reason: Refutation not found, incomplete strategy
% 1.34/0.55  
% 1.34/0.55  % (8372)Memory used [KB]: 1663
% 1.34/0.55  % (8372)Time elapsed: 0.126 s
% 1.34/0.55  % (8372)------------------------------
% 1.34/0.55  % (8372)------------------------------
% 1.34/0.55  % (8387)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.48/0.55  % (8399)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.48/0.55  % (8382)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.48/0.56  % (8386)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.48/0.56  % (8390)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.48/0.56  % (8389)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.48/0.56  % (8398)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.48/0.57  % (8391)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.48/0.57  % (8380)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.99/0.66  % (8374)Refutation not found, incomplete strategy% (8374)------------------------------
% 1.99/0.66  % (8374)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.99/0.66  % (8493)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.99/0.66  % (8374)Termination reason: Refutation not found, incomplete strategy
% 1.99/0.66  
% 1.99/0.66  % (8374)Memory used [KB]: 6268
% 1.99/0.66  % (8374)Time elapsed: 0.241 s
% 1.99/0.66  % (8374)------------------------------
% 1.99/0.66  % (8374)------------------------------
% 1.99/0.67  % (8498)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.34/0.70  % (8502)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.84/0.76  % (8528)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 3.37/0.83  % (8396)Time limit reached!
% 3.37/0.83  % (8396)------------------------------
% 3.37/0.83  % (8396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.83  % (8396)Termination reason: Time limit
% 3.37/0.83  
% 3.37/0.83  % (8396)Memory used [KB]: 13560
% 3.37/0.83  % (8396)Time elapsed: 0.414 s
% 3.37/0.83  % (8396)------------------------------
% 3.37/0.83  % (8396)------------------------------
% 3.37/0.83  % (8373)Time limit reached!
% 3.37/0.83  % (8373)------------------------------
% 3.37/0.83  % (8373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.37/0.83  % (8373)Termination reason: Time limit
% 3.37/0.83  % (8373)Termination phase: Saturation
% 3.37/0.83  
% 3.37/0.83  % (8373)Memory used [KB]: 6780
% 3.37/0.83  % (8373)Time elapsed: 0.400 s
% 3.37/0.83  % (8373)------------------------------
% 3.37/0.83  % (8373)------------------------------
% 4.05/0.93  % (8377)Time limit reached!
% 4.05/0.93  % (8377)------------------------------
% 4.05/0.93  % (8377)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.94  % (8386)Time limit reached!
% 4.05/0.94  % (8386)------------------------------
% 4.05/0.94  % (8386)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.05/0.94  % (8386)Termination reason: Time limit
% 4.05/0.94  
% 4.05/0.94  % (8386)Memory used [KB]: 4349
% 4.05/0.94  % (8386)Time elapsed: 0.521 s
% 4.05/0.94  % (8386)------------------------------
% 4.05/0.94  % (8386)------------------------------
% 4.05/0.96  % (8377)Termination reason: Time limit
% 4.05/0.96  
% 4.05/0.96  % (8377)Memory used [KB]: 16630
% 4.05/0.96  % (8377)Time elapsed: 0.524 s
% 4.05/0.96  % (8377)------------------------------
% 4.05/0.96  % (8377)------------------------------
% 4.05/0.97  % (8588)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 4.32/0.98  % (8589)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 4.76/1.05  % (8590)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 4.76/1.05  % (8378)Time limit reached!
% 4.76/1.05  % (8378)------------------------------
% 4.76/1.05  % (8378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.76/1.06  % (8378)Termination reason: Time limit
% 4.76/1.06  
% 4.76/1.06  % (8378)Memory used [KB]: 6524
% 4.76/1.06  % (8378)Time elapsed: 0.605 s
% 4.76/1.06  % (8378)------------------------------
% 4.76/1.06  % (8378)------------------------------
% 4.76/1.07  % (8591)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 6.27/1.18  % (8592)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 7.95/1.38  % (8502)Time limit reached!
% 7.95/1.38  % (8502)------------------------------
% 7.95/1.38  % (8502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.39  % (8502)Termination reason: Time limit
% 7.95/1.39  % (8502)Termination phase: Saturation
% 7.95/1.39  
% 7.95/1.39  % (8502)Memory used [KB]: 13816
% 7.95/1.39  % (8502)Time elapsed: 0.800 s
% 7.95/1.39  % (8502)------------------------------
% 7.95/1.39  % (8502)------------------------------
% 7.95/1.41  % (8384)Time limit reached!
% 7.95/1.41  % (8384)------------------------------
% 7.95/1.41  % (8384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.41  % (8384)Termination reason: Time limit
% 7.95/1.41  
% 7.95/1.41  % (8384)Memory used [KB]: 15607
% 7.95/1.41  % (8384)Time elapsed: 1.011 s
% 7.95/1.41  % (8384)------------------------------
% 7.95/1.41  % (8384)------------------------------
% 7.95/1.43  % (8399)Time limit reached!
% 7.95/1.43  % (8399)------------------------------
% 7.95/1.43  % (8399)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.95/1.43  % (8399)Termination reason: Time limit
% 7.95/1.43  % (8399)Termination phase: Saturation
% 7.95/1.43  
% 7.95/1.43  % (8399)Memory used [KB]: 14200
% 7.95/1.43  % (8399)Time elapsed: 1.0000 s
% 7.95/1.43  % (8399)------------------------------
% 7.95/1.43  % (8399)------------------------------
% 8.63/1.52  % (8593)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_4 on theBenchmark
% 9.13/1.55  % (8594)lrs+1010_3:2_afr=on:afp=100000:afq=1.1:anc=none:gsp=input_only:irw=on:lwlo=on:nm=2:newcnf=on:nwc=1.7:stl=30:sac=on:sp=occurrence_95 on theBenchmark
% 9.43/1.56  % (8595)lrs+1010_2_add=large:afp=4000:afq=2.0:amm=off:bd=off:bs=unit_only:bsr=on:br=off:fsr=off:gs=on:gsem=off:irw=on:lma=on:nm=32:nwc=1.1:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_80 on theBenchmark
% 9.43/1.61  % (8590)Time limit reached!
% 9.43/1.61  % (8590)------------------------------
% 9.43/1.61  % (8590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.43/1.62  % (8590)Termination reason: Time limit
% 9.43/1.62  
% 9.43/1.62  % (8590)Memory used [KB]: 20340
% 9.43/1.62  % (8590)Time elapsed: 0.634 s
% 9.43/1.62  % (8590)------------------------------
% 9.43/1.62  % (8590)------------------------------
% 10.12/1.65  % (8371)Time limit reached!
% 10.12/1.65  % (8371)------------------------------
% 10.12/1.65  % (8371)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.12/1.65  % (8371)Termination reason: Time limit
% 10.12/1.65  
% 10.12/1.65  % (8371)Memory used [KB]: 7164
% 10.12/1.65  % (8371)Time elapsed: 1.236 s
% 10.12/1.65  % (8371)------------------------------
% 10.12/1.65  % (8371)------------------------------
% 10.40/1.71  % (8596)lrs+1004_8:1_av=off:bd=off:fsr=off:lwlo=on:nm=4:nwc=1.5:stl=30:sd=1:ss=axioms:st=5.0:uhcvi=on_98 on theBenchmark
% 10.40/1.72  % (8376)Time limit reached!
% 10.40/1.72  % (8376)------------------------------
% 10.40/1.72  % (8376)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.40/1.72  % (8376)Termination reason: Time limit
% 10.40/1.72  
% 10.40/1.72  % (8376)Memory used [KB]: 12537
% 10.40/1.72  % (8376)Time elapsed: 1.302 s
% 10.40/1.72  % (8376)------------------------------
% 10.40/1.72  % (8376)------------------------------
% 11.04/1.79  % (8597)lrs+1_2:3_aac=none:afr=on:afp=100000:afq=1.0:amm=sco:bd=off:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off:uhcvi=on_1 on theBenchmark
% 11.44/1.83  % (8598)lrs+1010_5_afr=on:afp=4000:afq=2.0:amm=sco:anc=none:bd=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=64:newcnf=on:nwc=4:sas=z3:stl=30:sos=on:sac=on:sp=occurrence:urr=ec_only:updr=off_298 on theBenchmark
% 11.71/1.92  % (8389)Refutation found. Thanks to Tanya!
% 11.71/1.92  % SZS status Theorem for theBenchmark
% 11.71/1.93  % SZS output start Proof for theBenchmark
% 11.71/1.93  fof(f21652,plain,(
% 11.71/1.93    $false),
% 11.71/1.93    inference(subsumption_resolution,[],[f21651,f19081])).
% 11.71/1.93  fof(f19081,plain,(
% 11.71/1.93    sK1 = sK3),
% 11.71/1.93    inference(subsumption_resolution,[],[f19077,f18815])).
% 11.71/1.93  fof(f18815,plain,(
% 11.71/1.93    r1_tarski(sK1,sK3)),
% 11.71/1.93    inference(superposition,[],[f40,f18589])).
% 12.32/1.94  fof(f18589,plain,(
% 12.32/1.94    sK3 = k2_xboole_0(sK1,sK3)),
% 12.32/1.94    inference(subsumption_resolution,[],[f18584,f1453])).
% 12.32/1.94  fof(f1453,plain,(
% 12.32/1.94    r1_tarski(sK3,k2_xboole_0(sK1,sK3))),
% 12.32/1.94    inference(subsumption_resolution,[],[f1438,f34])).
% 12.32/1.94  fof(f34,plain,(
% 12.32/1.94    k1_xboole_0 != sK0),
% 12.32/1.94    inference(cnf_transformation,[],[f26])).
% 12.32/1.94  fof(f26,plain,(
% 12.32/1.94    ? [X0,X1,X2,X3] : ((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0 & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 12.32/1.94    inference(flattening,[],[f25])).
% 12.32/1.94  fof(f25,plain,(
% 12.32/1.94    ? [X0,X1,X2,X3] : (((X1 != X3 | X0 != X2) & k1_xboole_0 != X1 & k1_xboole_0 != X0) & k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3))),
% 12.32/1.94    inference(ennf_transformation,[],[f22])).
% 12.32/1.94  fof(f22,negated_conjecture,(
% 12.32/1.94    ~! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 12.32/1.94    inference(negated_conjecture,[],[f21])).
% 12.32/1.94  fof(f21,conjecture,(
% 12.32/1.94    ! [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X1) = k2_zfmisc_1(X2,X3) => ((X1 = X3 & X0 = X2) | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t134_zfmisc_1)).
% 12.32/1.94  fof(f1438,plain,(
% 12.32/1.94    k1_xboole_0 = sK0 | r1_tarski(sK3,k2_xboole_0(sK1,sK3))),
% 12.32/1.94    inference(resolution,[],[f1401,f70])).
% 12.32/1.94  fof(f70,plain,(
% 12.32/1.94    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(X1,X2)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f31])).
% 12.32/1.94  fof(f31,plain,(
% 12.32/1.94    ! [X0,X1,X2] : (r1_tarski(X1,X2) | (~r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) & ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) | k1_xboole_0 = X0)),
% 12.32/1.94    inference(ennf_transformation,[],[f18])).
% 12.32/1.94  fof(f18,axiom,(
% 12.32/1.94    ! [X0,X1,X2] : ~(~r1_tarski(X1,X2) & (r1_tarski(k2_zfmisc_1(X0,X1),k2_zfmisc_1(X0,X2)) | r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0))) & k1_xboole_0 != X0)),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_zfmisc_1)).
% 12.32/1.94  fof(f1401,plain,(
% 12.32/1.94    r1_tarski(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))),
% 12.32/1.94    inference(superposition,[],[f226,f138])).
% 12.32/1.94  fof(f138,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK3)),
% 12.32/1.94    inference(forward_demodulation,[],[f126,f41])).
% 12.32/1.94  fof(f41,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f1])).
% 12.32/1.94  fof(f1,axiom,(
% 12.32/1.94    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 12.32/1.94  fof(f126,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)) = k2_zfmisc_1(k2_xboole_0(sK2,sK0),sK3)),
% 12.32/1.94    inference(superposition,[],[f96,f60])).
% 12.32/1.94  fof(f60,plain,(
% 12.32/1.94    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 12.32/1.94    inference(cnf_transformation,[],[f19])).
% 12.32/1.94  fof(f19,axiom,(
% 12.32/1.94    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 12.32/1.94  fof(f96,plain,(
% 12.32/1.94    ( ! [X0] : (k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3))) )),
% 12.32/1.94    inference(superposition,[],[f59,f33])).
% 12.32/1.94  fof(f33,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK3)),
% 12.32/1.94    inference(cnf_transformation,[],[f26])).
% 12.32/1.94  fof(f59,plain,(
% 12.32/1.94    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 12.32/1.94    inference(cnf_transformation,[],[f19])).
% 12.32/1.94  fof(f226,plain,(
% 12.32/1.94    ( ! [X3] : (r1_tarski(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(k2_xboole_0(X3,sK2),sK3))) )),
% 12.32/1.94    inference(superposition,[],[f40,f97])).
% 12.32/1.94  fof(f97,plain,(
% 12.32/1.94    ( ! [X1] : (k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,sK1))) )),
% 12.32/1.94    inference(superposition,[],[f59,f33])).
% 12.32/1.94  fof(f18584,plain,(
% 12.32/1.94    ~r1_tarski(sK3,k2_xboole_0(sK1,sK3)) | sK3 = k2_xboole_0(sK1,sK3)),
% 12.32/1.94    inference(resolution,[],[f18563,f51])).
% 12.32/1.94  fof(f51,plain,(
% 12.32/1.94    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 12.32/1.94    inference(cnf_transformation,[],[f7])).
% 12.32/1.94  fof(f7,axiom,(
% 12.32/1.94    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 12.32/1.94  fof(f18563,plain,(
% 12.32/1.94    r1_tarski(k2_xboole_0(sK1,sK3),sK3)),
% 12.32/1.94    inference(subsumption_resolution,[],[f18562,f3148])).
% 12.32/1.94  fof(f3148,plain,(
% 12.32/1.94    k1_xboole_0 != sK2),
% 12.32/1.94    inference(superposition,[],[f3142,f2527])).
% 12.32/1.94  fof(f2527,plain,(
% 12.32/1.94    sK2 = k4_xboole_0(sK2,k1_xboole_0)),
% 12.32/1.94    inference(superposition,[],[f74,f2472])).
% 12.32/1.94  fof(f2472,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(sK2,sK2)),
% 12.32/1.94    inference(forward_demodulation,[],[f2471,f302])).
% 12.32/1.94  fof(f302,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k1_xboole_0)),
% 12.32/1.94    inference(superposition,[],[f266,f85])).
% 12.32/1.94  fof(f85,plain,(
% 12.32/1.94    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 12.32/1.94    inference(equality_resolution,[],[f57])).
% 12.32/1.94  fof(f57,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f17])).
% 12.32/1.94  fof(f17,axiom,(
% 12.32/1.94    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 12.32/1.94  fof(f266,plain,(
% 12.32/1.94    ( ! [X4] : (k2_zfmisc_1(X4,sK3) = k4_xboole_0(k2_zfmisc_1(X4,sK3),k1_xboole_0)) )),
% 12.32/1.94    inference(forward_demodulation,[],[f251,f248])).
% 12.32/1.94  fof(f248,plain,(
% 12.32/1.94    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3))) )),
% 12.32/1.94    inference(resolution,[],[f226,f54])).
% 12.32/1.94  fof(f54,plain,(
% 12.32/1.94    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,X1)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f8])).
% 12.32/1.94  fof(f8,axiom,(
% 12.32/1.94    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 12.32/1.94  fof(f251,plain,(
% 12.32/1.94    ( ! [X4] : (k2_zfmisc_1(X4,sK3) = k4_xboole_0(k2_zfmisc_1(X4,sK3),k4_xboole_0(k2_zfmisc_1(X4,sK3),k2_zfmisc_1(k2_xboole_0(X4,sK2),sK3)))) )),
% 12.32/1.94    inference(resolution,[],[f226,f78])).
% 12.32/1.94  fof(f78,plain,(
% 12.32/1.94    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 12.32/1.94    inference(definition_unfolding,[],[f48,f44])).
% 12.32/1.94  fof(f44,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 12.32/1.94    inference(cnf_transformation,[],[f13])).
% 12.32/1.94  fof(f13,axiom,(
% 12.32/1.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 12.32/1.94  fof(f48,plain,(
% 12.32/1.94    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 12.32/1.94    inference(cnf_transformation,[],[f30])).
% 12.32/1.94  fof(f30,plain,(
% 12.32/1.94    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 12.32/1.94    inference(ennf_transformation,[],[f11])).
% 12.32/1.94  fof(f11,axiom,(
% 12.32/1.94    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 12.32/1.94  fof(f2471,plain,(
% 12.32/1.94    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(sK2,sK2)),
% 12.32/1.94    inference(subsumption_resolution,[],[f2469,f2354])).
% 12.32/1.94  fof(f2354,plain,(
% 12.32/1.94    k1_xboole_0 != sK3),
% 12.32/1.94    inference(superposition,[],[f2348,f1474])).
% 12.32/1.94  fof(f1474,plain,(
% 12.32/1.94    sK3 = k4_xboole_0(sK3,k1_xboole_0)),
% 12.32/1.94    inference(forward_demodulation,[],[f1471,f1468])).
% 12.32/1.94  fof(f1468,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(sK3,k2_xboole_0(sK1,sK3))),
% 12.32/1.94    inference(resolution,[],[f1453,f54])).
% 12.32/1.94  fof(f1471,plain,(
% 12.32/1.94    sK3 = k4_xboole_0(sK3,k4_xboole_0(sK3,k2_xboole_0(sK1,sK3)))),
% 12.32/1.94    inference(resolution,[],[f1453,f78])).
% 12.32/1.94  fof(f2348,plain,(
% 12.32/1.94    k1_xboole_0 != k4_xboole_0(sK3,k1_xboole_0)),
% 12.32/1.94    inference(forward_demodulation,[],[f2346,f1491])).
% 12.32/1.94  fof(f1491,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(sK3,sK3)),
% 12.32/1.94    inference(superposition,[],[f73,f1474])).
% 12.32/1.94  fof(f73,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 12.32/1.94    inference(definition_unfolding,[],[f36,f44])).
% 12.32/1.94  fof(f36,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f12])).
% 12.32/1.94  fof(f12,axiom,(
% 12.32/1.94    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 12.32/1.94  fof(f2346,plain,(
% 12.32/1.94    k1_xboole_0 != k4_xboole_0(sK3,k4_xboole_0(sK3,sK3))),
% 12.32/1.94    inference(resolution,[],[f2345,f80])).
% 12.32/1.94  fof(f80,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 12.32/1.94    inference(definition_unfolding,[],[f52,f44])).
% 12.32/1.94  fof(f52,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f3])).
% 12.32/1.94  fof(f3,axiom,(
% 12.32/1.94    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 12.32/1.94  fof(f2345,plain,(
% 12.32/1.94    ~r1_xboole_0(sK3,sK3)),
% 12.32/1.94    inference(subsumption_resolution,[],[f2337,f35])).
% 12.32/1.94  fof(f35,plain,(
% 12.32/1.94    k1_xboole_0 != sK1),
% 12.32/1.94    inference(cnf_transformation,[],[f26])).
% 12.32/1.94  fof(f2337,plain,(
% 12.32/1.94    ~r1_xboole_0(sK3,sK3) | k1_xboole_0 = sK1),
% 12.32/1.94    inference(resolution,[],[f2311,f38])).
% 12.32/1.94  fof(f38,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = X0 | r2_hidden(sK4(X0),X0)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f27])).
% 12.32/1.94  fof(f27,plain,(
% 12.32/1.94    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 12.32/1.94    inference(ennf_transformation,[],[f6])).
% 12.32/1.94  fof(f6,axiom,(
% 12.32/1.94    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 12.32/1.94  fof(f2311,plain,(
% 12.32/1.94    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r1_xboole_0(sK3,sK3)) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f2303,f34])).
% 12.32/1.94  fof(f2303,plain,(
% 12.32/1.94    ( ! [X0] : (~r1_xboole_0(sK3,sK3) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK0) )),
% 12.32/1.94    inference(resolution,[],[f1990,f38])).
% 12.32/1.94  fof(f1990,plain,(
% 12.32/1.94    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r1_xboole_0(sK3,sK3) | ~r2_hidden(X1,sK1)) )),
% 12.32/1.94    inference(resolution,[],[f1926,f87])).
% 12.32/1.94  fof(f87,plain,(
% 12.32/1.94    ( ! [X4,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),k2_zfmisc_1(X0,X1))) )),
% 12.32/1.94    inference(equality_resolution,[],[f86])).
% 12.32/1.94  fof(f86,plain,(
% 12.32/1.94    ( ! [X4,X2,X0,X5,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | r2_hidden(k4_tarski(X4,X5),X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 12.32/1.94    inference(equality_resolution,[],[f68])).
% 12.32/1.94  fof(f68,plain,(
% 12.32/1.94    ( ! [X4,X2,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 12.32/1.94    inference(cnf_transformation,[],[f16])).
% 12.32/1.94  fof(f16,axiom,(
% 12.32/1.94    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 12.32/1.94  fof(f1926,plain,(
% 12.32/1.94    ( ! [X17] : (~r2_hidden(X17,k2_zfmisc_1(sK0,sK1)) | ~r1_xboole_0(sK3,sK3)) )),
% 12.32/1.94    inference(superposition,[],[f1553,f33])).
% 12.32/1.94  fof(f1553,plain,(
% 12.32/1.94    ( ! [X8,X9] : (~r2_hidden(X9,k2_zfmisc_1(X8,sK3)) | ~r1_xboole_0(sK3,sK3)) )),
% 12.32/1.94    inference(resolution,[],[f1527,f89])).
% 12.32/1.94  fof(f89,plain,(
% 12.32/1.94    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 12.32/1.94    inference(equality_resolution,[],[f66])).
% 12.32/1.94  fof(f66,plain,(
% 12.32/1.94    ( ! [X2,X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 12.32/1.94    inference(cnf_transformation,[],[f16])).
% 12.32/1.94  fof(f1527,plain,(
% 12.32/1.94    ( ! [X0] : (~r2_hidden(X0,sK3) | ~r1_xboole_0(sK3,sK3)) )),
% 12.32/1.94    inference(forward_demodulation,[],[f1519,f1474])).
% 12.32/1.94  fof(f1519,plain,(
% 12.32/1.94    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK3,k1_xboole_0)) | ~r1_xboole_0(sK3,sK3)) )),
% 12.32/1.94    inference(superposition,[],[f77,f1491])).
% 12.32/1.94  fof(f77,plain,(
% 12.32/1.94    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 12.32/1.94    inference(definition_unfolding,[],[f45,f44])).
% 12.32/1.94  fof(f45,plain,(
% 12.32/1.94    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f28])).
% 12.32/1.94  fof(f28,plain,(
% 12.32/1.94    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 12.32/1.94    inference(ennf_transformation,[],[f24])).
% 12.32/1.94  fof(f24,plain,(
% 12.32/1.94    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 12.32/1.94    inference(rectify,[],[f5])).
% 12.32/1.94  fof(f5,axiom,(
% 12.32/1.94    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 12.32/1.94  fof(f2469,plain,(
% 12.32/1.94    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(sK2,sK2) | k1_xboole_0 = sK3),
% 12.32/1.94    inference(backward_demodulation,[],[f2126,f2468])).
% 12.32/1.94  fof(f2468,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(k1_xboole_0,sK2)),
% 12.32/1.94    inference(forward_demodulation,[],[f2467,f37])).
% 12.32/1.94  fof(f37,plain,(
% 12.32/1.94    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 12.32/1.94    inference(cnf_transformation,[],[f14])).
% 12.32/1.94  fof(f14,axiom,(
% 12.32/1.94    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 12.32/1.94  fof(f2467,plain,(
% 12.32/1.94    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK2)),
% 12.32/1.94    inference(subsumption_resolution,[],[f2451,f2354])).
% 12.32/1.94  fof(f2451,plain,(
% 12.32/1.94    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,sK2) | k1_xboole_0 = sK3),
% 12.32/1.94    inference(superposition,[],[f72,f2039])).
% 12.32/1.94  fof(f2039,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)) | k1_xboole_0 = sK3),
% 12.32/1.94    inference(resolution,[],[f2035,f78])).
% 12.32/1.94  fof(f2035,plain,(
% 12.32/1.94    r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 = sK3),
% 12.32/1.94    inference(subsumption_resolution,[],[f2025,f670])).
% 12.32/1.94  fof(f670,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 12.32/1.94    inference(forward_demodulation,[],[f655,f37])).
% 12.32/1.94  fof(f655,plain,(
% 12.32/1.94    k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 12.32/1.94    inference(superposition,[],[f72,f198])).
% 12.32/1.94  fof(f198,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)))),
% 12.32/1.94    inference(forward_demodulation,[],[f188,f184])).
% 12.32/1.94  fof(f184,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 12.32/1.94    inference(superposition,[],[f73,f156])).
% 12.32/1.94  fof(f156,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k1_xboole_0)),
% 12.32/1.94    inference(forward_demodulation,[],[f143,f140])).
% 12.32/1.94  fof(f140,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X0),sK3))) )),
% 12.32/1.94    inference(resolution,[],[f134,f54])).
% 12.32/1.94  fof(f134,plain,(
% 12.32/1.94    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X3),sK3))) )),
% 12.32/1.94    inference(superposition,[],[f40,f96])).
% 12.32/1.94  fof(f143,plain,(
% 12.32/1.94    ( ! [X3] : (k2_zfmisc_1(sK0,sK1) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,X3),sK3)))) )),
% 12.32/1.94    inference(resolution,[],[f134,f78])).
% 12.32/1.94  fof(f188,plain,(
% 12.32/1.94    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1)))),
% 12.32/1.94    inference(superposition,[],[f75,f156])).
% 12.32/1.94  fof(f75,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 12.32/1.94    inference(definition_unfolding,[],[f42,f44,f44])).
% 12.32/1.94  fof(f42,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f2])).
% 12.32/1.94  fof(f2,axiom,(
% 12.32/1.94    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 12.32/1.94  fof(f2025,plain,(
% 12.32/1.94    k1_xboole_0 = sK3 | r1_tarski(k1_xboole_0,sK2) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 12.32/1.94    inference(resolution,[],[f881,f55])).
% 12.32/1.94  fof(f55,plain,(
% 12.32/1.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | k1_xboole_0 != k4_xboole_0(X0,X1)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f8])).
% 12.32/1.94  fof(f881,plain,(
% 12.32/1.94    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK3 | r1_tarski(k1_xboole_0,sK2)),
% 12.32/1.94    inference(superposition,[],[f105,f85])).
% 12.32/1.94  fof(f105,plain,(
% 12.32/1.94    ( ! [X10] : (~r1_tarski(k2_zfmisc_1(X10,sK3),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK3 | r1_tarski(X10,sK2)) )),
% 12.32/1.94    inference(superposition,[],[f69,f33])).
% 12.32/1.94  fof(f69,plain,(
% 12.32/1.94    ( ! [X2,X0,X1] : (k1_xboole_0 = X0 | ~r1_tarski(k2_zfmisc_1(X1,X0),k2_zfmisc_1(X2,X0)) | r1_tarski(X1,X2)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f31])).
% 12.32/1.94  fof(f72,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 12.32/1.94    inference(definition_unfolding,[],[f43,f44])).
% 12.32/1.94  fof(f43,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 12.32/1.94    inference(cnf_transformation,[],[f9])).
% 12.32/1.94  fof(f9,axiom,(
% 12.32/1.94    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 12.32/1.94  fof(f2126,plain,(
% 12.32/1.94    k4_xboole_0(sK2,sK2) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,sK2)) | k1_xboole_0 = sK3),
% 12.32/1.94    inference(superposition,[],[f75,f2104])).
% 12.32/1.94  fof(f2104,plain,(
% 12.32/1.94    sK2 = k4_xboole_0(sK2,k1_xboole_0) | k1_xboole_0 = sK3),
% 12.32/1.94    inference(superposition,[],[f74,f2081])).
% 12.32/1.94  fof(f2081,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(sK2,sK2) | k1_xboole_0 = sK3),
% 12.32/1.94    inference(duplicate_literal_removal,[],[f2075])).
% 12.32/1.94  fof(f2075,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(sK2,sK2) | k1_xboole_0 = sK3 | k1_xboole_0 = sK3),
% 12.32/1.94    inference(superposition,[],[f732,f2040])).
% 12.32/1.94  fof(f2040,plain,(
% 12.32/1.94    sK2 = k2_xboole_0(k1_xboole_0,sK2) | k1_xboole_0 = sK3),
% 12.32/1.94    inference(resolution,[],[f2035,f47])).
% 12.32/1.94  fof(f47,plain,(
% 12.32/1.94    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k2_xboole_0(X0,X1) = X1) )),
% 12.32/1.94    inference(cnf_transformation,[],[f29])).
% 12.32/1.94  fof(f29,plain,(
% 12.32/1.94    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 12.32/1.94    inference(ennf_transformation,[],[f10])).
% 12.32/1.94  fof(f10,axiom,(
% 12.32/1.94    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 12.32/1.94  fof(f732,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(sK2,k2_xboole_0(X0,sK2)) | k1_xboole_0 = sK3) )),
% 12.32/1.94    inference(resolution,[],[f691,f54])).
% 12.32/1.94  fof(f691,plain,(
% 12.32/1.94    ( ! [X1] : (r1_tarski(sK2,k2_xboole_0(X1,sK2)) | k1_xboole_0 = sK3) )),
% 12.32/1.94    inference(resolution,[],[f104,f150])).
% 12.32/1.94  fof(f150,plain,(
% 12.32/1.94    ( ! [X1] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k2_xboole_0(X1,sK2),sK3))) )),
% 12.32/1.94    inference(superposition,[],[f134,f41])).
% 12.32/1.94  fof(f104,plain,(
% 12.32/1.94    ( ! [X9] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK3)) | k1_xboole_0 = sK3 | r1_tarski(sK2,X9)) )),
% 12.32/1.94    inference(superposition,[],[f69,f33])).
% 12.32/1.94  fof(f74,plain,(
% 12.32/1.94    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 12.32/1.94    inference(definition_unfolding,[],[f39,f44])).
% 12.32/1.94  fof(f39,plain,(
% 12.32/1.94    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 12.32/1.94    inference(cnf_transformation,[],[f23])).
% 12.32/1.94  fof(f23,plain,(
% 12.32/1.94    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 12.32/1.94    inference(rectify,[],[f4])).
% 12.32/1.94  fof(f4,axiom,(
% 12.32/1.94    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 12.32/1.94  fof(f3142,plain,(
% 12.32/1.94    k1_xboole_0 != k4_xboole_0(sK2,k1_xboole_0)),
% 12.32/1.94    inference(forward_demodulation,[],[f3140,f2472])).
% 12.32/1.94  fof(f3140,plain,(
% 12.32/1.94    k1_xboole_0 != k4_xboole_0(sK2,k4_xboole_0(sK2,sK2))),
% 12.32/1.94    inference(resolution,[],[f3139,f80])).
% 12.32/1.94  fof(f3139,plain,(
% 12.32/1.94    ~r1_xboole_0(sK2,sK2)),
% 12.32/1.94    inference(subsumption_resolution,[],[f3131,f35])).
% 12.32/1.94  fof(f3131,plain,(
% 12.32/1.94    ~r1_xboole_0(sK2,sK2) | k1_xboole_0 = sK1),
% 12.32/1.94    inference(resolution,[],[f3130,f38])).
% 12.32/1.94  fof(f3130,plain,(
% 12.32/1.94    ( ! [X0] : (~r2_hidden(X0,sK1) | ~r1_xboole_0(sK2,sK2)) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f3122,f34])).
% 12.32/1.94  fof(f3122,plain,(
% 12.32/1.94    ( ! [X0] : (~r1_xboole_0(sK2,sK2) | ~r2_hidden(X0,sK1) | k1_xboole_0 = sK0) )),
% 12.32/1.94    inference(resolution,[],[f2984,f38])).
% 12.32/1.94  fof(f2984,plain,(
% 12.32/1.94    ( ! [X0,X1] : (~r2_hidden(X0,sK0) | ~r1_xboole_0(sK2,sK2) | ~r2_hidden(X1,sK1)) )),
% 12.32/1.94    inference(resolution,[],[f2853,f87])).
% 12.32/1.94  fof(f2853,plain,(
% 12.32/1.94    ( ! [X0] : (~r2_hidden(X0,k2_zfmisc_1(sK0,sK1)) | ~r1_xboole_0(sK2,sK2)) )),
% 12.32/1.94    inference(superposition,[],[f2660,f33])).
% 12.32/1.94  fof(f2660,plain,(
% 12.32/1.94    ( ! [X6,X7] : (~r2_hidden(X7,k2_zfmisc_1(sK2,X6)) | ~r1_xboole_0(sK2,sK2)) )),
% 12.32/1.94    inference(resolution,[],[f2558,f90])).
% 12.32/1.94  fof(f90,plain,(
% 12.32/1.94    ( ! [X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,k2_zfmisc_1(X0,X1))) )),
% 12.32/1.94    inference(equality_resolution,[],[f65])).
% 12.32/1.94  fof(f65,plain,(
% 12.32/1.94    ( ! [X2,X0,X3,X1] : (r2_hidden(sK7(X0,X1,X3),X0) | ~r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 12.32/1.94    inference(cnf_transformation,[],[f16])).
% 12.32/1.94  fof(f2558,plain,(
% 12.32/1.94    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r1_xboole_0(sK2,sK2)) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f2546,f2354])).
% 12.32/1.94  fof(f2546,plain,(
% 12.32/1.94    ( ! [X0] : (~r2_hidden(X0,sK2) | ~r1_xboole_0(sK2,sK2) | k1_xboole_0 = sK3) )),
% 12.32/1.94    inference(backward_demodulation,[],[f2108,f2527])).
% 12.32/1.94  fof(f2108,plain,(
% 12.32/1.94    ( ! [X0] : (~r2_hidden(X0,k4_xboole_0(sK2,k1_xboole_0)) | ~r1_xboole_0(sK2,sK2) | k1_xboole_0 = sK3) )),
% 12.32/1.94    inference(superposition,[],[f77,f2081])).
% 12.32/1.94  fof(f18562,plain,(
% 12.32/1.94    k1_xboole_0 = sK2 | r1_tarski(k2_xboole_0(sK1,sK3),sK3)),
% 12.32/1.94    inference(subsumption_resolution,[],[f18484,f83])).
% 12.32/1.94  fof(f83,plain,(
% 12.32/1.94    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 12.32/1.94    inference(equality_resolution,[],[f49])).
% 12.32/1.94  fof(f49,plain,(
% 12.32/1.94    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 12.32/1.94    inference(cnf_transformation,[],[f7])).
% 12.32/1.94  fof(f18484,plain,(
% 12.32/1.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK2 | r1_tarski(k2_xboole_0(sK1,sK3),sK3)),
% 12.32/1.94    inference(superposition,[],[f107,f18012])).
% 12.32/1.94  fof(f18012,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3))),
% 12.32/1.94    inference(backward_demodulation,[],[f397,f17972])).
% 12.32/1.94  fof(f17972,plain,(
% 12.32/1.94    sK0 = k2_xboole_0(sK0,sK2)),
% 12.32/1.94    inference(superposition,[],[f17942,f41])).
% 12.32/1.94  fof(f17942,plain,(
% 12.32/1.94    sK0 = k2_xboole_0(sK2,sK0)),
% 12.32/1.94    inference(resolution,[],[f17937,f47])).
% 12.32/1.94  fof(f17937,plain,(
% 12.32/1.94    r1_tarski(sK2,sK0)),
% 12.32/1.94    inference(trivial_inequality_removal,[],[f17933])).
% 12.32/1.94  fof(f17933,plain,(
% 12.32/1.94    k1_xboole_0 != k1_xboole_0 | r1_tarski(sK2,sK0)),
% 12.32/1.94    inference(superposition,[],[f17814,f184])).
% 12.32/1.94  fof(f17814,plain,(
% 12.32/1.94    ( ! [X6] : (k1_xboole_0 != k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X6,sK1)) | r1_tarski(sK2,X6)) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f17810,f2354])).
% 12.32/1.94  fof(f17810,plain,(
% 12.32/1.94    ( ! [X6] : (k1_xboole_0 != k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X6,sK1)) | r1_tarski(sK2,X6) | k1_xboole_0 = sK3) )),
% 12.32/1.94    inference(backward_demodulation,[],[f694,f17809])).
% 12.32/1.94  fof(f17809,plain,(
% 12.32/1.94    ( ! [X0] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK1))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f17791,f13101])).
% 12.32/1.94  fof(f13101,plain,(
% 12.32/1.94    ( ! [X4,X2,X3] : (k4_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(X4,X3)) = k5_xboole_0(k2_zfmisc_1(X2,X3),k2_zfmisc_1(k4_xboole_0(X2,k4_xboole_0(X2,X4)),X3))) )),
% 12.32/1.94    inference(superposition,[],[f72,f12172])).
% 12.32/1.94  fof(f12172,plain,(
% 12.32/1.94    ( ! [X14,X15,X16] : (k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),X14) = k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,X14)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f12167,f12121])).
% 12.32/1.94  fof(f12121,plain,(
% 12.32/1.94    ( ! [X3] : (k4_xboole_0(X3,k1_xboole_0) = X3) )),
% 12.32/1.94    inference(forward_demodulation,[],[f12113,f12110])).
% 12.32/1.94  fof(f12110,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(k2_xboole_0(sK0,sK2),X0))) )),
% 12.32/1.94    inference(resolution,[],[f12106,f54])).
% 12.32/1.94  fof(f12106,plain,(
% 12.32/1.94    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK0,sK2),X0))) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f12080,f2354])).
% 12.32/1.94  fof(f12080,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = sK3 | r1_tarski(X0,k2_xboole_0(k2_xboole_0(sK0,sK2),X0))) )),
% 12.32/1.94    inference(resolution,[],[f12066,f69])).
% 12.32/1.94  fof(f12066,plain,(
% 12.32/1.94    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k2_xboole_0(k2_xboole_0(sK0,sK2),X1),sK3))) )),
% 12.32/1.94    inference(superposition,[],[f11972,f41])).
% 12.32/1.94  fof(f11972,plain,(
% 12.32/1.94    ( ! [X3] : (r1_tarski(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(k2_xboole_0(X3,k2_xboole_0(sK0,sK2)),sK3))) )),
% 12.32/1.94    inference(superposition,[],[f40,f1416])).
% 12.32/1.94  fof(f1416,plain,(
% 12.32/1.94    ( ! [X1] : (k2_zfmisc_1(k2_xboole_0(X1,k2_xboole_0(sK0,sK2)),sK3) = k2_xboole_0(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) )),
% 12.32/1.94    inference(superposition,[],[f59,f138])).
% 12.32/1.94  fof(f12113,plain,(
% 12.32/1.94    ( ! [X3] : (k4_xboole_0(X3,k4_xboole_0(X3,k2_xboole_0(k2_xboole_0(sK0,sK2),X3))) = X3) )),
% 12.32/1.94    inference(resolution,[],[f12106,f78])).
% 12.32/1.94  fof(f12167,plain,(
% 12.32/1.94    ( ! [X14,X15,X16] : (k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X14,k1_xboole_0)) = k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,X14)))) )),
% 12.32/1.94    inference(superposition,[],[f81,f12122])).
% 12.32/1.94  fof(f12122,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 12.32/1.94    inference(backward_demodulation,[],[f73,f12121])).
% 12.32/1.94  fof(f81,plain,(
% 12.32/1.94    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = k4_xboole_0(k2_zfmisc_1(X0,X2),k4_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) )),
% 12.32/1.94    inference(definition_unfolding,[],[f71,f44,f44,f44])).
% 12.32/1.94  fof(f71,plain,(
% 12.32/1.94    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 12.32/1.94    inference(cnf_transformation,[],[f20])).
% 12.32/1.94  fof(f20,axiom,(
% 12.32/1.94    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 12.32/1.94  fof(f17791,plain,(
% 12.32/1.94    ( ! [X0] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X0)),sK1))) )),
% 12.32/1.94    inference(backward_demodulation,[],[f17017,f17788])).
% 12.32/1.94  fof(f17788,plain,(
% 12.32/1.94    ( ! [X23] : (k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X23)),sK3) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X23)),sK1)) )),
% 12.32/1.94    inference(forward_demodulation,[],[f17780,f8040])).
% 12.32/1.94  fof(f8040,plain,(
% 12.32/1.94    ( ! [X4,X3] : (k4_xboole_0(k2_zfmisc_1(X3,sK1),k4_xboole_0(k2_zfmisc_1(X3,sK1),k2_zfmisc_1(X4,sK1))) = k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X4)),sK1)) )),
% 12.32/1.94    inference(forward_demodulation,[],[f8035,f8026])).
% 12.32/1.94  fof(f8026,plain,(
% 12.32/1.94    sK1 = k4_xboole_0(sK1,k1_xboole_0)),
% 12.32/1.94    inference(superposition,[],[f74,f8004])).
% 12.32/1.94  fof(f8004,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(sK1,sK1)),
% 12.32/1.94    inference(backward_demodulation,[],[f7971,f7977])).
% 12.32/1.94  fof(f7977,plain,(
% 12.32/1.94    sK1 = k2_xboole_0(sK1,sK1)),
% 12.32/1.94    inference(subsumption_resolution,[],[f7972,f40])).
% 12.32/1.94  fof(f7972,plain,(
% 12.32/1.94    ~r1_tarski(sK1,k2_xboole_0(sK1,sK1)) | sK1 = k2_xboole_0(sK1,sK1)),
% 12.32/1.94    inference(resolution,[],[f7954,f51])).
% 12.32/1.94  fof(f7954,plain,(
% 12.32/1.94    r1_tarski(k2_xboole_0(sK1,sK1),sK1)),
% 12.32/1.94    inference(resolution,[],[f5163,f83])).
% 12.32/1.94  fof(f5163,plain,(
% 12.32/1.94    ( ! [X11] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X11)) | r1_tarski(k2_xboole_0(sK1,sK1),X11)) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f5154,f34])).
% 12.32/1.94  fof(f5154,plain,(
% 12.32/1.94    ( ! [X11] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X11)) | k1_xboole_0 = sK0 | r1_tarski(k2_xboole_0(sK1,sK1),X11)) )),
% 12.32/1.94    inference(superposition,[],[f70,f4967])).
% 12.32/1.94  fof(f4967,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1))),
% 12.32/1.94    inference(forward_demodulation,[],[f4952,f33])).
% 12.32/1.94  fof(f4952,plain,(
% 12.32/1.94    k2_zfmisc_1(sK2,sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1))),
% 12.32/1.94    inference(backward_demodulation,[],[f393,f4951])).
% 12.32/1.94  fof(f4951,plain,(
% 12.32/1.94    sK3 = k2_xboole_0(sK3,sK3)),
% 12.32/1.94    inference(subsumption_resolution,[],[f4934,f3148])).
% 12.32/1.94  fof(f4934,plain,(
% 12.32/1.94    sK3 = k2_xboole_0(sK3,sK3) | k1_xboole_0 = sK2),
% 12.32/1.94    inference(superposition,[],[f4895,f2330])).
% 12.32/1.94  fof(f2330,plain,(
% 12.32/1.94    sK3 = k2_xboole_0(k1_xboole_0,sK3) | k1_xboole_0 = sK2),
% 12.32/1.94    inference(resolution,[],[f2325,f47])).
% 12.32/1.94  fof(f2325,plain,(
% 12.32/1.94    r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 = sK2),
% 12.32/1.94    inference(subsumption_resolution,[],[f2315,f670])).
% 12.32/1.94  fof(f2315,plain,(
% 12.32/1.94    k1_xboole_0 = sK2 | r1_tarski(k1_xboole_0,sK3) | k1_xboole_0 != k4_xboole_0(k1_xboole_0,k2_zfmisc_1(sK0,sK1))),
% 12.32/1.94    inference(resolution,[],[f1117,f55])).
% 12.32/1.94  fof(f1117,plain,(
% 12.32/1.94    ~r1_tarski(k1_xboole_0,k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK2 | r1_tarski(k1_xboole_0,sK3)),
% 12.32/1.94    inference(superposition,[],[f107,f84])).
% 12.32/1.94  fof(f84,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 12.32/1.94    inference(equality_resolution,[],[f58])).
% 12.32/1.94  fof(f58,plain,(
% 12.32/1.94    ( ! [X0,X1] : (k1_xboole_0 != X1 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 12.32/1.94    inference(cnf_transformation,[],[f17])).
% 12.32/1.94  fof(f4895,plain,(
% 12.32/1.94    sK3 = k2_xboole_0(k2_xboole_0(k1_xboole_0,sK3),sK3)),
% 12.32/1.94    inference(resolution,[],[f4890,f47])).
% 12.32/1.94  fof(f4890,plain,(
% 12.32/1.94    r1_tarski(k2_xboole_0(k1_xboole_0,sK3),sK3)),
% 12.32/1.94    inference(forward_demodulation,[],[f4889,f41])).
% 12.32/1.94  fof(f4889,plain,(
% 12.32/1.94    r1_tarski(k2_xboole_0(sK3,k1_xboole_0),sK3)),
% 12.32/1.94    inference(subsumption_resolution,[],[f4887,f3148])).
% 12.32/1.94  fof(f4887,plain,(
% 12.32/1.94    r1_tarski(k2_xboole_0(sK3,k1_xboole_0),sK3) | k1_xboole_0 = sK2),
% 12.32/1.94    inference(superposition,[],[f4867,f2330])).
% 12.32/1.94  fof(f4867,plain,(
% 12.32/1.94    ( ! [X0] : (r1_tarski(k2_xboole_0(sK3,X0),k2_xboole_0(X0,sK3))) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f4839,f3148])).
% 12.32/1.94  fof(f4839,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = sK2 | r1_tarski(k2_xboole_0(sK3,X0),k2_xboole_0(X0,sK3))) )),
% 12.32/1.94    inference(resolution,[],[f4224,f70])).
% 12.32/1.94  fof(f4224,plain,(
% 12.32/1.94    ( ! [X8] : (r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X8)),k2_zfmisc_1(sK2,k2_xboole_0(X8,sK3)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f4223,f4207])).
% 12.32/1.94  fof(f4207,plain,(
% 12.32/1.94    ( ! [X7] : (k2_zfmisc_1(sK2,k2_xboole_0(X7,sK3)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(X7,sK3)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f4206,f4201])).
% 12.32/1.94  fof(f4201,plain,(
% 12.32/1.94    ( ! [X3] : (k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X3)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f4126,f482])).
% 12.32/1.94  fof(f482,plain,(
% 12.32/1.94    ( ! [X4] : (k2_zfmisc_1(sK2,k2_xboole_0(X4,sK3)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X4,sK3)))) )),
% 12.32/1.94    inference(resolution,[],[f471,f47])).
% 12.32/1.94  fof(f471,plain,(
% 12.32/1.94    ( ! [X1] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X1,sK3)))) )),
% 12.32/1.94    inference(superposition,[],[f392,f41])).
% 12.32/1.94  fof(f392,plain,(
% 12.32/1.94    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X3)))) )),
% 12.32/1.94    inference(superposition,[],[f40,f98])).
% 12.32/1.94  fof(f98,plain,(
% 12.32/1.94    ( ! [X2] : (k2_zfmisc_1(sK2,k2_xboole_0(sK3,X2)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2))) )),
% 12.32/1.94    inference(superposition,[],[f60,f33])).
% 12.32/1.94  fof(f4126,plain,(
% 12.32/1.94    ( ! [X3] : (k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X3))) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)))) )),
% 12.32/1.94    inference(superposition,[],[f98,f2749])).
% 12.32/1.94  fof(f2749,plain,(
% 12.32/1.94    ( ! [X1] : (k2_zfmisc_1(sK2,k2_xboole_0(sK3,X1)) = k2_zfmisc_1(sK2,k2_xboole_0(X1,sK3))) )),
% 12.32/1.94    inference(superposition,[],[f508,f98])).
% 12.32/1.94  fof(f508,plain,(
% 12.32/1.94    ( ! [X2] : (k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X2)) = k2_zfmisc_1(sK2,k2_xboole_0(X2,sK3))) )),
% 12.32/1.94    inference(superposition,[],[f99,f41])).
% 12.32/1.94  fof(f99,plain,(
% 12.32/1.94    ( ! [X3] : (k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)) = k2_xboole_0(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK0,sK1))) )),
% 12.32/1.94    inference(superposition,[],[f60,f33])).
% 12.32/1.94  fof(f4206,plain,(
% 12.32/1.94    ( ! [X7] : (k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(X7,sK3))) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(sK3,X7)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f4205,f41])).
% 12.32/1.94  fof(f4205,plain,(
% 12.32/1.94    ( ! [X7] : (k2_zfmisc_1(sK2,k2_xboole_0(k2_xboole_0(sK3,X7),sK3)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(X7,sK3)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f4130,f98])).
% 12.32/1.94  fof(f4130,plain,(
% 12.32/1.94    ( ! [X7] : (k2_zfmisc_1(sK2,k2_xboole_0(k2_xboole_0(sK3,X7),sK3)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,k2_xboole_0(X7,sK3)))) )),
% 12.32/1.94    inference(superposition,[],[f508,f2749])).
% 12.32/1.94  fof(f4223,plain,(
% 12.32/1.94    ( ! [X8] : (r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X8)),k2_zfmisc_1(sK2,k2_xboole_0(sK3,k2_xboole_0(X8,sK3))))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f4170,f2749])).
% 12.32/1.94  fof(f4170,plain,(
% 12.32/1.94    ( ! [X8] : (r1_tarski(k2_zfmisc_1(sK2,k2_xboole_0(sK3,X8)),k2_zfmisc_1(sK2,k2_xboole_0(k2_xboole_0(X8,sK3),sK3)))) )),
% 12.32/1.94    inference(superposition,[],[f515,f2749])).
% 12.32/1.94  fof(f515,plain,(
% 12.32/1.94    ( ! [X3] : (r1_tarski(k2_zfmisc_1(sK2,X3),k2_zfmisc_1(sK2,k2_xboole_0(X3,sK3)))) )),
% 12.32/1.94    inference(superposition,[],[f40,f99])).
% 12.32/1.94  fof(f393,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK3))),
% 12.32/1.94    inference(forward_demodulation,[],[f380,f60])).
% 12.32/1.94  fof(f380,plain,(
% 12.32/1.94    k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK3))),
% 12.32/1.94    inference(superposition,[],[f98,f33])).
% 12.32/1.94  fof(f7971,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK1,sK1),sK1)),
% 12.32/1.94    inference(resolution,[],[f7954,f54])).
% 12.32/1.94  fof(f8035,plain,(
% 12.32/1.94    ( ! [X4,X3] : (k4_xboole_0(k2_zfmisc_1(X3,sK1),k4_xboole_0(k2_zfmisc_1(X3,sK1),k2_zfmisc_1(X4,sK1))) = k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(sK1,k1_xboole_0))) )),
% 12.32/1.94    inference(superposition,[],[f81,f8004])).
% 12.32/1.94  fof(f17780,plain,(
% 12.32/1.94    ( ! [X23] : (k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X23)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,sK1)))) )),
% 12.32/1.94    inference(backward_demodulation,[],[f17748,f17764])).
% 12.32/1.94  fof(f17764,plain,(
% 12.32/1.94    sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 12.32/1.94    inference(subsumption_resolution,[],[f17756,f17739])).
% 12.32/1.94  fof(f17739,plain,(
% 12.32/1.94    r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))),
% 12.32/1.94    inference(subsumption_resolution,[],[f17697,f83])).
% 12.32/1.94  fof(f17697,plain,(
% 12.32/1.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))),
% 12.32/1.94    inference(superposition,[],[f7987,f17077])).
% 12.32/1.94  fof(f17077,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))),
% 12.32/1.94    inference(forward_demodulation,[],[f17076,f75])).
% 12.32/1.94  fof(f17076,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1)))),
% 12.32/1.94    inference(forward_demodulation,[],[f17075,f17053])).
% 12.32/1.94  fof(f17053,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3)),
% 12.32/1.94    inference(forward_demodulation,[],[f17052,f12121])).
% 12.32/1.94  fof(f17052,plain,(
% 12.32/1.94    k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),sK1) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3)),
% 12.32/1.94    inference(forward_demodulation,[],[f17051,f12122])).
% 12.32/1.94  fof(f17051,plain,(
% 12.32/1.94    k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK0)),sK1) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3)),
% 12.32/1.94    inference(forward_demodulation,[],[f17050,f12158])).
% 12.32/1.94  fof(f12158,plain,(
% 12.32/1.94    ( ! [X14,X15,X16] : (k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,k2_xboole_0(X14,sK3)))) = k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),X14)) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f12140,f3148])).
% 12.32/1.94  fof(f12140,plain,(
% 12.32/1.94    ( ! [X14,X15,X16] : (k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,k2_xboole_0(X14,sK3)))) = k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),X14) | k1_xboole_0 = sK2) )),
% 12.32/1.94    inference(backward_demodulation,[],[f1137,f12121])).
% 12.32/1.94  fof(f1137,plain,(
% 12.32/1.94    ( ! [X14,X15,X16] : (k2_zfmisc_1(k4_xboole_0(X15,k4_xboole_0(X15,X16)),k4_xboole_0(X14,k1_xboole_0)) = k4_xboole_0(k2_zfmisc_1(X15,X14),k4_xboole_0(k2_zfmisc_1(X15,X14),k2_zfmisc_1(X16,k2_xboole_0(X14,sK3)))) | k1_xboole_0 = sK2) )),
% 12.32/1.94    inference(superposition,[],[f81,f1056])).
% 12.32/1.94  fof(f1056,plain,(
% 12.32/1.94    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X1,sK3)) | k1_xboole_0 = sK2) )),
% 12.32/1.94    inference(superposition,[],[f564,f41])).
% 12.32/1.94  fof(f564,plain,(
% 12.32/1.94    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(sK3,X0)) | k1_xboole_0 = sK2) )),
% 12.32/1.94    inference(resolution,[],[f542,f54])).
% 12.32/1.94  fof(f542,plain,(
% 12.32/1.94    ( ! [X0] : (r1_tarski(X0,k2_xboole_0(sK3,X0)) | k1_xboole_0 = sK2) )),
% 12.32/1.94    inference(resolution,[],[f534,f70])).
% 12.32/1.94  fof(f534,plain,(
% 12.32/1.94    ( ! [X1] : (r1_tarski(k2_zfmisc_1(sK2,X1),k2_zfmisc_1(sK2,k2_xboole_0(sK3,X1)))) )),
% 12.32/1.94    inference(superposition,[],[f515,f41])).
% 12.32/1.94  fof(f17050,plain,(
% 12.32/1.94    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3)),
% 12.32/1.94    inference(forward_demodulation,[],[f17049,f75])).
% 12.32/1.94  fof(f17049,plain,(
% 12.32/1.94    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3)),
% 12.32/1.94    inference(forward_demodulation,[],[f16999,f13127])).
% 12.32/1.94  fof(f13127,plain,(
% 12.32/1.94    ( ! [X21] : (k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,k2_xboole_0(sK0,sK2))),sK3) = k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,sK0)),sK3)) )),
% 12.32/1.94    inference(forward_demodulation,[],[f13078,f1617])).
% 12.32/1.94  fof(f1617,plain,(
% 12.32/1.94    ( ! [X4,X3] : (k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X4)),sK3) = k4_xboole_0(k2_zfmisc_1(X3,sK3),k4_xboole_0(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(X4,k2_xboole_0(sK1,sK3))))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f1612,f1474])).
% 12.32/1.94  fof(f1612,plain,(
% 12.32/1.94    ( ! [X4,X3] : (k2_zfmisc_1(k4_xboole_0(X3,k4_xboole_0(X3,X4)),k4_xboole_0(sK3,k1_xboole_0)) = k4_xboole_0(k2_zfmisc_1(X3,sK3),k4_xboole_0(k2_zfmisc_1(X3,sK3),k2_zfmisc_1(X4,k2_xboole_0(sK1,sK3))))) )),
% 12.32/1.94    inference(superposition,[],[f81,f1468])).
% 12.32/1.94  fof(f13078,plain,(
% 12.32/1.94    ( ! [X21] : (k2_zfmisc_1(k4_xboole_0(X21,k4_xboole_0(X21,k2_xboole_0(sK0,sK2))),sK3) = k4_xboole_0(k2_zfmisc_1(X21,sK3),k4_xboole_0(k2_zfmisc_1(X21,sK3),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3))))) )),
% 12.32/1.94    inference(superposition,[],[f12172,f138])).
% 12.32/1.94  fof(f16999,plain,(
% 12.32/1.94    k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK3)))) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,k2_xboole_0(sK0,sK2))),sK3)),
% 12.32/1.94    inference(superposition,[],[f13069,f138])).
% 12.32/1.94  fof(f13069,plain,(
% 12.32/1.94    ( ! [X33] : (k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X33)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X33,sK3)))) )),
% 12.32/1.94    inference(superposition,[],[f12172,f33])).
% 12.32/1.94  fof(f17075,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK3)),
% 12.32/1.94    inference(forward_demodulation,[],[f17007,f75])).
% 12.32/1.94  fof(f17007,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,k4_xboole_0(sK3,k4_xboole_0(sK3,sK1))) = k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)),sK3)),
% 12.32/1.94    inference(superposition,[],[f13069,f12842])).
% 12.32/1.94  fof(f12842,plain,(
% 12.32/1.94    ( ! [X10,X11,X9] : (k4_xboole_0(k2_zfmisc_1(X9,X11),k4_xboole_0(k2_zfmisc_1(X9,X11),k2_zfmisc_1(X9,X10))) = k2_zfmisc_1(X9,k4_xboole_0(X10,k4_xboole_0(X10,X11)))) )),
% 12.32/1.94    inference(superposition,[],[f12171,f75])).
% 12.32/1.94  fof(f12171,plain,(
% 12.32/1.94    ( ! [X12,X13,X11] : (k2_zfmisc_1(X11,k4_xboole_0(X12,k4_xboole_0(X12,X13))) = k4_xboole_0(k2_zfmisc_1(X11,X12),k4_xboole_0(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X11,X13)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f12166,f12121])).
% 12.32/1.94  fof(f12166,plain,(
% 12.32/1.94    ( ! [X12,X13,X11] : (k2_zfmisc_1(k4_xboole_0(X11,k1_xboole_0),k4_xboole_0(X12,k4_xboole_0(X12,X13))) = k4_xboole_0(k2_zfmisc_1(X11,X12),k4_xboole_0(k2_zfmisc_1(X11,X12),k2_zfmisc_1(X11,X13)))) )),
% 12.32/1.94    inference(superposition,[],[f81,f12122])).
% 12.32/1.94  fof(f7987,plain,(
% 12.32/1.94    ( ! [X11] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,X11)) | r1_tarski(sK1,X11)) )),
% 12.32/1.94    inference(backward_demodulation,[],[f5163,f7977])).
% 12.32/1.94  fof(f17756,plain,(
% 12.32/1.94    ~r1_tarski(sK1,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) | sK1 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))),
% 12.32/1.94    inference(resolution,[],[f17738,f51])).
% 12.32/1.94  fof(f17738,plain,(
% 12.32/1.94    r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),sK1)),
% 12.32/1.94    inference(subsumption_resolution,[],[f17696,f83])).
% 12.32/1.94  fof(f17696,plain,(
% 12.32/1.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)),sK1)),
% 12.32/1.94    inference(superposition,[],[f7988,f17077])).
% 12.32/1.94  fof(f7988,plain,(
% 12.32/1.94    ( ! [X12] : (~r1_tarski(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X12,sK1)) )),
% 12.32/1.94    inference(backward_demodulation,[],[f5164,f7977])).
% 12.32/1.94  fof(f5164,plain,(
% 12.32/1.94    ( ! [X12] : (~r1_tarski(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X12,k2_xboole_0(sK1,sK1))) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f5155,f34])).
% 12.32/1.94  fof(f5155,plain,(
% 12.32/1.94    ( ! [X12] : (~r1_tarski(k2_zfmisc_1(sK0,X12),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK0 | r1_tarski(X12,k2_xboole_0(sK1,sK1))) )),
% 12.32/1.94    inference(superposition,[],[f70,f4967])).
% 12.32/1.94  fof(f17748,plain,(
% 12.32/1.94    ( ! [X23] : (k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X23)),sK3) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f17747,f13069])).
% 12.32/1.94  fof(f17747,plain,(
% 12.32/1.94    ( ! [X23] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,sK3))) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f17719,f81])).
% 12.32/1.94  fof(f17719,plain,(
% 12.32/1.94    ( ! [X23] : (k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,X23)),k4_xboole_0(sK1,k4_xboole_0(sK1,sK3))) = k4_xboole_0(k2_zfmisc_1(sK0,sK1),k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X23,k4_xboole_0(sK1,k4_xboole_0(sK1,sK3)))))) )),
% 12.32/1.94    inference(superposition,[],[f12172,f17077])).
% 12.32/1.94  fof(f17017,plain,(
% 12.32/1.94    ( ! [X0] : (k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X0,sK3)) = k5_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(k4_xboole_0(sK2,k4_xboole_0(sK2,X0)),sK3))) )),
% 12.32/1.94    inference(superposition,[],[f72,f13069])).
% 12.32/1.94  fof(f694,plain,(
% 12.32/1.94    ( ! [X6] : (k1_xboole_0 != k4_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X6,sK3)) | r1_tarski(sK2,X6) | k1_xboole_0 = sK3) )),
% 12.32/1.94    inference(resolution,[],[f104,f55])).
% 12.32/1.94  fof(f397,plain,(
% 12.32/1.94    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK1,sK3))),
% 12.32/1.94    inference(forward_demodulation,[],[f387,f41])).
% 12.32/1.94  fof(f387,plain,(
% 12.32/1.94    k2_zfmisc_1(k2_xboole_0(sK0,sK2),sK1) = k2_zfmisc_1(sK2,k2_xboole_0(sK3,sK1))),
% 12.32/1.94    inference(superposition,[],[f98,f59])).
% 12.32/1.94  fof(f107,plain,(
% 12.32/1.94    ( ! [X12] : (~r1_tarski(k2_zfmisc_1(sK2,X12),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK2 | r1_tarski(X12,sK3)) )),
% 12.32/1.94    inference(superposition,[],[f70,f33])).
% 12.32/1.94  fof(f40,plain,(
% 12.32/1.94    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 12.32/1.94    inference(cnf_transformation,[],[f15])).
% 12.32/1.94  fof(f15,axiom,(
% 12.32/1.94    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 12.32/1.94    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 12.32/1.94  fof(f19077,plain,(
% 12.32/1.94    ~r1_tarski(sK1,sK3) | sK1 = sK3),
% 12.32/1.94    inference(resolution,[],[f18941,f51])).
% 12.32/1.94  fof(f18941,plain,(
% 12.32/1.94    r1_tarski(sK3,sK1)),
% 12.32/1.94    inference(subsumption_resolution,[],[f18940,f3148])).
% 12.32/1.94  fof(f18940,plain,(
% 12.32/1.94    k1_xboole_0 = sK2 | r1_tarski(sK3,sK1)),
% 12.32/1.94    inference(subsumption_resolution,[],[f18864,f83])).
% 12.32/1.94  fof(f18864,plain,(
% 12.32/1.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK2 | r1_tarski(sK3,sK1)),
% 12.32/1.94    inference(superposition,[],[f106,f17860])).
% 12.32/1.94  fof(f17860,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(sK2,sK1)),
% 12.32/1.94    inference(forward_demodulation,[],[f17859,f12121])).
% 12.32/1.94  fof(f17859,plain,(
% 12.32/1.94    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k1_xboole_0))),
% 12.32/1.94    inference(forward_demodulation,[],[f17833,f12122])).
% 12.32/1.94  fof(f17833,plain,(
% 12.32/1.94    k2_zfmisc_1(sK2,sK1) = k2_zfmisc_1(sK0,k4_xboole_0(sK1,k4_xboole_0(sK1,sK1)))),
% 12.32/1.94    inference(superposition,[],[f17409,f17764])).
% 12.32/1.94  fof(f17409,plain,(
% 12.32/1.94    ( ! [X33] : (k2_zfmisc_1(sK2,k4_xboole_0(X33,k4_xboole_0(X33,sK3))) = k2_zfmisc_1(sK0,k4_xboole_0(X33,k4_xboole_0(X33,sK1)))) )),
% 12.32/1.94    inference(backward_demodulation,[],[f12828,f17395])).
% 12.32/1.94  fof(f17395,plain,(
% 12.32/1.94    ( ! [X29] : (k2_zfmisc_1(sK0,k4_xboole_0(X29,k4_xboole_0(X29,sK1))) = k4_xboole_0(k2_zfmisc_1(sK2,X29),k4_xboole_0(k2_zfmisc_1(sK2,X29),k2_zfmisc_1(sK0,sK1)))) )),
% 12.32/1.94    inference(backward_demodulation,[],[f17255,f17376])).
% 12.32/1.94  fof(f17376,plain,(
% 12.32/1.94    sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 12.32/1.94    inference(subsumption_resolution,[],[f17368,f17231])).
% 12.32/1.94  fof(f17231,plain,(
% 12.32/1.94    r1_tarski(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 12.32/1.94    inference(subsumption_resolution,[],[f17230,f2354])).
% 12.32/1.94  fof(f17230,plain,(
% 12.32/1.94    k1_xboole_0 = sK3 | r1_tarski(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 12.32/1.94    inference(subsumption_resolution,[],[f17149,f83])).
% 12.32/1.94  fof(f17149,plain,(
% 12.32/1.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK3 | r1_tarski(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 12.32/1.94    inference(superposition,[],[f104,f17053])).
% 12.32/1.94  fof(f17368,plain,(
% 12.32/1.94    ~r1_tarski(sK2,k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | sK2 = k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))),
% 12.32/1.94    inference(resolution,[],[f17233,f51])).
% 12.32/1.94  fof(f17233,plain,(
% 12.32/1.94    r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK2)),
% 12.32/1.94    inference(subsumption_resolution,[],[f17232,f2354])).
% 12.32/1.94  fof(f17232,plain,(
% 12.32/1.94    k1_xboole_0 = sK3 | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK2)),
% 12.32/1.94    inference(subsumption_resolution,[],[f17150,f83])).
% 12.32/1.94  fof(f17150,plain,(
% 12.32/1.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = sK3 | r1_tarski(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),sK2)),
% 12.32/1.94    inference(superposition,[],[f105,f17053])).
% 12.32/1.94  fof(f17255,plain,(
% 12.32/1.94    ( ! [X29] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k2_zfmisc_1(sK0,sK1))) = k2_zfmisc_1(sK0,k4_xboole_0(X29,k4_xboole_0(X29,sK1)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f17254,f9226])).
% 12.32/1.94  fof(f9226,plain,(
% 12.32/1.94    ( ! [X2,X1] : (k4_xboole_0(k2_zfmisc_1(sK0,X1),k4_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK0,X2))) = k2_zfmisc_1(sK0,k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f9221,f9213])).
% 12.32/1.94  fof(f9213,plain,(
% 12.32/1.94    sK0 = k4_xboole_0(sK0,k1_xboole_0)),
% 12.32/1.94    inference(superposition,[],[f74,f9189])).
% 12.32/1.94  fof(f9189,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(sK0,sK0)),
% 12.32/1.94    inference(backward_demodulation,[],[f9172,f9178])).
% 12.32/1.94  fof(f9178,plain,(
% 12.32/1.94    sK0 = k2_xboole_0(sK0,sK0)),
% 12.32/1.94    inference(subsumption_resolution,[],[f9173,f40])).
% 12.32/1.94  fof(f9173,plain,(
% 12.32/1.94    ~r1_tarski(sK0,k2_xboole_0(sK0,sK0)) | sK0 = k2_xboole_0(sK0,sK0)),
% 12.32/1.94    inference(resolution,[],[f9167,f51])).
% 12.32/1.94  fof(f9167,plain,(
% 12.32/1.94    r1_tarski(k2_xboole_0(sK0,sK0),sK0)),
% 12.32/1.94    inference(subsumption_resolution,[],[f9148,f83])).
% 12.32/1.94  fof(f9148,plain,(
% 12.32/1.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(k2_xboole_0(sK0,sK0),sK0)),
% 12.32/1.94    inference(superposition,[],[f8008,f9138])).
% 12.32/1.94  fof(f9138,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k2_zfmisc_1(k2_xboole_0(sK0,sK0),sK1)),
% 12.32/1.94    inference(superposition,[],[f4986,f59])).
% 12.32/1.94  fof(f4986,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,sK1) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 12.32/1.94    inference(backward_demodulation,[],[f1339,f4967])).
% 12.32/1.94  fof(f1339,plain,(
% 12.32/1.94    k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)))),
% 12.32/1.94    inference(resolution,[],[f1325,f47])).
% 12.32/1.94  fof(f1325,plain,(
% 12.32/1.94    r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)))),
% 12.32/1.94    inference(forward_demodulation,[],[f1293,f33])).
% 12.32/1.94  fof(f1293,plain,(
% 12.32/1.94    r1_tarski(k2_zfmisc_1(sK2,sK3),k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1)))),
% 12.32/1.94    inference(superposition,[],[f260,f137])).
% 12.32/1.94  fof(f137,plain,(
% 12.32/1.94    k2_zfmisc_1(k2_xboole_0(sK2,sK2),sK3) = k2_zfmisc_1(sK0,k2_xboole_0(sK1,sK1))),
% 12.32/1.94    inference(forward_demodulation,[],[f125,f60])).
% 12.32/1.94  fof(f125,plain,(
% 12.32/1.94    k2_zfmisc_1(k2_xboole_0(sK2,sK2),sK3) = k2_xboole_0(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1))),
% 12.32/1.94    inference(superposition,[],[f96,f33])).
% 12.32/1.94  fof(f260,plain,(
% 12.32/1.94    ( ! [X1] : (r1_tarski(k2_zfmisc_1(X1,sK3),k2_zfmisc_1(k2_xboole_0(sK2,X1),sK3))) )),
% 12.32/1.94    inference(superposition,[],[f226,f41])).
% 12.32/1.94  fof(f8008,plain,(
% 12.32/1.94    ( ! [X10] : (~r1_tarski(k2_zfmisc_1(X10,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X10,sK0)) )),
% 12.32/1.94    inference(forward_demodulation,[],[f8007,f7977])).
% 12.32/1.94  fof(f8007,plain,(
% 12.32/1.94    ( ! [X10] : (~r1_tarski(k2_zfmisc_1(X10,k2_xboole_0(sK1,sK1)),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X10,sK0)) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f7983,f35])).
% 12.32/1.94  fof(f7983,plain,(
% 12.32/1.94    ( ! [X10] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_zfmisc_1(X10,k2_xboole_0(sK1,sK1)),k2_zfmisc_1(sK0,sK1)) | r1_tarski(X10,sK0)) )),
% 12.32/1.94    inference(backward_demodulation,[],[f5153,f7977])).
% 12.32/1.94  fof(f5153,plain,(
% 12.32/1.94    ( ! [X10] : (~r1_tarski(k2_zfmisc_1(X10,k2_xboole_0(sK1,sK1)),k2_zfmisc_1(sK0,sK1)) | k1_xboole_0 = k2_xboole_0(sK1,sK1) | r1_tarski(X10,sK0)) )),
% 12.32/1.94    inference(superposition,[],[f69,f4967])).
% 12.32/1.94  fof(f9172,plain,(
% 12.32/1.94    k1_xboole_0 = k4_xboole_0(k2_xboole_0(sK0,sK0),sK0)),
% 12.32/1.94    inference(resolution,[],[f9167,f54])).
% 12.32/1.94  fof(f9221,plain,(
% 12.32/1.94    ( ! [X2,X1] : (k4_xboole_0(k2_zfmisc_1(sK0,X1),k4_xboole_0(k2_zfmisc_1(sK0,X1),k2_zfmisc_1(sK0,X2))) = k2_zfmisc_1(k4_xboole_0(sK0,k1_xboole_0),k4_xboole_0(X1,k4_xboole_0(X1,X2)))) )),
% 12.32/1.94    inference(superposition,[],[f81,f9189])).
% 12.32/1.94  fof(f17254,plain,(
% 12.32/1.94    ( ! [X29] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(sK0,X29),k4_xboole_0(k2_zfmisc_1(sK0,X29),k2_zfmisc_1(sK0,sK1)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f17253,f33])).
% 12.32/1.94  fof(f17253,plain,(
% 12.32/1.94    ( ! [X29] : (k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k2_zfmisc_1(sK0,sK1))) = k4_xboole_0(k2_zfmisc_1(sK0,X29),k4_xboole_0(k2_zfmisc_1(sK0,X29),k2_zfmisc_1(sK2,sK3)))) )),
% 12.32/1.94    inference(forward_demodulation,[],[f17205,f81])).
% 12.32/1.94  fof(f17205,plain,(
% 12.32/1.94    ( ! [X29] : (k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),k4_xboole_0(X29,k4_xboole_0(X29,sK3))) = k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k4_xboole_0(k2_zfmisc_1(k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)),X29),k2_zfmisc_1(sK0,sK1)))) )),
% 12.32/1.94    inference(superposition,[],[f12171,f17053])).
% 12.32/1.94  fof(f12828,plain,(
% 12.32/1.94    ( ! [X33] : (k2_zfmisc_1(sK2,k4_xboole_0(X33,k4_xboole_0(X33,sK3))) = k4_xboole_0(k2_zfmisc_1(sK2,X33),k4_xboole_0(k2_zfmisc_1(sK2,X33),k2_zfmisc_1(sK0,sK1)))) )),
% 12.32/1.94    inference(superposition,[],[f12171,f33])).
% 12.32/1.94  fof(f106,plain,(
% 12.32/1.94    ( ! [X11] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK2,X11)) | k1_xboole_0 = sK2 | r1_tarski(sK3,X11)) )),
% 12.32/1.94    inference(superposition,[],[f70,f33])).
% 12.32/1.94  fof(f21651,plain,(
% 12.32/1.94    sK1 != sK3),
% 12.32/1.94    inference(trivial_inequality_removal,[],[f20630])).
% 12.32/1.94  fof(f20630,plain,(
% 12.32/1.94    sK0 != sK0 | sK1 != sK3),
% 12.32/1.94    inference(backward_demodulation,[],[f32,f20624])).
% 12.32/1.94  fof(f20624,plain,(
% 12.32/1.94    sK0 = sK2),
% 12.32/1.94    inference(resolution,[],[f18944,f17939])).
% 12.32/1.94  fof(f17939,plain,(
% 12.32/1.94    ~r1_tarski(sK0,sK2) | sK0 = sK2),
% 12.32/1.94    inference(resolution,[],[f17937,f51])).
% 12.32/1.94  fof(f18944,plain,(
% 12.32/1.94    r1_tarski(sK0,sK2)),
% 12.32/1.94    inference(subsumption_resolution,[],[f18896,f83])).
% 12.32/1.94  fof(f18896,plain,(
% 12.32/1.94    ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(sK0,sK1)) | r1_tarski(sK0,sK2)),
% 12.32/1.94    inference(superposition,[],[f8006,f17860])).
% 12.32/1.94  fof(f8006,plain,(
% 12.32/1.94    ( ! [X9] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,sK1)) | r1_tarski(sK0,X9)) )),
% 12.32/1.94    inference(forward_demodulation,[],[f8005,f7977])).
% 12.32/1.94  fof(f8005,plain,(
% 12.32/1.94    ( ! [X9] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,k2_xboole_0(sK1,sK1))) | r1_tarski(sK0,X9)) )),
% 12.32/1.94    inference(subsumption_resolution,[],[f7982,f35])).
% 12.32/1.94  fof(f7982,plain,(
% 12.32/1.94    ( ! [X9] : (k1_xboole_0 = sK1 | ~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,k2_xboole_0(sK1,sK1))) | r1_tarski(sK0,X9)) )),
% 12.32/1.94    inference(backward_demodulation,[],[f5152,f7977])).
% 12.32/1.94  fof(f5152,plain,(
% 12.32/1.94    ( ! [X9] : (~r1_tarski(k2_zfmisc_1(sK0,sK1),k2_zfmisc_1(X9,k2_xboole_0(sK1,sK1))) | k1_xboole_0 = k2_xboole_0(sK1,sK1) | r1_tarski(sK0,X9)) )),
% 12.32/1.94    inference(superposition,[],[f69,f4967])).
% 12.32/1.94  fof(f32,plain,(
% 12.32/1.94    sK1 != sK3 | sK0 != sK2),
% 12.32/1.94    inference(cnf_transformation,[],[f26])).
% 12.32/1.94  % SZS output end Proof for theBenchmark
% 12.32/1.94  % (8389)------------------------------
% 12.32/1.94  % (8389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.32/1.94  % (8389)Termination reason: Refutation
% 12.32/1.94  
% 12.32/1.94  % (8389)Memory used [KB]: 11769
% 12.32/1.94  % (8389)Time elapsed: 1.472 s
% 12.32/1.94  % (8389)------------------------------
% 12.32/1.94  % (8389)------------------------------
% 12.32/1.94  % (8368)Success in time 1.57 s
%------------------------------------------------------------------------------
