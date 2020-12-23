%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0100+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:09 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  59 expanded)
%              Number of equality atoms :   42 (  53 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1699,plain,(
    $false ),
    inference(subsumption_resolution,[],[f1698,f454])).

fof(f454,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f364,f308])).

fof(f308,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f146])).

fof(f146,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f364,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f85])).

fof(f85,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f1698,plain,(
    k1_xboole_0 != k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1696,f1697])).

fof(f1697,plain,(
    ! [X17,X18] : k2_xboole_0(X17,X18) = k2_xboole_0(k3_xboole_0(X17,X18),k5_xboole_0(X17,X18)) ),
    inference(forward_demodulation,[],[f1652,f534])).

fof(f534,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,X2),k2_xboole_0(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f263,f302])).

fof(f302,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_xboole_0(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f174])).

fof(f174,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f45])).

fof(f45,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f263,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f1652,plain,(
    ! [X17,X18] : k2_xboole_0(k3_xboole_0(X17,X18),k2_xboole_0(X17,X18)) = k2_xboole_0(k3_xboole_0(X17,X18),k5_xboole_0(X17,X18)) ),
    inference(superposition,[],[f304,f387])).

fof(f387,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f265,f283])).

fof(f283,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f265,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

fof(f96,axiom,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f304,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f1696,plain,(
    k1_xboole_0 != k4_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1695,f454])).

fof(f1695,plain,(
    k4_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1)) != k4_xboole_0(k5_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1022,f1651])).

fof(f1651,plain,(
    ! [X14,X15,X16] : k4_xboole_0(k2_xboole_0(X14,X15),k2_xboole_0(k3_xboole_0(X14,X15),X16)) = k4_xboole_0(k5_xboole_0(X14,X15),X16) ),
    inference(superposition,[],[f300,f387])).

fof(f300,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f1022,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1))) != k4_xboole_0(k2_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1014,f306])).

fof(f306,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1014,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) != k4_xboole_0(k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),k2_xboole_0(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f243,f317])).

fof(f317,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f181])).

fof(f181,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f69])).

fof(f69,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f243,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f197])).

fof(f197,plain,(
    k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f149,f196])).

fof(f196,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k2_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f149,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f143])).

fof(f143,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f142])).

fof(f142,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).
%------------------------------------------------------------------------------
