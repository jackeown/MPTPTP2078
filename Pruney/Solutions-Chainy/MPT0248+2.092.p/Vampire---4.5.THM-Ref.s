%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:38:03 EST 2020

% Result     : Theorem 2.00s
% Output     : Refutation 2.44s
% Verified   : 
% Statistics : Number of formulae       :  140 (6679 expanded)
%              Number of leaves         :   24 (2143 expanded)
%              Depth                    :   34
%              Number of atoms          :  260 (8657 expanded)
%              Number of equality atoms :  118 (6814 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1657,plain,(
    $false ),
    inference(global_subsumption,[],[f1519,f1656])).

fof(f1656,plain,(
    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(forward_demodulation,[],[f1644,f134])).

fof(f134,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(superposition,[],[f130,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f130,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f125,f100])).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f99,f85])).

fof(f85,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f41,f76])).

fof(f76,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f60,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f67,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f68,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f69,f70])).

fof(f70,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f67,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f99,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f84,f38])).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f40,f77])).

fof(f77,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f76])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f40,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f125,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f61,f38])).

fof(f61,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1644,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0) ),
    inference(superposition,[],[f130,f1589])).

fof(f1589,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(forward_demodulation,[],[f1275,f1311])).

fof(f1311,plain,(
    k1_xboole_0 = sK1 ),
    inference(unit_resulting_resolution,[],[f1267,f108])).

fof(f108,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f50,f37])).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1267,plain,(
    ! [X1] : r1_tarski(sK1,X1) ),
    inference(global_subsumption,[],[f633,f820,f1266])).

fof(f1266,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | sK1 = sK2 ) ),
    inference(global_subsumption,[],[f632,f820,f1261])).

fof(f1261,plain,(
    ! [X0] :
      ( k1_xboole_0 = sK2
      | r1_tarski(sK1,X0)
      | sK1 = sK2 ) ),
    inference(resolution,[],[f1214,f1180])).

fof(f1180,plain,(
    ! [X4] :
      ( ~ r1_tarski(sK1,sK2)
      | r1_tarski(sK1,X4)
      | sK1 = sK2 ) ),
    inference(resolution,[],[f1165,f50])).

fof(f1165,plain,(
    ! [X2] :
      ( r1_tarski(sK2,sK1)
      | r1_tarski(sK1,X2) ) ),
    inference(duplicate_literal_removal,[],[f1161])).

fof(f1161,plain,(
    ! [X2] :
      ( r1_tarski(sK1,X2)
      | r1_tarski(sK2,sK1)
      | r1_tarski(sK2,sK1) ) ),
    inference(resolution,[],[f1075,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f1075,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK2,X0),sK1)
      | r1_tarski(sK1,X1)
      | r1_tarski(sK2,X0) ) ),
    inference(resolution,[],[f1074,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1074,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,sK2)
      | r2_hidden(X0,sK1)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f1068,f820])).

fof(f1068,plain,(
    ! [X31] :
      ( ~ r2_hidden(sK0,sK1)
      | r2_hidden(X31,sK1)
      | ~ r2_hidden(X31,sK2) ) ),
    inference(duplicate_literal_removal,[],[f1054])).

fof(f1054,plain,(
    ! [X31] :
      ( ~ r2_hidden(X31,sK2)
      | r2_hidden(X31,sK1)
      | r2_hidden(X31,sK1)
      | ~ r2_hidden(sK0,sK1) ) ),
    inference(resolution,[],[f241,f762])).

fof(f762,plain,
    ( r1_tarski(k5_xboole_0(sK1,sK2),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f760,f211])).

fof(f211,plain,(
    ! [X8,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8) ),
    inference(superposition,[],[f130,f183])).

fof(f183,plain,(
    ! [X6,X5] : k5_xboole_0(X6,k5_xboole_0(X5,X6)) = X5 ),
    inference(forward_demodulation,[],[f172,f134])).

fof(f172,plain,(
    ! [X6,X5] : k5_xboole_0(X6,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k1_xboole_0) ),
    inference(superposition,[],[f130,f128])).

fof(f128,plain,(
    ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(superposition,[],[f61,f38])).

fof(f760,plain,
    ( r1_tarski(k5_xboole_0(sK2,sK1),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f695,f612])).

fof(f612,plain,
    ( sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | ~ r2_hidden(sK0,sK1) ),
    inference(resolution,[],[f93,f578])).

fof(f578,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(resolution,[],[f571,f50])).

fof(f571,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f86,f80])).

fof(f80,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f36,f79,f76])).

fof(f79,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f75])).

fof(f39,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        | k1_tarski(X0) != X1 )
      & ( k1_tarski(X0) != X2
        | k1_xboole_0 != X1 )
      & ( k1_tarski(X0) != X2
        | k1_tarski(X0) != X1 )
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( ~ ( k1_xboole_0 = X2
              & k1_tarski(X0) = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_xboole_0 = X1 )
          & ~ ( k1_tarski(X0) = X2
              & k1_tarski(X0) = X1 )
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1,X2] :
      ~ ( ~ ( k1_xboole_0 = X2
            & k1_tarski(X0) = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_xboole_0 = X1 )
        & ~ ( k1_tarski(X0) = X2
            & k1_tarski(X0) = X1 )
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

fof(f86,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f42,f76])).

fof(f42,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f58,f79])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f695,plain,(
    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1) ),
    inference(superposition,[],[f131,f80])).

fof(f131,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(backward_demodulation,[],[f101,f130])).

fof(f101,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X0) ),
    inference(backward_demodulation,[],[f87,f61])).

fof(f87,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(definition_unfolding,[],[f43,f78])).

fof(f78,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f46,f77])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f43,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f241,plain,(
    ! [X12,X10,X11,X9] :
      ( ~ r1_tarski(k5_xboole_0(X10,X11),X12)
      | ~ r2_hidden(X9,X11)
      | r2_hidden(X9,X12)
      | r2_hidden(X9,X10) ) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f1214,plain,
    ( r1_tarski(sK1,sK2)
    | k1_xboole_0 = sK2 ),
    inference(factoring,[],[f1206])).

fof(f1206,plain,(
    ! [X9] :
      ( r1_tarski(sK1,sK2)
      | r1_tarski(sK1,X9)
      | k1_xboole_0 = sK2 ) ),
    inference(resolution,[],[f1183,f108])).

fof(f1183,plain,(
    ! [X6,X7] :
      ( r1_tarski(sK2,X6)
      | r1_tarski(sK1,X7)
      | r1_tarski(sK1,sK2) ) ),
    inference(resolution,[],[f1178,f821])).

fof(f821,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK0,X2)
      | r1_tarski(sK1,X2) ) ),
    inference(duplicate_literal_removal,[],[f818])).

fof(f818,plain,(
    ! [X2] :
      ( ~ r2_hidden(sK0,X2)
      | r1_tarski(sK1,X2)
      | r1_tarski(sK1,X2) ) ),
    inference(superposition,[],[f53,f813])).

fof(f813,plain,(
    ! [X0] :
      ( sK0 = sK3(sK1,X0)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f807,f52])).

fof(f807,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK1)
      | sK0 = X0 ) ),
    inference(resolution,[],[f611,f96])).

fof(f96,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f611,plain,(
    ! [X3] :
      ( r2_hidden(X3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r2_hidden(X3,sK1) ) ),
    inference(resolution,[],[f93,f595])).

fof(f595,plain,(
    ! [X5] :
      ( ~ r1_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),sK1)
      | r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ) ),
    inference(resolution,[],[f92,f577])).

fof(f577,plain,(
    ! [X0] :
      ( r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
      | ~ r1_tarski(X0,sK1) ) ),
    inference(resolution,[],[f571,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f92,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f59,f79])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | ~ r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1178,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK0,sK2)
      | r1_tarski(sK2,X1)
      | r1_tarski(sK1,X0) ) ),
    inference(resolution,[],[f1165,f1007])).

fof(f1007,plain,(
    ! [X6,X5] :
      ( ~ r1_tarski(X5,sK1)
      | r1_tarski(X5,X6)
      | r2_hidden(sK0,X5) ) ),
    inference(duplicate_literal_removal,[],[f1006])).

fof(f1006,plain,(
    ! [X6,X5] :
      ( r2_hidden(sK0,X5)
      | r1_tarski(X5,X6)
      | ~ r1_tarski(X5,sK1)
      | r1_tarski(X5,X6) ) ),
    inference(superposition,[],[f52,f814])).

fof(f814,plain,(
    ! [X2,X1] :
      ( sK0 = sK3(X1,X2)
      | ~ r1_tarski(X1,sK1)
      | r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f807,f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1),X2)
      | ~ r1_tarski(X0,X2)
      | r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f51,f52])).

fof(f632,plain,
    ( k1_xboole_0 != sK2
    | ~ r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f619])).

fof(f619,plain,
    ( sK1 != sK1
    | k1_xboole_0 != sK2
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f83,f612])).

fof(f83,plain,
    ( sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK2 ),
    inference(definition_unfolding,[],[f33,f79])).

fof(f33,plain,
    ( sK1 != k1_tarski(sK0)
    | k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f28])).

fof(f820,plain,(
    ! [X3] :
      ( r2_hidden(sK0,sK1)
      | r1_tarski(sK1,X3) ) ),
    inference(duplicate_literal_removal,[],[f819])).

fof(f819,plain,(
    ! [X3] :
      ( r2_hidden(sK0,sK1)
      | r1_tarski(sK1,X3)
      | r1_tarski(sK1,X3) ) ),
    inference(superposition,[],[f52,f813])).

fof(f633,plain,
    ( sK1 != sK2
    | ~ r2_hidden(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f617])).

fof(f617,plain,
    ( sK1 != sK2
    | sK1 != sK1
    | ~ r2_hidden(sK0,sK1) ),
    inference(superposition,[],[f81,f612])).

fof(f81,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(definition_unfolding,[],[f35,f79,f79])).

fof(f35,plain,
    ( sK1 != k1_tarski(sK0)
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f1275,plain,(
    sK1 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f695,f1267,f50])).

fof(f1519,plain,(
    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(global_subsumption,[],[f82,f1311])).

fof(f82,plain,
    ( sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)
    | k1_xboole_0 != sK1 ),
    inference(definition_unfolding,[],[f34,f79])).

fof(f34,plain,
    ( k1_xboole_0 != sK1
    | sK2 != k1_tarski(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n014.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:06:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (3247)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (3249)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (3254)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.27/0.53  % (3248)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.27/0.53  % (3263)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.27/0.53  % (3269)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.27/0.53  % (3262)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.27/0.54  % (3258)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.27/0.54  % (3268)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.27/0.54  % (3255)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.27/0.54  % (3260)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.27/0.54  % (3252)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.27/0.54  % (3261)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.27/0.54  % (3251)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.40/0.54  % (3250)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.40/0.54  % (3259)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.40/0.55  % (3264)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.40/0.55  % (3257)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.40/0.55  % (3253)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.40/0.55  % (3257)Refutation not found, incomplete strategy% (3257)------------------------------
% 1.40/0.55  % (3257)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.40/0.55  % (3257)Termination reason: Refutation not found, incomplete strategy
% 1.40/0.55  
% 1.40/0.55  % (3257)Memory used [KB]: 10618
% 1.40/0.55  % (3257)Time elapsed: 0.133 s
% 1.40/0.55  % (3257)------------------------------
% 1.40/0.55  % (3257)------------------------------
% 1.40/0.55  % (3270)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.40/0.55  % (3276)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.40/0.55  % (3272)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.40/0.55  % (3265)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.40/0.55  % (3273)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.40/0.55  % (3271)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.40/0.56  % (3266)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.40/0.56  % (3256)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.40/0.56  % (3275)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.40/0.57  % (3274)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.40/0.58  % (3267)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 2.00/0.67  % (3271)Refutation found. Thanks to Tanya!
% 2.00/0.67  % SZS status Theorem for theBenchmark
% 2.00/0.68  % SZS output start Proof for theBenchmark
% 2.00/0.68  fof(f1657,plain,(
% 2.00/0.68    $false),
% 2.00/0.68    inference(global_subsumption,[],[f1519,f1656])).
% 2.00/0.68  fof(f1656,plain,(
% 2.00/0.68    sK2 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.00/0.68    inference(forward_demodulation,[],[f1644,f134])).
% 2.00/0.68  fof(f134,plain,(
% 2.00/0.68    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.00/0.68    inference(superposition,[],[f130,f38])).
% 2.00/0.68  fof(f38,plain,(
% 2.00/0.68    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f12])).
% 2.00/0.68  fof(f12,axiom,(
% 2.00/0.68    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.00/0.68  fof(f130,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.00/0.68    inference(forward_demodulation,[],[f125,f100])).
% 2.00/0.68  fof(f100,plain,(
% 2.00/0.68    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.00/0.68    inference(backward_demodulation,[],[f99,f85])).
% 2.00/0.68  fof(f85,plain,(
% 2.00/0.68    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.00/0.68    inference(definition_unfolding,[],[f41,f76])).
% 2.00/0.68  fof(f76,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.00/0.68    inference(definition_unfolding,[],[f44,f75])).
% 2.00/0.68  fof(f75,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.00/0.68    inference(definition_unfolding,[],[f45,f74])).
% 2.00/0.68  fof(f74,plain,(
% 2.00/0.68    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.00/0.68    inference(definition_unfolding,[],[f60,f73])).
% 2.00/0.68  fof(f73,plain,(
% 2.00/0.68    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.00/0.68    inference(definition_unfolding,[],[f67,f72])).
% 2.00/0.68  fof(f72,plain,(
% 2.00/0.68    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.00/0.68    inference(definition_unfolding,[],[f68,f71])).
% 2.00/0.68  fof(f71,plain,(
% 2.00/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.00/0.68    inference(definition_unfolding,[],[f69,f70])).
% 2.00/0.68  fof(f70,plain,(
% 2.00/0.68    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f21])).
% 2.00/0.68  fof(f21,axiom,(
% 2.00/0.68    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.00/0.68  fof(f69,plain,(
% 2.00/0.68    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f20])).
% 2.00/0.68  fof(f20,axiom,(
% 2.00/0.68    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.00/0.68  fof(f68,plain,(
% 2.00/0.68    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f19])).
% 2.00/0.68  fof(f19,axiom,(
% 2.00/0.68    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.00/0.68  fof(f67,plain,(
% 2.00/0.68    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f18])).
% 2.00/0.68  fof(f18,axiom,(
% 2.00/0.68    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.00/0.68  fof(f60,plain,(
% 2.00/0.68    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f17])).
% 2.00/0.68  fof(f17,axiom,(
% 2.00/0.68    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.00/0.68  fof(f45,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f16])).
% 2.00/0.68  fof(f16,axiom,(
% 2.00/0.68    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.00/0.68  fof(f44,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.00/0.68    inference(cnf_transformation,[],[f23])).
% 2.00/0.68  fof(f23,axiom,(
% 2.00/0.68    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.00/0.68  fof(f41,plain,(
% 2.00/0.68    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.00/0.68    inference(cnf_transformation,[],[f27])).
% 2.00/0.68  fof(f27,plain,(
% 2.00/0.68    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.00/0.68    inference(rectify,[],[f2])).
% 2.00/0.68  fof(f2,axiom,(
% 2.00/0.68    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.00/0.68  fof(f99,plain,(
% 2.00/0.68    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.00/0.68    inference(forward_demodulation,[],[f84,f38])).
% 2.00/0.68  fof(f84,plain,(
% 2.00/0.68    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.00/0.68    inference(definition_unfolding,[],[f40,f77])).
% 2.00/0.68  fof(f77,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.00/0.68    inference(definition_unfolding,[],[f47,f76])).
% 2.00/0.68  fof(f47,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.00/0.68    inference(cnf_transformation,[],[f13])).
% 2.00/0.68  fof(f13,axiom,(
% 2.00/0.68    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.00/0.68  fof(f40,plain,(
% 2.00/0.68    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.00/0.68    inference(cnf_transformation,[],[f26])).
% 2.00/0.68  fof(f26,plain,(
% 2.00/0.68    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.00/0.68    inference(rectify,[],[f3])).
% 2.00/0.68  fof(f3,axiom,(
% 2.00/0.68    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.00/0.68  fof(f125,plain,(
% 2.00/0.68    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.00/0.68    inference(superposition,[],[f61,f38])).
% 2.00/0.68  fof(f61,plain,(
% 2.00/0.68    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.00/0.68    inference(cnf_transformation,[],[f11])).
% 2.00/0.68  fof(f11,axiom,(
% 2.00/0.68    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.00/0.68  fof(f1644,plain,(
% 2.00/0.68    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k5_xboole_0(sK2,k1_xboole_0)),
% 2.00/0.68    inference(superposition,[],[f130,f1589])).
% 2.00/0.68  fof(f1589,plain,(
% 2.00/0.68    k1_xboole_0 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.00/0.68    inference(forward_demodulation,[],[f1275,f1311])).
% 2.00/0.68  fof(f1311,plain,(
% 2.00/0.68    k1_xboole_0 = sK1),
% 2.00/0.68    inference(unit_resulting_resolution,[],[f1267,f108])).
% 2.00/0.68  fof(f108,plain,(
% 2.00/0.68    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 2.00/0.68    inference(resolution,[],[f50,f37])).
% 2.00/0.68  fof(f37,plain,(
% 2.00/0.68    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.00/0.68    inference(cnf_transformation,[],[f8])).
% 2.00/0.68  fof(f8,axiom,(
% 2.00/0.68    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 2.00/0.68  fof(f50,plain,(
% 2.00/0.68    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.00/0.68    inference(cnf_transformation,[],[f5])).
% 2.00/0.68  fof(f5,axiom,(
% 2.00/0.68    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.00/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.00/0.68  fof(f1267,plain,(
% 2.00/0.68    ( ! [X1] : (r1_tarski(sK1,X1)) )),
% 2.00/0.68    inference(global_subsumption,[],[f633,f820,f1266])).
% 2.44/0.68  fof(f1266,plain,(
% 2.44/0.68    ( ! [X0] : (r1_tarski(sK1,X0) | sK1 = sK2) )),
% 2.44/0.68    inference(global_subsumption,[],[f632,f820,f1261])).
% 2.44/0.68  fof(f1261,plain,(
% 2.44/0.68    ( ! [X0] : (k1_xboole_0 = sK2 | r1_tarski(sK1,X0) | sK1 = sK2) )),
% 2.44/0.68    inference(resolution,[],[f1214,f1180])).
% 2.44/0.68  fof(f1180,plain,(
% 2.44/0.68    ( ! [X4] : (~r1_tarski(sK1,sK2) | r1_tarski(sK1,X4) | sK1 = sK2) )),
% 2.44/0.68    inference(resolution,[],[f1165,f50])).
% 2.44/0.68  fof(f1165,plain,(
% 2.44/0.68    ( ! [X2] : (r1_tarski(sK2,sK1) | r1_tarski(sK1,X2)) )),
% 2.44/0.68    inference(duplicate_literal_removal,[],[f1161])).
% 2.44/0.68  fof(f1161,plain,(
% 2.44/0.68    ( ! [X2] : (r1_tarski(sK1,X2) | r1_tarski(sK2,sK1) | r1_tarski(sK2,sK1)) )),
% 2.44/0.68    inference(resolution,[],[f1075,f53])).
% 2.44/0.68  fof(f53,plain,(
% 2.44/0.68    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f29])).
% 2.44/0.68  fof(f29,plain,(
% 2.44/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.44/0.68    inference(ennf_transformation,[],[f1])).
% 2.44/0.68  fof(f1,axiom,(
% 2.44/0.68    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.44/0.68  fof(f1075,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r2_hidden(sK3(sK2,X0),sK1) | r1_tarski(sK1,X1) | r1_tarski(sK2,X0)) )),
% 2.44/0.68    inference(resolution,[],[f1074,f52])).
% 2.44/0.68  fof(f52,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f29])).
% 2.44/0.68  fof(f1074,plain,(
% 2.44/0.68    ( ! [X0,X1] : (~r2_hidden(X0,sK2) | r2_hidden(X0,sK1) | r1_tarski(sK1,X1)) )),
% 2.44/0.68    inference(resolution,[],[f1068,f820])).
% 2.44/0.68  fof(f1068,plain,(
% 2.44/0.68    ( ! [X31] : (~r2_hidden(sK0,sK1) | r2_hidden(X31,sK1) | ~r2_hidden(X31,sK2)) )),
% 2.44/0.68    inference(duplicate_literal_removal,[],[f1054])).
% 2.44/0.68  fof(f1054,plain,(
% 2.44/0.68    ( ! [X31] : (~r2_hidden(X31,sK2) | r2_hidden(X31,sK1) | r2_hidden(X31,sK1) | ~r2_hidden(sK0,sK1)) )),
% 2.44/0.68    inference(resolution,[],[f241,f762])).
% 2.44/0.68  fof(f762,plain,(
% 2.44/0.68    r1_tarski(k5_xboole_0(sK1,sK2),sK1) | ~r2_hidden(sK0,sK1)),
% 2.44/0.68    inference(forward_demodulation,[],[f760,f211])).
% 2.44/0.68  fof(f211,plain,(
% 2.44/0.68    ( ! [X8,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(X9,X8)) )),
% 2.44/0.68    inference(superposition,[],[f130,f183])).
% 2.44/0.68  fof(f183,plain,(
% 2.44/0.68    ( ! [X6,X5] : (k5_xboole_0(X6,k5_xboole_0(X5,X6)) = X5) )),
% 2.44/0.68    inference(forward_demodulation,[],[f172,f134])).
% 2.44/0.68  fof(f172,plain,(
% 2.44/0.68    ( ! [X6,X5] : (k5_xboole_0(X6,k5_xboole_0(X5,X6)) = k5_xboole_0(X5,k1_xboole_0)) )),
% 2.44/0.68    inference(superposition,[],[f130,f128])).
% 2.44/0.68  fof(f128,plain,(
% 2.44/0.68    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 2.44/0.68    inference(superposition,[],[f61,f38])).
% 2.44/0.68  fof(f760,plain,(
% 2.44/0.68    r1_tarski(k5_xboole_0(sK2,sK1),sK1) | ~r2_hidden(sK0,sK1)),
% 2.44/0.68    inference(superposition,[],[f695,f612])).
% 2.44/0.68  fof(f612,plain,(
% 2.44/0.68    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | ~r2_hidden(sK0,sK1)),
% 2.44/0.68    inference(resolution,[],[f93,f578])).
% 2.44/0.68  fof(f578,plain,(
% 2.44/0.68    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.44/0.68    inference(resolution,[],[f571,f50])).
% 2.44/0.68  fof(f571,plain,(
% 2.44/0.68    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.44/0.68    inference(superposition,[],[f86,f80])).
% 2.44/0.68  fof(f80,plain,(
% 2.44/0.68    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.44/0.68    inference(definition_unfolding,[],[f36,f79,f76])).
% 2.44/0.68  fof(f79,plain,(
% 2.44/0.68    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.44/0.68    inference(definition_unfolding,[],[f39,f75])).
% 2.44/0.68  fof(f39,plain,(
% 2.44/0.68    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f15])).
% 2.44/0.68  fof(f15,axiom,(
% 2.44/0.68    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.44/0.68  fof(f36,plain,(
% 2.44/0.68    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.44/0.68    inference(cnf_transformation,[],[f28])).
% 2.44/0.68  fof(f28,plain,(
% 2.44/0.68    ? [X0,X1,X2] : ((k1_xboole_0 != X2 | k1_tarski(X0) != X1) & (k1_tarski(X0) != X2 | k1_xboole_0 != X1) & (k1_tarski(X0) != X2 | k1_tarski(X0) != X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.44/0.68    inference(ennf_transformation,[],[f25])).
% 2.44/0.68  fof(f25,negated_conjecture,(
% 2.44/0.68    ~! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.44/0.68    inference(negated_conjecture,[],[f24])).
% 2.44/0.68  fof(f24,conjecture,(
% 2.44/0.68    ! [X0,X1,X2] : ~(~(k1_xboole_0 = X2 & k1_tarski(X0) = X1) & ~(k1_tarski(X0) = X2 & k1_xboole_0 = X1) & ~(k1_tarski(X0) = X2 & k1_tarski(X0) = X1) & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).
% 2.44/0.68  fof(f86,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.44/0.68    inference(definition_unfolding,[],[f42,f76])).
% 2.44/0.68  fof(f42,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.44/0.68    inference(cnf_transformation,[],[f10])).
% 2.44/0.68  fof(f10,axiom,(
% 2.44/0.68    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.44/0.68  fof(f93,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.44/0.68    inference(definition_unfolding,[],[f58,f79])).
% 2.44/0.68  fof(f58,plain,(
% 2.44/0.68    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f22])).
% 2.44/0.68  fof(f22,axiom,(
% 2.44/0.68    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.44/0.68  fof(f695,plain,(
% 2.44/0.68    r1_tarski(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),sK1)),
% 2.44/0.68    inference(superposition,[],[f131,f80])).
% 2.44/0.68  fof(f131,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 2.44/0.68    inference(backward_demodulation,[],[f101,f130])).
% 2.44/0.68  fof(f101,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X0)) )),
% 2.44/0.68    inference(backward_demodulation,[],[f87,f61])).
% 2.44/0.68  fof(f87,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 2.44/0.68    inference(definition_unfolding,[],[f43,f78])).
% 2.44/0.68  fof(f78,plain,(
% 2.44/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.44/0.68    inference(definition_unfolding,[],[f46,f77])).
% 2.44/0.68  fof(f46,plain,(
% 2.44/0.68    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.44/0.68    inference(cnf_transformation,[],[f6])).
% 2.44/0.68  fof(f6,axiom,(
% 2.44/0.68    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.44/0.68  fof(f43,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f9])).
% 2.44/0.68  fof(f9,axiom,(
% 2.44/0.68    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.44/0.68  fof(f241,plain,(
% 2.44/0.68    ( ! [X12,X10,X11,X9] : (~r1_tarski(k5_xboole_0(X10,X11),X12) | ~r2_hidden(X9,X11) | r2_hidden(X9,X12) | r2_hidden(X9,X10)) )),
% 2.44/0.68    inference(resolution,[],[f65,f51])).
% 2.44/0.68  fof(f51,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f29])).
% 2.44/0.68  fof(f65,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f32])).
% 2.44/0.68  fof(f32,plain,(
% 2.44/0.68    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.44/0.68    inference(ennf_transformation,[],[f4])).
% 2.44/0.68  fof(f4,axiom,(
% 2.44/0.68    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.44/0.68  fof(f1214,plain,(
% 2.44/0.68    r1_tarski(sK1,sK2) | k1_xboole_0 = sK2),
% 2.44/0.68    inference(factoring,[],[f1206])).
% 2.44/0.68  fof(f1206,plain,(
% 2.44/0.68    ( ! [X9] : (r1_tarski(sK1,sK2) | r1_tarski(sK1,X9) | k1_xboole_0 = sK2) )),
% 2.44/0.68    inference(resolution,[],[f1183,f108])).
% 2.44/0.68  fof(f1183,plain,(
% 2.44/0.68    ( ! [X6,X7] : (r1_tarski(sK2,X6) | r1_tarski(sK1,X7) | r1_tarski(sK1,sK2)) )),
% 2.44/0.68    inference(resolution,[],[f1178,f821])).
% 2.44/0.68  fof(f821,plain,(
% 2.44/0.68    ( ! [X2] : (~r2_hidden(sK0,X2) | r1_tarski(sK1,X2)) )),
% 2.44/0.68    inference(duplicate_literal_removal,[],[f818])).
% 2.44/0.68  fof(f818,plain,(
% 2.44/0.68    ( ! [X2] : (~r2_hidden(sK0,X2) | r1_tarski(sK1,X2) | r1_tarski(sK1,X2)) )),
% 2.44/0.68    inference(superposition,[],[f53,f813])).
% 2.44/0.68  fof(f813,plain,(
% 2.44/0.68    ( ! [X0] : (sK0 = sK3(sK1,X0) | r1_tarski(sK1,X0)) )),
% 2.44/0.68    inference(resolution,[],[f807,f52])).
% 2.44/0.68  fof(f807,plain,(
% 2.44/0.68    ( ! [X0] : (~r2_hidden(X0,sK1) | sK0 = X0) )),
% 2.44/0.68    inference(resolution,[],[f611,f96])).
% 2.44/0.68  fof(f96,plain,(
% 2.44/0.68    ( ! [X2,X0] : (~r2_hidden(X2,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) | X0 = X2) )),
% 2.44/0.68    inference(equality_resolution,[],[f90])).
% 2.44/0.68  fof(f90,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != X1) )),
% 2.44/0.68    inference(definition_unfolding,[],[f55,f79])).
% 2.44/0.68  fof(f55,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 2.44/0.68    inference(cnf_transformation,[],[f14])).
% 2.44/0.68  fof(f14,axiom,(
% 2.44/0.68    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 2.44/0.68  fof(f611,plain,(
% 2.44/0.68    ( ! [X3] : (r2_hidden(X3,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r2_hidden(X3,sK1)) )),
% 2.44/0.68    inference(resolution,[],[f93,f595])).
% 2.44/0.68  fof(f595,plain,(
% 2.44/0.68    ( ! [X5] : (~r1_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5),sK1) | r2_hidden(X5,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) )),
% 2.44/0.68    inference(resolution,[],[f92,f577])).
% 2.44/0.68  fof(f577,plain,(
% 2.44/0.68    ( ! [X0] : (r1_tarski(X0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r1_tarski(X0,sK1)) )),
% 2.44/0.68    inference(resolution,[],[f571,f62])).
% 2.44/0.68  fof(f62,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f31])).
% 2.44/0.68  fof(f31,plain,(
% 2.44/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 2.44/0.68    inference(flattening,[],[f30])).
% 2.44/0.68  fof(f30,plain,(
% 2.44/0.68    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 2.44/0.68    inference(ennf_transformation,[],[f7])).
% 2.44/0.68  fof(f7,axiom,(
% 2.44/0.68    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 2.44/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 2.44/0.68  fof(f92,plain,(
% 2.44/0.68    ( ! [X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | r2_hidden(X0,X1)) )),
% 2.44/0.68    inference(definition_unfolding,[],[f59,f79])).
% 2.44/0.68  fof(f59,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) )),
% 2.44/0.68    inference(cnf_transformation,[],[f22])).
% 2.44/0.68  fof(f1178,plain,(
% 2.44/0.68    ( ! [X0,X1] : (r2_hidden(sK0,sK2) | r1_tarski(sK2,X1) | r1_tarski(sK1,X0)) )),
% 2.44/0.68    inference(resolution,[],[f1165,f1007])).
% 2.44/0.68  fof(f1007,plain,(
% 2.44/0.68    ( ! [X6,X5] : (~r1_tarski(X5,sK1) | r1_tarski(X5,X6) | r2_hidden(sK0,X5)) )),
% 2.44/0.68    inference(duplicate_literal_removal,[],[f1006])).
% 2.44/0.68  fof(f1006,plain,(
% 2.44/0.68    ( ! [X6,X5] : (r2_hidden(sK0,X5) | r1_tarski(X5,X6) | ~r1_tarski(X5,sK1) | r1_tarski(X5,X6)) )),
% 2.44/0.68    inference(superposition,[],[f52,f814])).
% 2.44/0.68  fof(f814,plain,(
% 2.44/0.68    ( ! [X2,X1] : (sK0 = sK3(X1,X2) | ~r1_tarski(X1,sK1) | r1_tarski(X1,X2)) )),
% 2.44/0.68    inference(resolution,[],[f807,f110])).
% 2.44/0.68  fof(f110,plain,(
% 2.44/0.68    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1),X2) | ~r1_tarski(X0,X2) | r1_tarski(X0,X1)) )),
% 2.44/0.68    inference(resolution,[],[f51,f52])).
% 2.44/0.68  fof(f632,plain,(
% 2.44/0.68    k1_xboole_0 != sK2 | ~r2_hidden(sK0,sK1)),
% 2.44/0.68    inference(trivial_inequality_removal,[],[f619])).
% 2.44/0.68  fof(f619,plain,(
% 2.44/0.68    sK1 != sK1 | k1_xboole_0 != sK2 | ~r2_hidden(sK0,sK1)),
% 2.44/0.68    inference(superposition,[],[f83,f612])).
% 2.44/0.68  fof(f83,plain,(
% 2.44/0.68    sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK2),
% 2.44/0.68    inference(definition_unfolding,[],[f33,f79])).
% 2.44/0.68  fof(f33,plain,(
% 2.44/0.68    sK1 != k1_tarski(sK0) | k1_xboole_0 != sK2),
% 2.44/0.68    inference(cnf_transformation,[],[f28])).
% 2.44/0.68  fof(f820,plain,(
% 2.44/0.68    ( ! [X3] : (r2_hidden(sK0,sK1) | r1_tarski(sK1,X3)) )),
% 2.44/0.68    inference(duplicate_literal_removal,[],[f819])).
% 2.44/0.68  fof(f819,plain,(
% 2.44/0.68    ( ! [X3] : (r2_hidden(sK0,sK1) | r1_tarski(sK1,X3) | r1_tarski(sK1,X3)) )),
% 2.44/0.68    inference(superposition,[],[f52,f813])).
% 2.44/0.68  fof(f633,plain,(
% 2.44/0.68    sK1 != sK2 | ~r2_hidden(sK0,sK1)),
% 2.44/0.68    inference(trivial_inequality_removal,[],[f617])).
% 2.44/0.68  fof(f617,plain,(
% 2.44/0.68    sK1 != sK2 | sK1 != sK1 | ~r2_hidden(sK0,sK1)),
% 2.44/0.68    inference(superposition,[],[f81,f612])).
% 2.44/0.68  fof(f81,plain,(
% 2.44/0.68    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | sK1 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.44/0.68    inference(definition_unfolding,[],[f35,f79,f79])).
% 2.44/0.68  fof(f35,plain,(
% 2.44/0.68    sK1 != k1_tarski(sK0) | sK2 != k1_tarski(sK0)),
% 2.44/0.68    inference(cnf_transformation,[],[f28])).
% 2.44/0.68  fof(f1275,plain,(
% 2.44/0.68    sK1 = k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.44/0.68    inference(unit_resulting_resolution,[],[f695,f1267,f50])).
% 2.44/0.68  fof(f1519,plain,(
% 2.44/0.68    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.44/0.68    inference(global_subsumption,[],[f82,f1311])).
% 2.44/0.68  fof(f82,plain,(
% 2.44/0.68    sK2 != k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) | k1_xboole_0 != sK1),
% 2.44/0.68    inference(definition_unfolding,[],[f34,f79])).
% 2.44/0.68  fof(f34,plain,(
% 2.44/0.68    k1_xboole_0 != sK1 | sK2 != k1_tarski(sK0)),
% 2.44/0.68    inference(cnf_transformation,[],[f28])).
% 2.44/0.68  % SZS output end Proof for theBenchmark
% 2.44/0.68  % (3271)------------------------------
% 2.44/0.68  % (3271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.44/0.68  % (3271)Termination reason: Refutation
% 2.44/0.68  
% 2.44/0.68  % (3271)Memory used [KB]: 8571
% 2.44/0.68  % (3271)Time elapsed: 0.233 s
% 2.44/0.68  % (3271)------------------------------
% 2.44/0.68  % (3271)------------------------------
% 2.44/0.69  % (3246)Success in time 0.323 s
%------------------------------------------------------------------------------
