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
% DateTime   : Thu Dec  3 12:33:32 EST 2020

% Result     : Theorem 6.19s
% Output     : Refutation 6.19s
% Verified   : 
% Statistics : Number of formulae       :  106 (2400 expanded)
%              Number of leaves         :   16 ( 815 expanded)
%              Depth                    :   22
%              Number of atoms          :  152 (2582 expanded)
%              Number of equality atoms :   94 (2372 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9086,plain,(
    $false ),
    inference(resolution,[],[f9067,f63])).

fof(f63,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f9067,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f9066,f1311])).

fof(f1311,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f1254,f839])).

fof(f839,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f159,f833])).

fof(f833,plain,(
    ! [X5] : k1_xboole_0 = k4_xboole_0(X5,X5) ),
    inference(forward_demodulation,[],[f794,f667])).

fof(f667,plain,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f420,f198])).

fof(f198,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f26,f30,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f30])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f420,plain,(
    ! [X9] : k5_xboole_0(X9,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9))) = X9 ),
    inference(forward_demodulation,[],[f400,f54])).

fof(f54,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0 ),
    inference(definition_unfolding,[],[f23,f29])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f23,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f400,plain,(
    ! [X9] : k5_xboole_0(X9,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9))) = k5_xboole_0(X9,k4_xboole_0(k1_xboole_0,X9)) ),
    inference(superposition,[],[f131,f54])).

fof(f131,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1)) ),
    inference(superposition,[],[f43,f54])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f794,plain,(
    ! [X5] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X5,X5) ),
    inference(backward_demodulation,[],[f737,f760])).

fof(f760,plain,(
    ! [X12] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X12) ),
    inference(backward_demodulation,[],[f744,f759])).

fof(f759,plain,(
    ! [X14] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,X14)) ),
    inference(forward_demodulation,[],[f746,f667])).

fof(f746,plain,(
    ! [X14] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X14,X14),k1_xboole_0)) ),
    inference(superposition,[],[f256,f667])).

fof(f256,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = X0 ),
    inference(superposition,[],[f57,f56])).

fof(f57,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f29,f30])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f744,plain,(
    ! [X12] : k4_xboole_0(k1_xboole_0,X12) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X12,X12)) ),
    inference(superposition,[],[f198,f667])).

fof(f737,plain,(
    ! [X5] : k4_xboole_0(X5,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5)) ),
    inference(superposition,[],[f56,f667])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(backward_demodulation,[],[f154,f155])).

fof(f155,plain,(
    ! [X2] : k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2) ),
    inference(superposition,[],[f52,f125])).

fof(f125,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(unit_resulting_resolution,[],[f63,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f154,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f52,f58])).

fof(f1254,plain,(
    ! [X0,X1] : r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f90,f1250])).

fof(f1250,plain,(
    ! [X4,X3] :
      ( r1_tarski(k2_tarski(X3,X3),X4)
      | ~ r2_hidden(X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f1247])).

fof(f1247,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | r1_tarski(k2_tarski(X3,X3),X4)
      | r1_tarski(k2_tarski(X3,X3),X4) ) ),
    inference(superposition,[],[f37,f78])).

fof(f78,plain,(
    ! [X2,X1] :
      ( sK2(k2_tarski(X1,X1),X2) = X1
      | r1_tarski(k2_tarski(X1,X1),X2) ) ),
    inference(resolution,[],[f65,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_tarski(X0,X0))
      | X0 = X2 ) ),
    inference(equality_resolution,[],[f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f39,f24])).

fof(f24,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( X0 = X2
      | ~ r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK2(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f90,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(unit_resulting_resolution,[],[f71,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_tarski(X0,X1))
      | ~ sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f71,plain,(
    ! [X3,X1] : sP5(X3,X1,X3) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( X0 != X3
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f9066,plain,(
    ~ r1_tarski(k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),k1_xboole_0) ),
    inference(forward_demodulation,[],[f9065,f198])).

fof(f9065,plain,(
    ~ r1_tarski(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),k1_xboole_0) ),
    inference(backward_demodulation,[],[f5334,f9030])).

fof(f9030,plain,(
    ! [X12,X13] : k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k5_xboole_0(k4_xboole_0(X12,X13),X12) ),
    inference(superposition,[],[f1140,f1917])).

fof(f1917,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(forward_demodulation,[],[f1879,f761])).

fof(f761,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f54,f760])).

fof(f1879,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k1_xboole_0) ),
    inference(superposition,[],[f157,f838])).

fof(f838,plain,(
    ! [X2] : k1_xboole_0 = k5_xboole_0(X2,X2) ),
    inference(backward_demodulation,[],[f155,f833])).

fof(f157,plain,(
    ! [X2,X0,X1] : k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(superposition,[],[f43,f52])).

fof(f1140,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f840,f1111])).

fof(f1111,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(unit_resulting_resolution,[],[f63,f854])).

fof(f854,plain,(
    ! [X14,X13] :
      ( k5_xboole_0(k1_xboole_0,X14) = X14
      | ~ r1_tarski(X14,X13) ) ),
    inference(backward_demodulation,[],[f454,f840])).

fof(f454,plain,(
    ! [X14,X13] :
      ( k5_xboole_0(X13,k5_xboole_0(X13,X14)) = X14
      | ~ r1_tarski(X14,X13) ) ),
    inference(superposition,[],[f164,f285])).

fof(f285,plain,(
    ! [X14,X13] :
      ( k5_xboole_0(X13,k4_xboole_0(X13,X14)) = X14
      | ~ r1_tarski(X14,X13) ) ),
    inference(superposition,[],[f52,f210])).

fof(f210,plain,(
    ! [X8,X7] :
      ( k4_xboole_0(X8,k4_xboole_0(X8,X7)) = X7
      | ~ r1_tarski(X7,X8) ) ),
    inference(forward_demodulation,[],[f192,f125])).

fof(f192,plain,(
    ! [X8,X7] :
      ( k4_xboole_0(X7,k4_xboole_0(X7,X7)) = k4_xboole_0(X8,k4_xboole_0(X8,X7))
      | ~ r1_tarski(X7,X8) ) ),
    inference(superposition,[],[f56,f159])).

fof(f164,plain,(
    ! [X2,X3] : k5_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X3))) ),
    inference(backward_demodulation,[],[f132,f161])).

fof(f161,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f43,f155])).

fof(f132,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X2),X3)) = k5_xboole_0(X2,X3) ),
    inference(superposition,[],[f43,f55])).

fof(f55,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f25,f29])).

fof(f25,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f840,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(backward_demodulation,[],[f161,f833])).

fof(f5334,plain,(
    ~ r1_tarski(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1))),k1_xboole_0) ),
    inference(forward_demodulation,[],[f5318,f43])).

fof(f5318,plain,(
    ~ r1_tarski(k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f53,f1214])).

fof(f1214,plain,(
    ! [X4,X3] :
      ( ~ r1_tarski(k5_xboole_0(X3,X4),k1_xboole_0)
      | X3 = X4 ) ),
    inference(superposition,[],[f1140,f804])).

fof(f804,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,X2) = X1
      | ~ r1_tarski(X2,k1_xboole_0) ) ),
    inference(forward_demodulation,[],[f803,f760])).

fof(f803,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,X2) = X1
      | ~ r1_tarski(X2,k4_xboole_0(k1_xboole_0,X1)) ) ),
    inference(forward_demodulation,[],[f802,f761])).

fof(f802,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,X2) = k5_xboole_0(X1,k1_xboole_0)
      | ~ r1_tarski(X2,k4_xboole_0(k1_xboole_0,X1)) ) ),
    inference(forward_demodulation,[],[f772,f760])).

fof(f772,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2))
      | ~ r1_tarski(X2,k4_xboole_0(k1_xboole_0,X1)) ) ),
    inference(backward_demodulation,[],[f395,f760])).

fof(f395,plain,(
    ! [X2,X1] :
      ( k5_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2))
      | ~ r1_tarski(X2,k4_xboole_0(k1_xboole_0,X1)) ) ),
    inference(superposition,[],[f131,f281])).

fof(f281,plain,(
    ! [X6,X7] :
      ( k5_xboole_0(X6,X7) = k4_xboole_0(X6,X7)
      | ~ r1_tarski(X7,X6) ) ),
    inference(superposition,[],[f52,f210])).

fof(f53,plain,(
    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))) ),
    inference(definition_unfolding,[],[f22,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0))) ),
    inference(definition_unfolding,[],[f42,f29,f24])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f22,plain,(
    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:40:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.51  % (16863)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.52  % (16850)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.52  % (16854)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.52  % (16863)Refutation not found, incomplete strategy% (16863)------------------------------
% 0.20/0.52  % (16863)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (16853)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.52  % (16863)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (16863)Memory used [KB]: 10746
% 0.20/0.52  % (16863)Time elapsed: 0.067 s
% 0.20/0.52  % (16863)------------------------------
% 0.20/0.52  % (16863)------------------------------
% 0.20/0.53  % (16846)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (16847)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (16845)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.53  % (16843)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (16842)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (16843)Refutation not found, incomplete strategy% (16843)------------------------------
% 0.20/0.53  % (16843)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (16843)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (16843)Memory used [KB]: 10618
% 0.20/0.53  % (16843)Time elapsed: 0.128 s
% 0.20/0.53  % (16843)------------------------------
% 0.20/0.53  % (16843)------------------------------
% 0.20/0.53  % (16870)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (16841)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.54  % (16862)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.54  % (16849)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (16869)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.54  % (16849)Refutation not found, incomplete strategy% (16849)------------------------------
% 0.20/0.54  % (16849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16849)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16849)Memory used [KB]: 10618
% 0.20/0.54  % (16849)Time elapsed: 0.123 s
% 0.20/0.54  % (16849)------------------------------
% 0.20/0.54  % (16849)------------------------------
% 0.20/0.54  % (16862)Refutation not found, incomplete strategy% (16862)------------------------------
% 0.20/0.54  % (16862)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16848)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (16862)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16862)Memory used [KB]: 1663
% 0.20/0.54  % (16862)Time elapsed: 0.128 s
% 0.20/0.54  % (16862)------------------------------
% 0.20/0.54  % (16862)------------------------------
% 0.20/0.54  % (16861)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.54  % (16844)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (16861)Refutation not found, incomplete strategy% (16861)------------------------------
% 0.20/0.54  % (16861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (16861)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (16861)Memory used [KB]: 10746
% 0.20/0.54  % (16861)Time elapsed: 0.138 s
% 0.20/0.54  % (16861)------------------------------
% 0.20/0.54  % (16861)------------------------------
% 1.47/0.55  % (16867)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.47/0.55  % (16852)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.47/0.55  % (16852)Refutation not found, incomplete strategy% (16852)------------------------------
% 1.47/0.55  % (16852)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.55  % (16852)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.55  
% 1.47/0.55  % (16852)Memory used [KB]: 10618
% 1.47/0.55  % (16852)Time elapsed: 0.149 s
% 1.47/0.55  % (16852)------------------------------
% 1.47/0.55  % (16852)------------------------------
% 1.47/0.55  % (16866)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.47/0.55  % (16860)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.47/0.55  % (16859)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.47/0.55  % (16857)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.47/0.56  % (16851)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.47/0.56  % (16851)Refutation not found, incomplete strategy% (16851)------------------------------
% 1.47/0.56  % (16851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (16851)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (16851)Memory used [KB]: 10618
% 1.47/0.56  % (16851)Time elapsed: 0.149 s
% 1.47/0.56  % (16851)------------------------------
% 1.47/0.56  % (16851)------------------------------
% 1.47/0.56  % (16856)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.47/0.56  % (16855)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.47/0.56  % (16864)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.47/0.56  % (16864)Refutation not found, incomplete strategy% (16864)------------------------------
% 1.47/0.56  % (16864)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.56  % (16864)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.56  
% 1.47/0.56  % (16864)Memory used [KB]: 1663
% 1.47/0.56  % (16864)Time elapsed: 0.157 s
% 1.47/0.56  % (16864)------------------------------
% 1.47/0.56  % (16864)------------------------------
% 1.63/0.57  % (16868)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.63/0.57  % (16858)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.63/0.57  % (16858)Refutation not found, incomplete strategy% (16858)------------------------------
% 1.63/0.57  % (16858)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.57  % (16858)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.57  
% 1.63/0.57  % (16858)Memory used [KB]: 10618
% 1.63/0.57  % (16858)Time elapsed: 0.159 s
% 1.63/0.57  % (16858)------------------------------
% 1.63/0.57  % (16858)------------------------------
% 1.63/0.57  % (16865)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 2.25/0.67  % (16871)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.25/0.68  % (16875)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.25/0.69  % (16876)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.25/0.69  % (16873)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.25/0.70  % (16872)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.66/0.73  % (16874)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.66/0.73  % (16878)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.66/0.73  % (16877)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.66/0.75  % (16879)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 3.53/0.89  % (16846)Time limit reached!
% 3.53/0.89  % (16846)------------------------------
% 3.53/0.89  % (16846)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.89  % (16846)Termination reason: Time limit
% 3.53/0.89  
% 3.53/0.89  % (16846)Memory used [KB]: 9594
% 3.53/0.89  % (16846)Time elapsed: 0.425 s
% 3.53/0.89  % (16846)------------------------------
% 3.53/0.89  % (16846)------------------------------
% 3.53/0.91  % (16841)Time limit reached!
% 3.53/0.91  % (16841)------------------------------
% 3.53/0.91  % (16841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.91  % (16841)Termination reason: Time limit
% 3.53/0.91  
% 3.53/0.91  % (16841)Memory used [KB]: 2686
% 3.53/0.91  % (16841)Time elapsed: 0.505 s
% 3.53/0.91  % (16841)------------------------------
% 3.53/0.91  % (16841)------------------------------
% 3.89/0.93  % (16842)Time limit reached!
% 3.89/0.93  % (16842)------------------------------
% 3.89/0.93  % (16842)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.93  % (16842)Termination reason: Time limit
% 3.89/0.93  
% 3.89/0.93  % (16842)Memory used [KB]: 9338
% 3.89/0.93  % (16842)Time elapsed: 0.528 s
% 3.89/0.93  % (16842)------------------------------
% 3.89/0.93  % (16842)------------------------------
% 3.89/0.94  % (16853)Time limit reached!
% 3.89/0.94  % (16853)------------------------------
% 3.89/0.94  % (16853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.89/0.94  % (16853)Termination reason: Time limit
% 3.89/0.94  % (16853)Termination phase: Saturation
% 3.89/0.94  
% 3.89/0.94  % (16853)Memory used [KB]: 11641
% 3.89/0.94  % (16853)Time elapsed: 0.500 s
% 3.89/0.94  % (16853)------------------------------
% 3.89/0.94  % (16853)------------------------------
% 4.09/1.01  % (16875)Time limit reached!
% 4.09/1.01  % (16875)------------------------------
% 4.09/1.01  % (16875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/1.01  % (16875)Termination reason: Time limit
% 4.09/1.01  % (16875)Termination phase: Saturation
% 4.09/1.01  
% 4.09/1.01  % (16875)Memory used [KB]: 13688
% 4.09/1.01  % (16875)Time elapsed: 0.400 s
% 4.09/1.01  % (16875)------------------------------
% 4.09/1.01  % (16875)------------------------------
% 4.09/1.01  % (16874)Time limit reached!
% 4.09/1.01  % (16874)------------------------------
% 4.09/1.01  % (16874)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/1.01  % (16874)Termination reason: Time limit
% 4.09/1.01  
% 4.09/1.01  % (16874)Memory used [KB]: 7419
% 4.09/1.01  % (16874)Time elapsed: 0.425 s
% 4.09/1.01  % (16874)------------------------------
% 4.09/1.01  % (16874)------------------------------
% 4.09/1.02  % (16869)Time limit reached!
% 4.09/1.02  % (16869)------------------------------
% 4.09/1.02  % (16869)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/1.02  % (16869)Termination reason: Time limit
% 4.09/1.02  % (16869)Termination phase: Saturation
% 4.09/1.02  
% 4.09/1.02  % (16869)Memory used [KB]: 9083
% 4.09/1.02  % (16869)Time elapsed: 0.600 s
% 4.09/1.02  % (16869)------------------------------
% 4.09/1.02  % (16869)------------------------------
% 4.09/1.03  % (16848)Time limit reached!
% 4.09/1.03  % (16848)------------------------------
% 4.09/1.03  % (16848)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.09/1.03  % (16848)Termination reason: Time limit
% 4.09/1.03  
% 4.09/1.03  % (16848)Memory used [KB]: 12409
% 4.09/1.03  % (16848)Time elapsed: 0.612 s
% 4.09/1.03  % (16848)------------------------------
% 4.09/1.03  % (16848)------------------------------
% 4.70/1.03  % (16857)Time limit reached!
% 4.70/1.03  % (16857)------------------------------
% 4.70/1.03  % (16857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.70/1.03  % (16857)Termination reason: Time limit
% 4.70/1.03  
% 4.70/1.03  % (16857)Memory used [KB]: 16886
% 4.70/1.03  % (16857)Time elapsed: 0.618 s
% 4.70/1.03  % (16857)------------------------------
% 4.70/1.03  % (16857)------------------------------
% 4.70/1.04  % (16881)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 4.70/1.05  % (16882)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 4.70/1.06  % (16880)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 5.63/1.12  % (16883)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 5.63/1.14  % (16884)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 5.63/1.14  % (16888)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 5.63/1.14  % (16885)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 5.63/1.14  % (16884)Refutation not found, incomplete strategy% (16884)------------------------------
% 5.63/1.14  % (16884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.63/1.14  % (16884)Termination reason: Refutation not found, incomplete strategy
% 5.63/1.14  
% 5.63/1.14  % (16884)Memory used [KB]: 1663
% 5.63/1.14  % (16884)Time elapsed: 0.105 s
% 5.63/1.14  % (16884)------------------------------
% 5.63/1.14  % (16884)------------------------------
% 6.19/1.16  % (16887)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 6.19/1.17  % (16865)Refutation found. Thanks to Tanya!
% 6.19/1.17  % SZS status Theorem for theBenchmark
% 6.19/1.17  % SZS output start Proof for theBenchmark
% 6.19/1.17  fof(f9086,plain,(
% 6.19/1.17    $false),
% 6.19/1.17    inference(resolution,[],[f9067,f63])).
% 6.19/1.17  fof(f63,plain,(
% 6.19/1.17    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 6.19/1.17    inference(equality_resolution,[],[f33])).
% 6.19/1.17  fof(f33,plain,(
% 6.19/1.17    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 6.19/1.17    inference(cnf_transformation,[],[f4])).
% 6.19/1.17  fof(f4,axiom,(
% 6.19/1.17    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 6.19/1.17  fof(f9067,plain,(
% 6.19/1.17    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 6.19/1.17    inference(forward_demodulation,[],[f9066,f1311])).
% 6.19/1.17  fof(f1311,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 6.19/1.17    inference(unit_resulting_resolution,[],[f1254,f839])).
% 6.19/1.17  fof(f839,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 6.19/1.17    inference(backward_demodulation,[],[f159,f833])).
% 6.19/1.17  fof(f833,plain,(
% 6.19/1.17    ( ! [X5] : (k1_xboole_0 = k4_xboole_0(X5,X5)) )),
% 6.19/1.17    inference(forward_demodulation,[],[f794,f667])).
% 6.19/1.17  fof(f667,plain,(
% 6.19/1.17    ( ! [X1] : (k4_xboole_0(X1,k1_xboole_0) = X1) )),
% 6.19/1.17    inference(superposition,[],[f420,f198])).
% 6.19/1.17  fof(f198,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 6.19/1.17    inference(superposition,[],[f52,f56])).
% 6.19/1.17  fof(f56,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 6.19/1.17    inference(definition_unfolding,[],[f26,f30,f30])).
% 6.19/1.17  fof(f30,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 6.19/1.17    inference(cnf_transformation,[],[f9])).
% 6.19/1.17  fof(f9,axiom,(
% 6.19/1.17    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 6.19/1.17  fof(f26,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 6.19/1.17    inference(cnf_transformation,[],[f1])).
% 6.19/1.17  fof(f1,axiom,(
% 6.19/1.17    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 6.19/1.17  fof(f52,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 6.19/1.17    inference(definition_unfolding,[],[f28,f30])).
% 6.19/1.17  fof(f28,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 6.19/1.17    inference(cnf_transformation,[],[f5])).
% 6.19/1.17  fof(f5,axiom,(
% 6.19/1.17    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 6.19/1.17  fof(f420,plain,(
% 6.19/1.17    ( ! [X9] : (k5_xboole_0(X9,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9))) = X9) )),
% 6.19/1.17    inference(forward_demodulation,[],[f400,f54])).
% 6.19/1.17  fof(f54,plain,(
% 6.19/1.17    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(k1_xboole_0,X0)) = X0) )),
% 6.19/1.17    inference(definition_unfolding,[],[f23,f29])).
% 6.19/1.17  fof(f29,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 6.19/1.17    inference(cnf_transformation,[],[f11])).
% 6.19/1.17  fof(f11,axiom,(
% 6.19/1.17    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 6.19/1.17  fof(f23,plain,(
% 6.19/1.17    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.19/1.17    inference(cnf_transformation,[],[f6])).
% 6.19/1.17  fof(f6,axiom,(
% 6.19/1.17    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 6.19/1.17  fof(f400,plain,(
% 6.19/1.17    ( ! [X9] : (k5_xboole_0(X9,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X9))) = k5_xboole_0(X9,k4_xboole_0(k1_xboole_0,X9))) )),
% 6.19/1.17    inference(superposition,[],[f131,f54])).
% 6.19/1.17  fof(f131,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(k1_xboole_0,X0),X1))) )),
% 6.19/1.17    inference(superposition,[],[f43,f54])).
% 6.19/1.17  fof(f43,plain,(
% 6.19/1.17    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 6.19/1.17    inference(cnf_transformation,[],[f10])).
% 6.19/1.17  fof(f10,axiom,(
% 6.19/1.17    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 6.19/1.17  fof(f794,plain,(
% 6.19/1.17    ( ! [X5] : (k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(X5,X5)) )),
% 6.19/1.17    inference(backward_demodulation,[],[f737,f760])).
% 6.19/1.17  fof(f760,plain,(
% 6.19/1.17    ( ! [X12] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X12)) )),
% 6.19/1.17    inference(backward_demodulation,[],[f744,f759])).
% 6.19/1.17  fof(f759,plain,(
% 6.19/1.17    ( ! [X14] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(X14,X14))) )),
% 6.19/1.17    inference(forward_demodulation,[],[f746,f667])).
% 6.19/1.17  fof(f746,plain,(
% 6.19/1.17    ( ! [X14] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k4_xboole_0(X14,X14),k1_xboole_0))) )),
% 6.19/1.17    inference(superposition,[],[f256,f667])).
% 6.19/1.17  fof(f256,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X0)) = X0) )),
% 6.19/1.17    inference(superposition,[],[f57,f56])).
% 6.19/1.17  fof(f57,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 6.19/1.17    inference(definition_unfolding,[],[f27,f29,f30])).
% 6.19/1.17  fof(f27,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 6.19/1.17    inference(cnf_transformation,[],[f7])).
% 6.19/1.17  fof(f7,axiom,(
% 6.19/1.17    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 6.19/1.17  fof(f744,plain,(
% 6.19/1.17    ( ! [X12] : (k4_xboole_0(k1_xboole_0,X12) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X12,X12))) )),
% 6.19/1.17    inference(superposition,[],[f198,f667])).
% 6.19/1.17  fof(f737,plain,(
% 6.19/1.17    ( ! [X5] : (k4_xboole_0(X5,X5) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X5))) )),
% 6.19/1.17    inference(superposition,[],[f56,f667])).
% 6.19/1.17  fof(f159,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 6.19/1.17    inference(backward_demodulation,[],[f154,f155])).
% 6.19/1.17  fof(f155,plain,(
% 6.19/1.17    ( ! [X2] : (k4_xboole_0(X2,X2) = k5_xboole_0(X2,X2)) )),
% 6.19/1.17    inference(superposition,[],[f52,f125])).
% 6.19/1.17  fof(f125,plain,(
% 6.19/1.17    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 6.19/1.17    inference(unit_resulting_resolution,[],[f63,f58])).
% 6.19/1.17  fof(f58,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 6.19/1.17    inference(definition_unfolding,[],[f31,f30])).
% 6.19/1.17  fof(f31,plain,(
% 6.19/1.17    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 6.19/1.17    inference(cnf_transformation,[],[f20])).
% 6.19/1.17  fof(f20,plain,(
% 6.19/1.17    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 6.19/1.17    inference(ennf_transformation,[],[f8])).
% 6.19/1.17  fof(f8,axiom,(
% 6.19/1.17    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 6.19/1.17  fof(f154,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,X0) | ~r1_tarski(X0,X1)) )),
% 6.19/1.17    inference(superposition,[],[f52,f58])).
% 6.19/1.17  fof(f1254,plain,(
% 6.19/1.17    ( ! [X0,X1] : (r1_tarski(k2_tarski(X0,X0),k2_tarski(X0,X1))) )),
% 6.19/1.17    inference(unit_resulting_resolution,[],[f90,f1250])).
% 6.19/1.17  fof(f1250,plain,(
% 6.19/1.17    ( ! [X4,X3] : (r1_tarski(k2_tarski(X3,X3),X4) | ~r2_hidden(X3,X4)) )),
% 6.19/1.17    inference(duplicate_literal_removal,[],[f1247])).
% 6.19/1.17  fof(f1247,plain,(
% 6.19/1.17    ( ! [X4,X3] : (~r2_hidden(X3,X4) | r1_tarski(k2_tarski(X3,X3),X4) | r1_tarski(k2_tarski(X3,X3),X4)) )),
% 6.19/1.17    inference(superposition,[],[f37,f78])).
% 6.19/1.17  fof(f78,plain,(
% 6.19/1.17    ( ! [X2,X1] : (sK2(k2_tarski(X1,X1),X2) = X1 | r1_tarski(k2_tarski(X1,X1),X2)) )),
% 6.19/1.17    inference(resolution,[],[f65,f36])).
% 6.19/1.17  fof(f36,plain,(
% 6.19/1.17    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 6.19/1.17    inference(cnf_transformation,[],[f21])).
% 6.19/1.17  fof(f21,plain,(
% 6.19/1.17    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 6.19/1.17    inference(ennf_transformation,[],[f2])).
% 6.19/1.17  fof(f2,axiom,(
% 6.19/1.17    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 6.19/1.17  fof(f65,plain,(
% 6.19/1.17    ( ! [X2,X0] : (~r2_hidden(X2,k2_tarski(X0,X0)) | X0 = X2) )),
% 6.19/1.17    inference(equality_resolution,[],[f61])).
% 6.19/1.17  fof(f61,plain,(
% 6.19/1.17    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k2_tarski(X0,X0) != X1) )),
% 6.19/1.17    inference(definition_unfolding,[],[f39,f24])).
% 6.19/1.17  fof(f24,plain,(
% 6.19/1.17    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 6.19/1.17    inference(cnf_transformation,[],[f15])).
% 6.19/1.17  fof(f15,axiom,(
% 6.19/1.17    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 6.19/1.17  fof(f39,plain,(
% 6.19/1.17    ( ! [X2,X0,X1] : (X0 = X2 | ~r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 6.19/1.17    inference(cnf_transformation,[],[f12])).
% 6.19/1.17  fof(f12,axiom,(
% 6.19/1.17    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).
% 6.19/1.17  fof(f37,plain,(
% 6.19/1.17    ( ! [X0,X1] : (~r2_hidden(sK2(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 6.19/1.17    inference(cnf_transformation,[],[f21])).
% 6.19/1.17  fof(f90,plain,(
% 6.19/1.17    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 6.19/1.17    inference(unit_resulting_resolution,[],[f71,f69])).
% 6.19/1.17  fof(f69,plain,(
% 6.19/1.17    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_tarski(X0,X1)) | ~sP5(X3,X1,X0)) )),
% 6.19/1.17    inference(equality_resolution,[],[f47])).
% 6.19/1.17  fof(f47,plain,(
% 6.19/1.17    ( ! [X2,X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 6.19/1.17    inference(cnf_transformation,[],[f13])).
% 6.19/1.17  fof(f13,axiom,(
% 6.19/1.17    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 6.19/1.17  fof(f71,plain,(
% 6.19/1.17    ( ! [X3,X1] : (sP5(X3,X1,X3)) )),
% 6.19/1.17    inference(equality_resolution,[],[f44])).
% 6.19/1.17  fof(f44,plain,(
% 6.19/1.17    ( ! [X0,X3,X1] : (X0 != X3 | sP5(X3,X1,X0)) )),
% 6.19/1.17    inference(cnf_transformation,[],[f13])).
% 6.19/1.17  fof(f9066,plain,(
% 6.19/1.17    ~r1_tarski(k4_xboole_0(k2_tarski(sK0,sK0),k2_tarski(sK0,sK1)),k1_xboole_0)),
% 6.19/1.17    inference(forward_demodulation,[],[f9065,f198])).
% 6.19/1.17  fof(f9065,plain,(
% 6.19/1.17    ~r1_tarski(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),k1_xboole_0)),
% 6.19/1.17    inference(backward_demodulation,[],[f5334,f9030])).
% 6.19/1.17  fof(f9030,plain,(
% 6.19/1.17    ( ! [X12,X13] : (k4_xboole_0(X12,k4_xboole_0(X12,X13)) = k5_xboole_0(k4_xboole_0(X12,X13),X12)) )),
% 6.19/1.17    inference(superposition,[],[f1140,f1917])).
% 6.19/1.17  fof(f1917,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 6.19/1.17    inference(forward_demodulation,[],[f1879,f761])).
% 6.19/1.17  fof(f761,plain,(
% 6.19/1.17    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 6.19/1.17    inference(backward_demodulation,[],[f54,f760])).
% 6.19/1.17  fof(f1879,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k5_xboole_0(X0,k1_xboole_0)) )),
% 6.19/1.17    inference(superposition,[],[f157,f838])).
% 6.19/1.17  fof(f838,plain,(
% 6.19/1.17    ( ! [X2] : (k1_xboole_0 = k5_xboole_0(X2,X2)) )),
% 6.19/1.17    inference(backward_demodulation,[],[f155,f833])).
% 6.19/1.17  fof(f157,plain,(
% 6.19/1.17    ( ! [X2,X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) = k5_xboole_0(k4_xboole_0(X0,X1),X2)) )),
% 6.19/1.17    inference(superposition,[],[f43,f52])).
% 6.19/1.17  fof(f1140,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 6.19/1.17    inference(backward_demodulation,[],[f840,f1111])).
% 6.19/1.17  fof(f1111,plain,(
% 6.19/1.17    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 6.19/1.17    inference(unit_resulting_resolution,[],[f63,f854])).
% 6.19/1.17  fof(f854,plain,(
% 6.19/1.17    ( ! [X14,X13] : (k5_xboole_0(k1_xboole_0,X14) = X14 | ~r1_tarski(X14,X13)) )),
% 6.19/1.17    inference(backward_demodulation,[],[f454,f840])).
% 6.19/1.17  fof(f454,plain,(
% 6.19/1.17    ( ! [X14,X13] : (k5_xboole_0(X13,k5_xboole_0(X13,X14)) = X14 | ~r1_tarski(X14,X13)) )),
% 6.19/1.17    inference(superposition,[],[f164,f285])).
% 6.19/1.17  fof(f285,plain,(
% 6.19/1.17    ( ! [X14,X13] : (k5_xboole_0(X13,k4_xboole_0(X13,X14)) = X14 | ~r1_tarski(X14,X13)) )),
% 6.19/1.17    inference(superposition,[],[f52,f210])).
% 6.19/1.17  fof(f210,plain,(
% 6.19/1.17    ( ! [X8,X7] : (k4_xboole_0(X8,k4_xboole_0(X8,X7)) = X7 | ~r1_tarski(X7,X8)) )),
% 6.19/1.17    inference(forward_demodulation,[],[f192,f125])).
% 6.19/1.17  fof(f192,plain,(
% 6.19/1.17    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X7,X7)) = k4_xboole_0(X8,k4_xboole_0(X8,X7)) | ~r1_tarski(X7,X8)) )),
% 6.19/1.17    inference(superposition,[],[f56,f159])).
% 6.19/1.17  fof(f164,plain,(
% 6.19/1.17    ( ! [X2,X3] : (k5_xboole_0(X2,X3) = k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(X2,X3)))) )),
% 6.19/1.17    inference(backward_demodulation,[],[f132,f161])).
% 6.19/1.17  fof(f161,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 6.19/1.17    inference(superposition,[],[f43,f155])).
% 6.19/1.17  fof(f132,plain,(
% 6.19/1.17    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(k4_xboole_0(X2,X2),X3)) = k5_xboole_0(X2,X3)) )),
% 6.19/1.17    inference(superposition,[],[f43,f55])).
% 6.19/1.17  fof(f55,plain,(
% 6.19/1.17    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 6.19/1.17    inference(definition_unfolding,[],[f25,f29])).
% 6.19/1.17  fof(f25,plain,(
% 6.19/1.17    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 6.19/1.17    inference(cnf_transformation,[],[f18])).
% 6.19/1.17  fof(f18,plain,(
% 6.19/1.17    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 6.19/1.17    inference(rectify,[],[f3])).
% 6.19/1.17  fof(f3,axiom,(
% 6.19/1.17    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 6.19/1.17  fof(f840,plain,(
% 6.19/1.17    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 6.19/1.17    inference(backward_demodulation,[],[f161,f833])).
% 6.19/1.17  fof(f5334,plain,(
% 6.19/1.17    ~r1_tarski(k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)),k2_tarski(sK0,sK1))),k1_xboole_0)),
% 6.19/1.17    inference(forward_demodulation,[],[f5318,f43])).
% 6.19/1.17  fof(f5318,plain,(
% 6.19/1.17    ~r1_tarski(k5_xboole_0(k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0))),k2_tarski(sK0,sK1)),k1_xboole_0)),
% 6.19/1.17    inference(unit_resulting_resolution,[],[f53,f1214])).
% 6.19/1.17  fof(f1214,plain,(
% 6.19/1.17    ( ! [X4,X3] : (~r1_tarski(k5_xboole_0(X3,X4),k1_xboole_0) | X3 = X4) )),
% 6.19/1.17    inference(superposition,[],[f1140,f804])).
% 6.19/1.17  fof(f804,plain,(
% 6.19/1.17    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = X1 | ~r1_tarski(X2,k1_xboole_0)) )),
% 6.19/1.17    inference(forward_demodulation,[],[f803,f760])).
% 6.19/1.17  fof(f803,plain,(
% 6.19/1.17    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = X1 | ~r1_tarski(X2,k4_xboole_0(k1_xboole_0,X1))) )),
% 6.19/1.17    inference(forward_demodulation,[],[f802,f761])).
% 6.19/1.17  fof(f802,plain,(
% 6.19/1.17    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X2,k4_xboole_0(k1_xboole_0,X1))) )),
% 6.19/1.17    inference(forward_demodulation,[],[f772,f760])).
% 6.19/1.17  fof(f772,plain,(
% 6.19/1.17    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(k1_xboole_0,X2)) | ~r1_tarski(X2,k4_xboole_0(k1_xboole_0,X1))) )),
% 6.19/1.17    inference(backward_demodulation,[],[f395,f760])).
% 6.19/1.17  fof(f395,plain,(
% 6.19/1.17    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X1,k4_xboole_0(k4_xboole_0(k1_xboole_0,X1),X2)) | ~r1_tarski(X2,k4_xboole_0(k1_xboole_0,X1))) )),
% 6.19/1.17    inference(superposition,[],[f131,f281])).
% 6.19/1.17  fof(f281,plain,(
% 6.19/1.17    ( ! [X6,X7] : (k5_xboole_0(X6,X7) = k4_xboole_0(X6,X7) | ~r1_tarski(X7,X6)) )),
% 6.19/1.17    inference(superposition,[],[f52,f210])).
% 6.19/1.17  fof(f53,plain,(
% 6.19/1.17    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK0),k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK0)))),
% 6.19/1.17    inference(definition_unfolding,[],[f22,f51])).
% 6.19/1.17  fof(f51,plain,(
% 6.19/1.17    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X0),k4_xboole_0(k2_tarski(X1,X2),k2_tarski(X0,X0)))) )),
% 6.19/1.17    inference(definition_unfolding,[],[f42,f29,f24])).
% 6.19/1.17  fof(f42,plain,(
% 6.19/1.17    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 6.19/1.17    inference(cnf_transformation,[],[f14])).
% 6.19/1.17  fof(f14,axiom,(
% 6.19/1.17    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 6.19/1.17  fof(f22,plain,(
% 6.19/1.17    k2_tarski(sK0,sK1) != k1_enumset1(sK0,sK0,sK1)),
% 6.19/1.17    inference(cnf_transformation,[],[f19])).
% 6.19/1.17  fof(f19,plain,(
% 6.19/1.17    ? [X0,X1] : k2_tarski(X0,X1) != k1_enumset1(X0,X0,X1)),
% 6.19/1.17    inference(ennf_transformation,[],[f17])).
% 6.19/1.17  fof(f17,negated_conjecture,(
% 6.19/1.17    ~! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.19/1.17    inference(negated_conjecture,[],[f16])).
% 6.19/1.17  fof(f16,conjecture,(
% 6.19/1.17    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 6.19/1.17    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 6.19/1.17  % SZS output end Proof for theBenchmark
% 6.19/1.17  % (16865)------------------------------
% 6.19/1.17  % (16865)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.19/1.17  % (16865)Termination reason: Refutation
% 6.19/1.17  
% 6.19/1.17  % (16865)Memory used [KB]: 10874
% 6.19/1.17  % (16865)Time elapsed: 0.761 s
% 6.19/1.17  % (16865)------------------------------
% 6.19/1.17  % (16865)------------------------------
% 6.19/1.17  % (16840)Success in time 0.802 s
%------------------------------------------------------------------------------
