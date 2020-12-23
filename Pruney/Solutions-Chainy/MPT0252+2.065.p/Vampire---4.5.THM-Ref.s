%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:00 EST 2020

% Result     : Theorem 2.03s
% Output     : Refutation 2.16s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 435 expanded)
%              Number of leaves         :   24 ( 147 expanded)
%              Depth                    :   16
%              Number of atoms          :  126 ( 477 expanded)
%              Number of equality atoms :   61 ( 400 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1266,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f39,f1162,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f54,f68])).

fof(f68,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f60,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f61,f66])).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f62,f64])).

fof(f64,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f62,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f1162,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    inference(forward_demodulation,[],[f1159,f183])).

fof(f183,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f123,f48])).

fof(f48,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f123,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f121,f87])).

fof(f87,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f48,f42])).

fof(f42,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f121,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f55,f119])).

fof(f119,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f118,f42])).

fof(f118,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f76,f77])).

fof(f77,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f41,f71])).

fof(f71,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f70])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f76,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f40,f72])).

fof(f72,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f51,f71])).

fof(f51,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f55,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1159,plain,(
    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(superposition,[],[f126,f1008])).

fof(f1008,plain,(
    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1006,f109])).

fof(f109,plain,(
    ! [X2,X3] : ~ r2_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X2) ),
    inference(resolution,[],[f80,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r2_xboole_0(X1,X0)
        & r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f46,f71])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1006,plain,
    ( sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | r2_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(resolution,[],[f1005,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f1005,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(forward_demodulation,[],[f956,f178])).

fof(f178,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5) ),
    inference(superposition,[],[f86,f74])).

fof(f74,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f65,f71,f66,f70])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f63,f66,f71,f67,f73])).

fof(f73,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f43,f70])).

fof(f43,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f956,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(backward_demodulation,[],[f159,f178])).

fof(f159,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(forward_demodulation,[],[f75,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f59,f68,f68])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f75,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f38,f71,f70])).

fof(f38,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f126,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(forward_demodulation,[],[f81,f55])).

fof(f81,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f47,f72])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f39,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 18:39:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (9091)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.50  % (9091)Refutation not found, incomplete strategy% (9091)------------------------------
% 0.20/0.50  % (9091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (9091)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (9091)Memory used [KB]: 6140
% 0.20/0.50  % (9091)Time elapsed: 0.084 s
% 0.20/0.50  % (9091)------------------------------
% 0.20/0.50  % (9091)------------------------------
% 0.20/0.51  % (9110)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.51  % (9101)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.51  % (9098)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.51  % (9111)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (9111)Refutation not found, incomplete strategy% (9111)------------------------------
% 0.20/0.51  % (9111)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9111)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9111)Memory used [KB]: 1791
% 0.20/0.51  % (9111)Time elapsed: 0.064 s
% 0.20/0.51  % (9111)------------------------------
% 0.20/0.51  % (9111)------------------------------
% 0.20/0.51  % (9110)Refutation not found, incomplete strategy% (9110)------------------------------
% 0.20/0.51  % (9110)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (9110)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (9110)Memory used [KB]: 10746
% 0.20/0.51  % (9110)Time elapsed: 0.099 s
% 0.20/0.51  % (9110)------------------------------
% 0.20/0.51  % (9110)------------------------------
% 0.20/0.52  % (9108)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (9108)Refutation not found, incomplete strategy% (9108)------------------------------
% 0.20/0.52  % (9108)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (9108)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (9108)Memory used [KB]: 10746
% 0.20/0.52  % (9108)Time elapsed: 0.112 s
% 0.20/0.52  % (9108)------------------------------
% 0.20/0.52  % (9108)------------------------------
% 0.20/0.52  % (9087)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (9089)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.52  % (9094)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.53  % (9116)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (9103)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.53  % (9088)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.53  % (9092)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.53  % (9087)Refutation not found, incomplete strategy% (9087)------------------------------
% 0.20/0.53  % (9087)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (9087)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (9087)Memory used [KB]: 1663
% 0.20/0.53  % (9087)Time elapsed: 0.112 s
% 0.20/0.53  % (9087)------------------------------
% 0.20/0.53  % (9087)------------------------------
% 0.20/0.53  % (9103)Refutation not found, incomplete strategy% (9103)------------------------------
% 0.20/0.53  % (9103)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (9103)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (9103)Memory used [KB]: 6140
% 0.20/0.53  % (9103)Time elapsed: 0.084 s
% 0.20/0.53  % (9103)------------------------------
% 0.20/0.53  % (9103)------------------------------
% 0.20/0.53  % (9104)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.53  % (9099)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.53  % (9115)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.53  % (9098)Refutation not found, incomplete strategy% (9098)------------------------------
% 0.20/0.53  % (9098)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (9098)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (9098)Memory used [KB]: 10618
% 0.20/0.53  % (9098)Time elapsed: 0.096 s
% 0.20/0.53  % (9098)------------------------------
% 0.20/0.53  % (9098)------------------------------
% 0.20/0.53  % (9099)Refutation not found, incomplete strategy% (9099)------------------------------
% 0.20/0.53  % (9099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (9099)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.53  
% 0.20/0.53  % (9099)Memory used [KB]: 10618
% 0.20/0.53  % (9099)Time elapsed: 0.124 s
% 0.20/0.53  % (9099)------------------------------
% 0.20/0.53  % (9099)------------------------------
% 0.20/0.53  % (9093)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.53  % (9095)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (9107)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.54  % (9106)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.54  % (9095)Refutation not found, incomplete strategy% (9095)------------------------------
% 0.20/0.54  % (9095)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (9095)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (9095)Memory used [KB]: 10746
% 0.20/0.54  % (9095)Time elapsed: 0.127 s
% 0.20/0.54  % (9095)------------------------------
% 0.20/0.54  % (9095)------------------------------
% 0.20/0.54  % (9112)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (9089)Refutation not found, incomplete strategy% (9089)------------------------------
% 0.20/0.54  % (9089)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.54  % (9089)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.54  
% 0.20/0.54  % (9089)Memory used [KB]: 10746
% 0.20/0.54  % (9089)Time elapsed: 0.109 s
% 0.20/0.54  % (9089)------------------------------
% 0.20/0.54  % (9089)------------------------------
% 0.20/0.54  % (9102)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (9117)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.55  % (9114)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (9090)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.55  % (9096)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (9109)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.56  % (9113)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (9109)Refutation not found, incomplete strategy% (9109)------------------------------
% 0.20/0.56  % (9109)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (9100)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  % (9105)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.49/0.56  % (9096)Refutation not found, incomplete strategy% (9096)------------------------------
% 1.49/0.56  % (9096)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (9114)Refutation not found, incomplete strategy% (9114)------------------------------
% 1.49/0.56  % (9114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (9114)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (9114)Memory used [KB]: 10746
% 1.49/0.56  % (9114)Time elapsed: 0.150 s
% 1.49/0.56  % (9114)------------------------------
% 1.49/0.56  % (9114)------------------------------
% 1.49/0.56  % (9113)Refutation not found, incomplete strategy% (9113)------------------------------
% 1.49/0.56  % (9113)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (9096)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (9096)Memory used [KB]: 10618
% 1.49/0.56  % (9096)Time elapsed: 0.144 s
% 1.49/0.56  % (9096)------------------------------
% 1.49/0.56  % (9096)------------------------------
% 1.49/0.56  % (9105)Refutation not found, incomplete strategy% (9105)------------------------------
% 1.49/0.56  % (9105)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.56  % (9105)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.56  
% 1.49/0.56  % (9105)Memory used [KB]: 10618
% 1.49/0.56  % (9105)Time elapsed: 0.149 s
% 1.49/0.56  % (9105)------------------------------
% 1.49/0.56  % (9105)------------------------------
% 1.49/0.57  % (9113)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (9113)Memory used [KB]: 6396
% 1.49/0.57  % (9113)Time elapsed: 0.151 s
% 1.49/0.57  % (9113)------------------------------
% 1.49/0.57  % (9113)------------------------------
% 1.49/0.57  % (9109)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (9109)Memory used [KB]: 1791
% 1.49/0.57  % (9109)Time elapsed: 0.149 s
% 1.49/0.57  % (9109)------------------------------
% 1.49/0.57  % (9109)------------------------------
% 1.72/0.60  % (9194)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.72/0.61  % (9194)Refutation not found, incomplete strategy% (9194)------------------------------
% 1.72/0.61  % (9194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.72/0.61  % (9194)Termination reason: Refutation not found, incomplete strategy
% 1.72/0.61  
% 1.72/0.61  % (9194)Memory used [KB]: 6140
% 1.72/0.61  % (9194)Time elapsed: 0.071 s
% 1.72/0.61  % (9194)------------------------------
% 1.72/0.61  % (9194)------------------------------
% 1.72/0.62  % (9202)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.03/0.64  % (9117)Refutation found. Thanks to Tanya!
% 2.03/0.64  % SZS status Theorem for theBenchmark
% 2.03/0.65  % (9200)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.16/0.66  % (9210)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.16/0.66  % SZS output start Proof for theBenchmark
% 2.16/0.66  fof(f1266,plain,(
% 2.16/0.66    $false),
% 2.16/0.66    inference(unit_resulting_resolution,[],[f39,f1162,f84])).
% 2.16/0.66  fof(f84,plain,(
% 2.16/0.66    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f56,f70])).
% 2.16/0.66  fof(f70,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f50,f69])).
% 2.16/0.66  fof(f69,plain,(
% 2.16/0.66    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f54,f68])).
% 2.16/0.66  fof(f68,plain,(
% 2.16/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f60,f67])).
% 2.16/0.66  fof(f67,plain,(
% 2.16/0.66    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f61,f66])).
% 2.16/0.66  fof(f66,plain,(
% 2.16/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f62,f64])).
% 2.16/0.66  fof(f64,plain,(
% 2.16/0.66    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f22])).
% 2.16/0.66  fof(f22,axiom,(
% 2.16/0.66    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.16/0.66  fof(f62,plain,(
% 2.16/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f21])).
% 2.16/0.66  fof(f21,axiom,(
% 2.16/0.66    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.16/0.66  fof(f61,plain,(
% 2.16/0.66    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f20])).
% 2.16/0.66  fof(f20,axiom,(
% 2.16/0.66    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.16/0.66  fof(f60,plain,(
% 2.16/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f19])).
% 2.16/0.66  fof(f19,axiom,(
% 2.16/0.66    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.16/0.66  fof(f54,plain,(
% 2.16/0.66    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f18])).
% 2.16/0.66  fof(f18,axiom,(
% 2.16/0.66    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.16/0.66  fof(f50,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f17])).
% 2.16/0.66  fof(f17,axiom,(
% 2.16/0.66    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.16/0.66  fof(f56,plain,(
% 2.16/0.66    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f37])).
% 2.16/0.66  fof(f37,plain,(
% 2.16/0.66    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.16/0.66    inference(flattening,[],[f36])).
% 2.16/0.66  fof(f36,plain,(
% 2.16/0.66    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.16/0.66    inference(nnf_transformation,[],[f24])).
% 2.16/0.66  fof(f24,axiom,(
% 2.16/0.66    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.16/0.66  fof(f1162,plain,(
% 2.16/0.66    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 2.16/0.66    inference(forward_demodulation,[],[f1159,f183])).
% 2.16/0.66  fof(f183,plain,(
% 2.16/0.66    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 2.16/0.66    inference(superposition,[],[f123,f48])).
% 2.16/0.66  fof(f48,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f1])).
% 2.16/0.66  fof(f1,axiom,(
% 2.16/0.66    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.16/0.66  fof(f123,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.16/0.66    inference(forward_demodulation,[],[f121,f87])).
% 2.16/0.66  fof(f87,plain,(
% 2.16/0.66    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.16/0.66    inference(superposition,[],[f48,f42])).
% 2.16/0.66  fof(f42,plain,(
% 2.16/0.66    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.66    inference(cnf_transformation,[],[f8])).
% 2.16/0.66  fof(f8,axiom,(
% 2.16/0.66    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.16/0.66  fof(f121,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.16/0.66    inference(superposition,[],[f55,f119])).
% 2.16/0.66  fof(f119,plain,(
% 2.16/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.16/0.66    inference(forward_demodulation,[],[f118,f42])).
% 2.16/0.66  fof(f118,plain,(
% 2.16/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 2.16/0.66    inference(forward_demodulation,[],[f76,f77])).
% 2.16/0.66  fof(f77,plain,(
% 2.16/0.66    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 2.16/0.66    inference(definition_unfolding,[],[f41,f71])).
% 2.16/0.66  fof(f71,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.16/0.66    inference(definition_unfolding,[],[f49,f70])).
% 2.16/0.66  fof(f49,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f23])).
% 2.16/0.66  fof(f23,axiom,(
% 2.16/0.66    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.16/0.66  fof(f41,plain,(
% 2.16/0.66    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.16/0.66    inference(cnf_transformation,[],[f6])).
% 2.16/0.66  fof(f6,axiom,(
% 2.16/0.66    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 2.16/0.66  fof(f76,plain,(
% 2.16/0.66    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,k1_xboole_0)))) )),
% 2.16/0.66    inference(definition_unfolding,[],[f40,f72])).
% 2.16/0.66  fof(f72,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.16/0.66    inference(definition_unfolding,[],[f51,f71])).
% 2.16/0.66  fof(f51,plain,(
% 2.16/0.66    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f12])).
% 2.16/0.66  fof(f12,axiom,(
% 2.16/0.66    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.16/0.66  fof(f40,plain,(
% 2.16/0.66    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f7])).
% 2.16/0.66  fof(f7,axiom,(
% 2.16/0.66    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 2.16/0.66  fof(f55,plain,(
% 2.16/0.66    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f11])).
% 2.16/0.66  fof(f11,axiom,(
% 2.16/0.66    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.16/0.66  fof(f1159,plain,(
% 2.16/0.66    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 2.16/0.66    inference(superposition,[],[f126,f1008])).
% 2.16/0.66  fof(f1008,plain,(
% 2.16/0.66    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 2.16/0.66    inference(subsumption_resolution,[],[f1006,f109])).
% 2.16/0.66  fof(f109,plain,(
% 2.16/0.66    ( ! [X2,X3] : (~r2_xboole_0(k3_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)),X2)) )),
% 2.16/0.66    inference(resolution,[],[f80,f53])).
% 2.16/0.66  fof(f53,plain,(
% 2.16/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r2_xboole_0(X1,X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f33])).
% 2.16/0.66  fof(f33,plain,(
% 2.16/0.66    ! [X0,X1] : (~r2_xboole_0(X1,X0) | ~r1_tarski(X0,X1))),
% 2.16/0.66    inference(ennf_transformation,[],[f9])).
% 2.16/0.66  fof(f9,axiom,(
% 2.16/0.66    ! [X0,X1] : ~(r2_xboole_0(X1,X0) & r1_tarski(X0,X1))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_xboole_1)).
% 2.16/0.66  fof(f80,plain,(
% 2.16/0.66    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.16/0.66    inference(definition_unfolding,[],[f46,f71])).
% 2.16/0.66  fof(f46,plain,(
% 2.16/0.66    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f10])).
% 2.16/0.66  fof(f10,axiom,(
% 2.16/0.66    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.16/0.66  fof(f1006,plain,(
% 2.16/0.66    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | r2_xboole_0(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 2.16/0.66    inference(resolution,[],[f1005,f52])).
% 2.16/0.66  fof(f52,plain,(
% 2.16/0.66    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f32])).
% 2.16/0.66  fof(f32,plain,(
% 2.16/0.66    ! [X0,X1] : (r2_xboole_0(X0,X1) | X0 = X1 | ~r1_tarski(X0,X1))),
% 2.16/0.66    inference(flattening,[],[f31])).
% 2.16/0.66  fof(f31,plain,(
% 2.16/0.66    ! [X0,X1] : (r2_xboole_0(X0,X1) | (X0 = X1 | ~r1_tarski(X0,X1)))),
% 2.16/0.66    inference(ennf_transformation,[],[f29])).
% 2.16/0.66  fof(f29,plain,(
% 2.16/0.66    ! [X0,X1] : ((X0 != X1 & r1_tarski(X0,X1)) => r2_xboole_0(X0,X1))),
% 2.16/0.66    inference(unused_predicate_definition_removal,[],[f2])).
% 2.16/0.66  fof(f2,axiom,(
% 2.16/0.66    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 2.16/0.66  fof(f1005,plain,(
% 2.16/0.66    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 2.16/0.66    inference(forward_demodulation,[],[f956,f178])).
% 2.16/0.66  fof(f178,plain,(
% 2.16/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X5)) )),
% 2.16/0.66    inference(superposition,[],[f86,f74])).
% 2.16/0.66  fof(f74,plain,(
% 2.16/0.66    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) )),
% 2.16/0.66    inference(definition_unfolding,[],[f65,f71,f66,f70])).
% 2.16/0.66  fof(f65,plain,(
% 2.16/0.66    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f15])).
% 2.16/0.66  fof(f15,axiom,(
% 2.16/0.66    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_enumset1)).
% 2.16/0.66  fof(f86,plain,(
% 2.16/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)))) )),
% 2.16/0.66    inference(definition_unfolding,[],[f63,f66,f71,f67,f73])).
% 2.16/0.66  fof(f73,plain,(
% 2.16/0.66    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f43,f70])).
% 2.16/0.66  fof(f43,plain,(
% 2.16/0.66    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f16])).
% 2.16/0.66  fof(f16,axiom,(
% 2.16/0.66    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.16/0.66  fof(f63,plain,(
% 2.16/0.66    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 2.16/0.66    inference(cnf_transformation,[],[f14])).
% 2.16/0.66  fof(f14,axiom,(
% 2.16/0.66    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 2.16/0.66  fof(f956,plain,(
% 2.16/0.66    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 2.16/0.66    inference(backward_demodulation,[],[f159,f178])).
% 2.16/0.66  fof(f159,plain,(
% 2.16/0.66    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 2.16/0.66    inference(forward_demodulation,[],[f75,f85])).
% 2.16/0.66  fof(f85,plain,(
% 2.16/0.66    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f59,f68,f68])).
% 2.16/0.66  fof(f59,plain,(
% 2.16/0.66    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f13])).
% 2.16/0.66  fof(f13,axiom,(
% 2.16/0.66    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 2.16/0.66  fof(f75,plain,(
% 2.16/0.66    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 2.16/0.66    inference(definition_unfolding,[],[f38,f71,f70])).
% 2.16/0.66  fof(f38,plain,(
% 2.16/0.66    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.16/0.66    inference(cnf_transformation,[],[f35])).
% 2.16/0.66  fof(f35,plain,(
% 2.16/0.66    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 2.16/0.66    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).
% 2.16/0.66  fof(f34,plain,(
% 2.16/0.66    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 2.16/0.66    introduced(choice_axiom,[])).
% 2.16/0.66  fof(f30,plain,(
% 2.16/0.66    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 2.16/0.66    inference(ennf_transformation,[],[f26])).
% 2.16/0.66  fof(f26,negated_conjecture,(
% 2.16/0.66    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.16/0.66    inference(negated_conjecture,[],[f25])).
% 2.16/0.66  fof(f25,conjecture,(
% 2.16/0.66    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 2.16/0.66  fof(f126,plain,(
% 2.16/0.66    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 2.16/0.66    inference(forward_demodulation,[],[f81,f55])).
% 2.16/0.66  fof(f81,plain,(
% 2.16/0.66    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 2.16/0.66    inference(definition_unfolding,[],[f47,f72])).
% 2.16/0.66  fof(f47,plain,(
% 2.16/0.66    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.16/0.66    inference(cnf_transformation,[],[f5])).
% 2.16/0.66  fof(f5,axiom,(
% 2.16/0.66    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 2.16/0.66    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 2.16/0.66  fof(f39,plain,(
% 2.16/0.66    ~r2_hidden(sK0,sK2)),
% 2.16/0.66    inference(cnf_transformation,[],[f35])).
% 2.16/0.66  % SZS output end Proof for theBenchmark
% 2.16/0.66  % (9117)------------------------------
% 2.16/0.66  % (9117)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.16/0.66  % (9117)Termination reason: Refutation
% 2.16/0.66  
% 2.16/0.66  % (9117)Memory used [KB]: 3070
% 2.16/0.66  % (9117)Time elapsed: 0.233 s
% 2.16/0.66  % (9117)------------------------------
% 2.16/0.66  % (9117)------------------------------
% 2.16/0.67  % (9083)Success in time 0.289 s
%------------------------------------------------------------------------------
