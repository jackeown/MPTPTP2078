%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:55 EST 2020

% Result     : Theorem 1.32s
% Output     : Refutation 1.32s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 977 expanded)
%              Number of leaves         :   23 ( 311 expanded)
%              Depth                    :   23
%              Number of atoms          :  172 (1182 expanded)
%              Number of equality atoms :  103 ( 980 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    7 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f416,plain,(
    $false ),
    inference(trivial_inequality_removal,[],[f415])).

fof(f415,plain,(
    k1_xboole_0 != k1_xboole_0 ),
    inference(superposition,[],[f409,f357])).

fof(f357,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f344,f350,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( sP4(sK3(X0,X1,X2),X1,X0)
      | r2_hidden(sK3(X0,X1,X2),X2)
      | k2_zfmisc_1(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f350,plain,(
    ! [X0,X1] : ~ sP4(X0,X1,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f344,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK5(X0,X1,X3),X0)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f344,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f343,f38])).

fof(f38,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f343,plain,(
    ! [X0] : ~ r2_hidden(X0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(superposition,[],[f134,f80])).

fof(f80,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f75])).

fof(f75,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f44,f74])).

fof(f74,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f45,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f50,f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f63,f71])).

fof(f71,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f67,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f68,f69])).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f67,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f45,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f44,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f43,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f134,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))) ),
    inference(backward_demodulation,[],[f91,f132])).

fof(f132,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f127,f89])).

fof(f89,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(backward_demodulation,[],[f88,f80])).

fof(f88,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(forward_demodulation,[],[f79,f38])).

fof(f79,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f42,f76])).

fof(f76,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f75])).

fof(f47,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f42,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f127,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f51,f38])).

fof(f51,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f91,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) ),
    inference(forward_demodulation,[],[f87,f51])).

fof(f87,plain,(
    ! [X2,X1] : ~ r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) ) ),
    inference(definition_unfolding,[],[f61,f77,f78])).

fof(f78,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f39,f74])).

fof(f39,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f77,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f46,f76])).

fof(f46,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | ~ r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))
    <=> ( X0 != X2
        & r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

fof(f409,plain,(
    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1) ),
    inference(forward_demodulation,[],[f408,f398])).

fof(f398,plain,(
    k1_xboole_0 = sK0 ),
    inference(unit_resulting_resolution,[],[f371,f292])).

fof(f292,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 = sK0 ),
    inference(trivial_inequality_removal,[],[f287])).

fof(f287,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0)
    | k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 = sK0 ),
    inference(superposition,[],[f34,f285])).

fof(f285,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(duplicate_literal_removal,[],[f282])).

fof(f282,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK0
    | k1_xboole_0 = sK0 ),
    inference(resolution,[],[f281,f40])).

fof(f40,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f281,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(duplicate_literal_removal,[],[f278])).

fof(f278,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0
      | k1_xboole_0 = sK1 ) ),
    inference(resolution,[],[f271,f40])).

fof(f271,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,sK1)
      | ~ r2_hidden(X0,sK0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f226,f99])).

fof(f99,plain,(
    ! [X0,X1] : ~ r2_hidden(k4_tarski(X0,X1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f97,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,k1_xboole_0)
      | r1_tarski(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f49,f36])).

fof(f36,plain,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    k1_xboole_0 = k3_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f97,plain,(
    ! [X0,X1] : ~ r1_tarski(k4_tarski(X0,X1),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f37,f41,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1)
      | ~ r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f41,plain,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : ~ v1_xboole_0(k4_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_zfmisc_1)).

fof(f37,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f226,plain,(
    ! [X17,X16] :
      ( r2_hidden(k4_tarski(X17,X16),k1_xboole_0)
      | ~ r2_hidden(X17,sK0)
      | ~ r2_hidden(X16,sK1)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(resolution,[],[f86,f103])).

fof(f103,plain,(
    ! [X0] :
      ( ~ sP4(X0,sK1,sK0)
      | r2_hidden(X0,k1_xboole_0)
      | k1_xboole_0 = sK1
      | k1_xboole_0 = sK0 ) ),
    inference(superposition,[],[f85,f35])).

fof(f35,plain,
    ( k1_xboole_0 = k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 = sK1
    | k1_xboole_0 = sK0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_zfmisc_1(X0,X1))
      | ~ sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    ! [X4,X0,X5,X1] :
      ( sP4(k4_tarski(X4,X5),X1,X0)
      | ~ r2_hidden(X5,X1)
      | ~ r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X4,X0,X5,X3,X1] :
      ( ~ r2_hidden(X4,X0)
      | ~ r2_hidden(X5,X1)
      | k4_tarski(X4,X5) != X3
      | sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f34,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f28])).

fof(f371,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f344,f351,f58])).

fof(f351,plain,(
    ! [X0,X1] : ~ sP4(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f344,f54])).

fof(f54,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | ~ sP4(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f408,plain,(
    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f406])).

fof(f406,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k2_zfmisc_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f33,f398])).

fof(f33,plain,
    ( k1_xboole_0 != k2_zfmisc_1(sK0,sK1)
    | k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:28:07 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (13366)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (13348)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.19/0.51  % (13358)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.19/0.52  % (13350)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.19/0.52  % (13355)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.32/0.54  % (13371)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.32/0.54  % (13344)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.32/0.54  % (13369)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.32/0.54  % (13359)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.32/0.54  % (13343)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.32/0.54  % (13347)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.32/0.54  % (13345)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.32/0.54  % (13345)Refutation not found, incomplete strategy% (13345)------------------------------
% 1.32/0.54  % (13345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.54  % (13345)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.54  
% 1.32/0.54  % (13345)Memory used [KB]: 10746
% 1.32/0.54  % (13345)Time elapsed: 0.124 s
% 1.32/0.54  % (13345)------------------------------
% 1.32/0.54  % (13345)------------------------------
% 1.32/0.54  % (13346)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.32/0.55  % (13354)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.32/0.55  % (13372)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.32/0.55  % (13361)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.32/0.55  % (13367)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.32/0.55  % (13353)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.32/0.55  % (13356)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.32/0.55  % (13363)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.32/0.55  % (13351)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.32/0.55  % (13362)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.32/0.55  % (13363)Refutation not found, incomplete strategy% (13363)------------------------------
% 1.32/0.55  % (13363)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.55  % (13363)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.55  
% 1.32/0.55  % (13363)Memory used [KB]: 10746
% 1.32/0.55  % (13363)Time elapsed: 0.149 s
% 1.32/0.55  % (13363)------------------------------
% 1.32/0.55  % (13363)------------------------------
% 1.32/0.56  % (13351)Refutation not found, incomplete strategy% (13351)------------------------------
% 1.32/0.56  % (13351)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (13364)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.32/0.56  % (13360)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.32/0.56  % (13370)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.32/0.56  % (13364)Refutation not found, incomplete strategy% (13364)------------------------------
% 1.32/0.56  % (13364)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.56  % (13364)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (13364)Memory used [KB]: 1663
% 1.32/0.56  % (13364)Time elapsed: 0.147 s
% 1.32/0.56  % (13364)------------------------------
% 1.32/0.56  % (13364)------------------------------
% 1.32/0.56  % (13349)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.32/0.56  % (13351)Termination reason: Refutation not found, incomplete strategy
% 1.32/0.56  
% 1.32/0.56  % (13351)Memory used [KB]: 10746
% 1.32/0.56  % (13351)Time elapsed: 0.149 s
% 1.32/0.56  % (13351)------------------------------
% 1.32/0.56  % (13351)------------------------------
% 1.32/0.57  % (13368)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.32/0.57  % (13365)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.32/0.57  % (13352)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.32/0.57  % (13367)Refutation found. Thanks to Tanya!
% 1.32/0.57  % SZS status Theorem for theBenchmark
% 1.32/0.57  % SZS output start Proof for theBenchmark
% 1.32/0.57  fof(f416,plain,(
% 1.32/0.57    $false),
% 1.32/0.57    inference(trivial_inequality_removal,[],[f415])).
% 1.32/0.57  fof(f415,plain,(
% 1.32/0.57    k1_xboole_0 != k1_xboole_0),
% 1.32/0.57    inference(superposition,[],[f409,f357])).
% 1.32/0.57  fof(f357,plain,(
% 1.32/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) )),
% 1.32/0.57    inference(unit_resulting_resolution,[],[f344,f350,f58])).
% 1.32/0.57  fof(f58,plain,(
% 1.32/0.57    ( ! [X2,X0,X1] : (sP4(sK3(X0,X1,X2),X1,X0) | r2_hidden(sK3(X0,X1,X2),X2) | k2_zfmisc_1(X0,X1) = X2) )),
% 1.32/0.57    inference(cnf_transformation,[],[f17])).
% 1.32/0.57  fof(f17,axiom,(
% 1.32/0.57    ! [X0,X1,X2] : (k2_zfmisc_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4,X5] : (k4_tarski(X4,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X4,X0))))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).
% 1.32/0.57  fof(f350,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~sP4(X0,X1,k1_xboole_0)) )),
% 1.32/0.57    inference(unit_resulting_resolution,[],[f344,f53])).
% 1.32/0.57  fof(f53,plain,(
% 1.32/0.57    ( ! [X0,X3,X1] : (r2_hidden(sK5(X0,X1,X3),X0) | ~sP4(X3,X1,X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f17])).
% 1.32/0.57  fof(f344,plain,(
% 1.32/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 1.32/0.57    inference(forward_demodulation,[],[f343,f38])).
% 1.32/0.57  fof(f38,plain,(
% 1.32/0.57    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f8])).
% 1.32/0.57  fof(f8,axiom,(
% 1.32/0.57    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 1.32/0.57  fof(f343,plain,(
% 1.32/0.57    ( ! [X0] : (~r2_hidden(X0,k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 1.32/0.57    inference(superposition,[],[f134,f80])).
% 1.32/0.57  fof(f80,plain,(
% 1.32/0.57    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.32/0.57    inference(definition_unfolding,[],[f43,f75])).
% 1.32/0.57  fof(f75,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.32/0.57    inference(definition_unfolding,[],[f44,f74])).
% 1.32/0.57  fof(f74,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.32/0.57    inference(definition_unfolding,[],[f45,f73])).
% 1.32/0.57  fof(f73,plain,(
% 1.32/0.57    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.32/0.57    inference(definition_unfolding,[],[f50,f72])).
% 1.32/0.57  fof(f72,plain,(
% 1.32/0.57    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.32/0.57    inference(definition_unfolding,[],[f63,f71])).
% 1.32/0.57  fof(f71,plain,(
% 1.32/0.57    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.32/0.57    inference(definition_unfolding,[],[f67,f70])).
% 1.32/0.57  fof(f70,plain,(
% 1.32/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.57    inference(definition_unfolding,[],[f68,f69])).
% 1.32/0.57  fof(f69,plain,(
% 1.32/0.57    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f16])).
% 1.32/0.57  fof(f16,axiom,(
% 1.32/0.57    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.32/0.57  fof(f68,plain,(
% 1.32/0.57    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f15])).
% 1.32/0.57  fof(f15,axiom,(
% 1.32/0.57    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.32/0.57  fof(f67,plain,(
% 1.32/0.57    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f14])).
% 1.32/0.57  fof(f14,axiom,(
% 1.32/0.57    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.32/0.57  fof(f63,plain,(
% 1.32/0.57    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f13])).
% 1.32/0.57  fof(f13,axiom,(
% 1.32/0.57    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.32/0.57  fof(f50,plain,(
% 1.32/0.57    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f12])).
% 1.32/0.57  fof(f12,axiom,(
% 1.32/0.57    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.32/0.57  fof(f45,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f11])).
% 1.32/0.57  fof(f11,axiom,(
% 1.32/0.57    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.32/0.57  fof(f44,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f20])).
% 1.32/0.57  fof(f20,axiom,(
% 1.32/0.57    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.32/0.57  fof(f43,plain,(
% 1.32/0.57    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f27])).
% 1.32/0.57  fof(f27,plain,(
% 1.32/0.57    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.32/0.57    inference(rectify,[],[f1])).
% 1.32/0.57  fof(f1,axiom,(
% 1.32/0.57    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.32/0.57  fof(f134,plain,(
% 1.32/0.57    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))) )),
% 1.32/0.57    inference(backward_demodulation,[],[f91,f132])).
% 1.32/0.57  fof(f132,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.32/0.57    inference(forward_demodulation,[],[f127,f89])).
% 1.32/0.57  fof(f89,plain,(
% 1.32/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.32/0.57    inference(backward_demodulation,[],[f88,f80])).
% 1.32/0.57  fof(f88,plain,(
% 1.32/0.57    ( ! [X0] : (k5_xboole_0(k1_xboole_0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.32/0.57    inference(forward_demodulation,[],[f79,f38])).
% 1.32/0.57  fof(f79,plain,(
% 1.32/0.57    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 1.32/0.57    inference(definition_unfolding,[],[f42,f76])).
% 1.32/0.57  fof(f76,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.32/0.57    inference(definition_unfolding,[],[f47,f75])).
% 1.32/0.57  fof(f47,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f9])).
% 1.32/0.57  fof(f9,axiom,(
% 1.32/0.57    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.32/0.57  fof(f42,plain,(
% 1.32/0.57    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f26])).
% 1.32/0.57  fof(f26,plain,(
% 1.32/0.57    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.32/0.57    inference(rectify,[],[f2])).
% 1.32/0.57  fof(f2,axiom,(
% 1.32/0.57    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.32/0.57  fof(f127,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 1.32/0.57    inference(superposition,[],[f51,f38])).
% 1.32/0.57  fof(f51,plain,(
% 1.32/0.57    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f7])).
% 1.32/0.57  fof(f7,axiom,(
% 1.32/0.57    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.32/0.57  fof(f91,plain,(
% 1.32/0.57    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(X1,k5_xboole_0(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)))))))) )),
% 1.32/0.57    inference(forward_demodulation,[],[f87,f51])).
% 1.32/0.57  fof(f87,plain,(
% 1.32/0.57    ( ! [X2,X1] : (~r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 1.32/0.57    inference(equality_resolution,[],[f82])).
% 1.32/0.57  fof(f82,plain,(
% 1.32/0.57    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k5_xboole_0(X1,k5_xboole_0(k5_xboole_0(X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)),k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2))))))) )),
% 1.32/0.57    inference(definition_unfolding,[],[f61,f77,f78])).
% 1.32/0.57  fof(f78,plain,(
% 1.32/0.57    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.32/0.57    inference(definition_unfolding,[],[f39,f74])).
% 1.32/0.57  fof(f39,plain,(
% 1.32/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f10])).
% 1.32/0.57  fof(f10,axiom,(
% 1.32/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.32/0.57  fof(f77,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 1.32/0.57    inference(definition_unfolding,[],[f46,f76])).
% 1.32/0.57  fof(f46,plain,(
% 1.32/0.57    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f4])).
% 1.32/0.57  fof(f4,axiom,(
% 1.32/0.57    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.32/0.57  fof(f61,plain,(
% 1.32/0.57    ( ! [X2,X0,X1] : (X0 != X2 | ~r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2)))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f23])).
% 1.32/0.57  fof(f23,axiom,(
% 1.32/0.57    ! [X0,X1,X2] : (r2_hidden(X0,k4_xboole_0(X1,k1_tarski(X2))) <=> (X0 != X2 & r2_hidden(X0,X1)))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).
% 1.32/0.57  fof(f409,plain,(
% 1.32/0.57    k1_xboole_0 != k2_zfmisc_1(k1_xboole_0,sK1)),
% 1.32/0.57    inference(forward_demodulation,[],[f408,f398])).
% 1.32/0.57  fof(f398,plain,(
% 1.32/0.57    k1_xboole_0 = sK0),
% 1.32/0.57    inference(unit_resulting_resolution,[],[f371,f292])).
% 1.32/0.57  fof(f292,plain,(
% 1.32/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 = sK0),
% 1.32/0.57    inference(trivial_inequality_removal,[],[f287])).
% 1.32/0.57  fof(f287,plain,(
% 1.32/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,k1_xboole_0) | k1_xboole_0 != k1_xboole_0 | k1_xboole_0 = sK0),
% 1.32/0.57    inference(superposition,[],[f34,f285])).
% 1.32/0.57  fof(f285,plain,(
% 1.32/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.32/0.57    inference(duplicate_literal_removal,[],[f282])).
% 1.32/0.57  fof(f282,plain,(
% 1.32/0.57    k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK0),
% 1.32/0.57    inference(resolution,[],[f281,f40])).
% 1.32/0.57  fof(f40,plain,(
% 1.32/0.57    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 1.32/0.57    inference(cnf_transformation,[],[f29])).
% 1.32/0.57  fof(f29,plain,(
% 1.32/0.57    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 1.32/0.57    inference(ennf_transformation,[],[f3])).
% 1.32/0.57  fof(f3,axiom,(
% 1.32/0.57    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 1.32/0.57  fof(f281,plain,(
% 1.32/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.57    inference(duplicate_literal_removal,[],[f278])).
% 1.32/0.57  fof(f278,plain,(
% 1.32/0.57    ( ! [X0] : (~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0 | k1_xboole_0 = sK1) )),
% 1.32/0.57    inference(resolution,[],[f271,f40])).
% 1.32/0.57  fof(f271,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~r2_hidden(X1,sK1) | ~r2_hidden(X0,sK0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.57    inference(resolution,[],[f226,f99])).
% 1.32/0.57  fof(f99,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~r2_hidden(k4_tarski(X0,X1),k1_xboole_0)) )),
% 1.32/0.57    inference(unit_resulting_resolution,[],[f97,f95])).
% 1.32/0.57  fof(f95,plain,(
% 1.32/0.57    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0) | r1_tarski(X0,k1_xboole_0)) )),
% 1.32/0.57    inference(superposition,[],[f49,f36])).
% 1.32/0.57  fof(f36,plain,(
% 1.32/0.57    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.32/0.57    inference(cnf_transformation,[],[f22])).
% 1.32/0.57  fof(f22,axiom,(
% 1.32/0.57    k1_xboole_0 = k3_tarski(k1_xboole_0)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).
% 1.32/0.57  fof(f49,plain,(
% 1.32/0.57    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f32])).
% 1.32/0.57  fof(f32,plain,(
% 1.32/0.57    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 1.32/0.57    inference(ennf_transformation,[],[f19])).
% 1.32/0.57  fof(f19,axiom,(
% 1.32/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 1.32/0.57  fof(f97,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~r1_tarski(k4_tarski(X0,X1),k1_xboole_0)) )),
% 1.32/0.57    inference(unit_resulting_resolution,[],[f37,f41,f48])).
% 1.32/0.57  fof(f48,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~r1_tarski(X1,X0) | v1_xboole_0(X1) | ~r1_xboole_0(X1,X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f31])).
% 1.32/0.57  fof(f31,plain,(
% 1.32/0.57    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 1.32/0.57    inference(flattening,[],[f30])).
% 1.32/0.57  fof(f30,plain,(
% 1.32/0.57    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 1.32/0.57    inference(ennf_transformation,[],[f6])).
% 1.32/0.57  fof(f6,axiom,(
% 1.32/0.57    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).
% 1.32/0.57  fof(f41,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~v1_xboole_0(k4_tarski(X0,X1))) )),
% 1.32/0.57    inference(cnf_transformation,[],[f18])).
% 1.32/0.57  fof(f18,axiom,(
% 1.32/0.57    ! [X0,X1] : ~v1_xboole_0(k4_tarski(X0,X1))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_zfmisc_1)).
% 1.32/0.57  fof(f37,plain,(
% 1.32/0.57    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f5])).
% 1.32/0.57  fof(f5,axiom,(
% 1.32/0.57    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 1.32/0.57  fof(f226,plain,(
% 1.32/0.57    ( ! [X17,X16] : (r2_hidden(k4_tarski(X17,X16),k1_xboole_0) | ~r2_hidden(X17,sK0) | ~r2_hidden(X16,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.57    inference(resolution,[],[f86,f103])).
% 1.32/0.57  fof(f103,plain,(
% 1.32/0.57    ( ! [X0] : (~sP4(X0,sK1,sK0) | r2_hidden(X0,k1_xboole_0) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0) )),
% 1.32/0.57    inference(superposition,[],[f85,f35])).
% 1.32/0.57  fof(f35,plain,(
% 1.32/0.57    k1_xboole_0 = k2_zfmisc_1(sK0,sK1) | k1_xboole_0 = sK1 | k1_xboole_0 = sK0),
% 1.32/0.57    inference(cnf_transformation,[],[f28])).
% 1.32/0.57  fof(f28,plain,(
% 1.32/0.57    ? [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <~> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.57    inference(ennf_transformation,[],[f25])).
% 1.32/0.57  fof(f25,negated_conjecture,(
% 1.32/0.57    ~! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.57    inference(negated_conjecture,[],[f24])).
% 1.32/0.57  fof(f24,conjecture,(
% 1.32/0.57    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 1.32/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 1.32/0.57  fof(f85,plain,(
% 1.32/0.57    ( ! [X0,X3,X1] : (r2_hidden(X3,k2_zfmisc_1(X0,X1)) | ~sP4(X3,X1,X0)) )),
% 1.32/0.57    inference(equality_resolution,[],[f56])).
% 1.32/0.57  fof(f56,plain,(
% 1.32/0.57    ( ! [X2,X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X2) | k2_zfmisc_1(X0,X1) != X2) )),
% 1.32/0.57    inference(cnf_transformation,[],[f17])).
% 1.32/0.57  fof(f86,plain,(
% 1.32/0.57    ( ! [X4,X0,X5,X1] : (sP4(k4_tarski(X4,X5),X1,X0) | ~r2_hidden(X5,X1) | ~r2_hidden(X4,X0)) )),
% 1.32/0.57    inference(equality_resolution,[],[f52])).
% 1.32/0.57  fof(f52,plain,(
% 1.32/0.57    ( ! [X4,X0,X5,X3,X1] : (~r2_hidden(X4,X0) | ~r2_hidden(X5,X1) | k4_tarski(X4,X5) != X3 | sP4(X3,X1,X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f17])).
% 1.32/0.57  fof(f34,plain,(
% 1.32/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK1),
% 1.32/0.57    inference(cnf_transformation,[],[f28])).
% 1.32/0.57  fof(f371,plain,(
% 1.32/0.57    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 1.32/0.57    inference(unit_resulting_resolution,[],[f344,f351,f58])).
% 1.32/0.57  fof(f351,plain,(
% 1.32/0.57    ( ! [X0,X1] : (~sP4(X0,k1_xboole_0,X1)) )),
% 1.32/0.57    inference(unit_resulting_resolution,[],[f344,f54])).
% 1.32/0.57  fof(f54,plain,(
% 1.32/0.57    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | ~sP4(X3,X1,X0)) )),
% 1.32/0.57    inference(cnf_transformation,[],[f17])).
% 1.32/0.57  fof(f408,plain,(
% 1.32/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.32/0.57    inference(trivial_inequality_removal,[],[f406])).
% 1.32/0.57  fof(f406,plain,(
% 1.32/0.57    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k2_zfmisc_1(sK0,sK1)),
% 1.32/0.57    inference(backward_demodulation,[],[f33,f398])).
% 1.32/0.57  fof(f33,plain,(
% 1.32/0.57    k1_xboole_0 != k2_zfmisc_1(sK0,sK1) | k1_xboole_0 != sK0),
% 1.32/0.57    inference(cnf_transformation,[],[f28])).
% 1.32/0.57  % SZS output end Proof for theBenchmark
% 1.32/0.57  % (13367)------------------------------
% 1.32/0.57  % (13367)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.32/0.57  % (13367)Termination reason: Refutation
% 1.32/0.57  
% 1.32/0.57  % (13367)Memory used [KB]: 6524
% 1.32/0.57  % (13367)Time elapsed: 0.169 s
% 1.32/0.57  % (13367)------------------------------
% 1.32/0.57  % (13367)------------------------------
% 1.32/0.58  % (13342)Success in time 0.213 s
%------------------------------------------------------------------------------
