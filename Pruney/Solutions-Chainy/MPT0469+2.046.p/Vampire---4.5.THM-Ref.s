%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:47:40 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 581 expanded)
%              Number of leaves         :   21 ( 196 expanded)
%              Depth                    :   20
%              Number of atoms          :  123 ( 657 expanded)
%              Number of equality atoms :   73 ( 565 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f477,plain,(
    $false ),
    inference(global_subsumption,[],[f476,f465])).

fof(f465,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f452,f454,f86])).

fof(f86,plain,(
    ! [X1] :
      ( sP6(sK4(X1),X1)
      | ~ v1_relat_1(X1)
      | k1_xboole_0 = k1_relat_1(X1) ) ),
    inference(resolution,[],[f84,f37])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | sP6(sK4(X1),X1) ) ),
    inference(resolution,[],[f42,f71])).

fof(f71,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,k2_relat_1(X0))
      | sP6(X2,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP6(X2,X0)
      | ~ r2_hidden(X2,X1)
      | k2_relat_1(X0) != X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X1),k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ? [X2] : r2_hidden(X2,k2_relat_1(X1))
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ~ ( ! [X2] : ~ r2_hidden(X2,k2_relat_1(X1))
          & r2_hidden(X0,k1_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).

fof(f454,plain,(
    ! [X0] : ~ sP6(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f448,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(sK7(X0,X2),X2),X0)
      | ~ sP6(X2,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f448,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f132,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f49,f65])).

fof(f65,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f61])).

fof(f61,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f40,f60])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f54,f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f55,f57])).

fof(f57,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f132,plain,(
    ! [X0] : ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f107,f33])).

fof(f33,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f107,plain,(
    ! [X1] : k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) ),
    inference(forward_demodulation,[],[f105,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f105,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) ),
    inference(backward_demodulation,[],[f75,f104])).

fof(f104,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f97,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f97,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f88,f30])).

fof(f88,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f53,f30])).

fof(f53,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f75,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(forward_demodulation,[],[f74,f30])).

fof(f74,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) ),
    inference(forward_demodulation,[],[f73,f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f58,f62,f61,f56])).

fof(f56,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).

fof(f62,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f61])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f58,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).

fof(f73,plain,(
    ! [X1] : k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) ) ),
    inference(definition_unfolding,[],[f52,f65,f64,f65,f65])).

fof(f64,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f39,f63])).

fof(f63,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f41,f62])).

fof(f41,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( X0 != X1
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1))
    <=> X0 != X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

fof(f452,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f448,f35])).

fof(f35,plain,(
    ! [X0] :
      ( r2_hidden(sK0(X0),X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ( ? [X2,X3] : k4_tarski(X2,X3) = X1
          | ~ r2_hidden(X1,X0) ) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
    <=> ! [X1] :
          ~ ( ! [X2,X3] : k4_tarski(X2,X3) != X1
            & r2_hidden(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

fof(f476,plain,(
    k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(trivial_inequality_removal,[],[f475])).

fof(f475,plain,
    ( k1_xboole_0 != k1_xboole_0
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(backward_demodulation,[],[f29,f468])).

fof(f468,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f448,f454,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( sP6(sK5(X0,X1),X0)
      | r2_hidden(sK5(X0,X1),X1)
      | k2_relat_1(X0) = X1 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f29,plain,
    ( k1_xboole_0 != k1_relat_1(k1_xboole_0)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( k1_xboole_0 != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 != k1_relat_1(k1_xboole_0) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
      & k1_xboole_0 = k1_relat_1(k1_xboole_0) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.11  % Command    : run_vampire %s %d
% 0.10/0.31  % Computer   : n010.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % WCLimit    : 600
% 0.10/0.31  % DateTime   : Tue Dec  1 18:53:59 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.17/0.43  % (5918)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.17/0.44  % (5934)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.17/0.47  % (5910)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.17/0.48  % (5910)Refutation not found, incomplete strategy% (5910)------------------------------
% 0.17/0.48  % (5910)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.48  % (5910)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.48  
% 0.17/0.48  % (5910)Memory used [KB]: 6140
% 0.17/0.48  % (5910)Time elapsed: 0.111 s
% 0.17/0.48  % (5910)------------------------------
% 0.17/0.48  % (5910)------------------------------
% 0.17/0.48  % (5911)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.17/0.48  % (5920)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.17/0.48  % (5913)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.17/0.48  % (5907)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.17/0.48  % (5909)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.17/0.48  % (5908)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.17/0.48  % (5933)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.17/0.49  % (5917)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.17/0.49  % (5908)Refutation not found, incomplete strategy% (5908)------------------------------
% 0.17/0.49  % (5908)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.49  % (5908)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.49  
% 0.17/0.49  % (5908)Memory used [KB]: 10746
% 0.17/0.49  % (5908)Time elapsed: 0.116 s
% 0.17/0.49  % (5908)------------------------------
% 0.17/0.49  % (5908)------------------------------
% 0.17/0.49  % (5925)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.17/0.49  % (5928)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.17/0.49  % (5917)Refutation not found, incomplete strategy% (5917)------------------------------
% 0.17/0.49  % (5917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.49  % (5928)Refutation not found, incomplete strategy% (5928)------------------------------
% 0.17/0.49  % (5928)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.49  % (5928)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.49  
% 0.17/0.49  % (5928)Memory used [KB]: 10746
% 0.17/0.49  % (5928)Time elapsed: 0.087 s
% 0.17/0.49  % (5928)------------------------------
% 0.17/0.49  % (5928)------------------------------
% 0.17/0.49  % (5917)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.49  
% 0.17/0.49  % (5917)Memory used [KB]: 10618
% 0.17/0.49  % (5917)Time elapsed: 0.128 s
% 0.17/0.49  % (5917)------------------------------
% 0.17/0.49  % (5917)------------------------------
% 0.17/0.50  % (5906)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.17/0.50  % (5906)Refutation not found, incomplete strategy% (5906)------------------------------
% 0.17/0.50  % (5906)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.50  % (5906)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.50  
% 0.17/0.50  % (5906)Memory used [KB]: 1663
% 0.17/0.50  % (5906)Time elapsed: 0.127 s
% 0.17/0.50  % (5906)------------------------------
% 0.17/0.50  % (5906)------------------------------
% 0.17/0.50  % (5912)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.17/0.50  % (5931)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.17/0.50  % (5932)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.17/0.51  % (5923)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.17/0.51  % (5915)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.17/0.51  % (5935)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.17/0.51  % (5930)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.17/0.51  % (5923)Refutation not found, incomplete strategy% (5923)------------------------------
% 0.17/0.51  % (5923)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.51  % (5929)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.17/0.51  % (5923)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.51  
% 0.17/0.51  % (5923)Memory used [KB]: 10618
% 0.17/0.51  % (5923)Time elapsed: 0.140 s
% 0.17/0.51  % (5923)------------------------------
% 0.17/0.51  % (5923)------------------------------
% 0.17/0.51  % (5924)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.17/0.52  % (5922)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.17/0.52  % (5927)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.17/0.52  % (5921)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.17/0.52  % (5926)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.17/0.52  % (5927)Refutation not found, incomplete strategy% (5927)------------------------------
% 0.17/0.52  % (5927)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.52  % (5927)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.52  
% 0.17/0.52  % (5927)Memory used [KB]: 1791
% 0.17/0.52  % (5927)Time elapsed: 0.149 s
% 0.17/0.52  % (5927)------------------------------
% 0.17/0.52  % (5927)------------------------------
% 0.17/0.52  % (5916)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.17/0.52  % (5926)Refutation not found, incomplete strategy% (5926)------------------------------
% 0.17/0.52  % (5926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.52  % (5926)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.52  
% 0.17/0.52  % (5926)Memory used [KB]: 10746
% 0.17/0.52  % (5926)Time elapsed: 0.123 s
% 0.17/0.52  % (5926)------------------------------
% 0.17/0.52  % (5926)------------------------------
% 0.17/0.52  % (5919)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.17/0.52  % (5916)Refutation not found, incomplete strategy% (5916)------------------------------
% 0.17/0.52  % (5916)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.52  % (5916)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.52  
% 0.17/0.52  % (5916)Memory used [KB]: 10618
% 0.17/0.52  % (5916)Time elapsed: 0.149 s
% 0.17/0.52  % (5916)------------------------------
% 0.17/0.52  % (5916)------------------------------
% 0.17/0.52  % (5914)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.17/0.52  % (5914)Refutation not found, incomplete strategy% (5914)------------------------------
% 0.17/0.52  % (5914)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.52  % (5914)Termination reason: Refutation not found, incomplete strategy
% 0.17/0.52  
% 0.17/0.52  % (5914)Memory used [KB]: 10746
% 0.17/0.52  % (5914)Time elapsed: 0.151 s
% 0.17/0.52  % (5914)------------------------------
% 0.17/0.52  % (5914)------------------------------
% 0.17/0.54  % (5930)Refutation found. Thanks to Tanya!
% 0.17/0.54  % SZS status Theorem for theBenchmark
% 0.17/0.55  % SZS output start Proof for theBenchmark
% 0.17/0.55  fof(f477,plain,(
% 0.17/0.55    $false),
% 0.17/0.55    inference(global_subsumption,[],[f476,f465])).
% 0.17/0.55  fof(f465,plain,(
% 0.17/0.55    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.55    inference(unit_resulting_resolution,[],[f452,f454,f86])).
% 0.17/0.55  fof(f86,plain,(
% 0.17/0.55    ( ! [X1] : (sP6(sK4(X1),X1) | ~v1_relat_1(X1) | k1_xboole_0 = k1_relat_1(X1)) )),
% 0.17/0.55    inference(resolution,[],[f84,f37])).
% 0.17/0.55  fof(f37,plain,(
% 0.17/0.55    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.17/0.55    inference(cnf_transformation,[],[f26])).
% 0.17/0.55  fof(f26,plain,(
% 0.17/0.55    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.17/0.55    inference(ennf_transformation,[],[f1])).
% 0.17/0.55  fof(f1,axiom,(
% 0.17/0.55    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.17/0.55  fof(f84,plain,(
% 0.17/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1) | sP6(sK4(X1),X1)) )),
% 0.17/0.55    inference(resolution,[],[f42,f71])).
% 0.17/0.55  fof(f71,plain,(
% 0.17/0.55    ( ! [X2,X0] : (~r2_hidden(X2,k2_relat_1(X0)) | sP6(X2,X0)) )),
% 0.17/0.55    inference(equality_resolution,[],[f46])).
% 0.17/0.55  fof(f46,plain,(
% 0.17/0.55    ( ! [X2,X0,X1] : (sP6(X2,X0) | ~r2_hidden(X2,X1) | k2_relat_1(X0) != X1) )),
% 0.17/0.55    inference(cnf_transformation,[],[f19])).
% 0.17/0.55  fof(f19,axiom,(
% 0.17/0.55    ! [X0,X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : r2_hidden(k4_tarski(X3,X2),X0)))),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_relat_1)).
% 0.17/0.55  fof(f42,plain,(
% 0.17/0.55    ( ! [X0,X1] : (r2_hidden(sK4(X1),k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f28])).
% 0.17/0.55  fof(f28,plain,(
% 0.17/0.55    ! [X0,X1] : (? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.17/0.55    inference(flattening,[],[f27])).
% 0.17/0.55  fof(f27,plain,(
% 0.17/0.55    ! [X0,X1] : ((? [X2] : r2_hidden(X2,k2_relat_1(X1)) | ~r2_hidden(X0,k1_relat_1(X1))) | ~v1_relat_1(X1))),
% 0.17/0.55    inference(ennf_transformation,[],[f20])).
% 0.17/0.55  fof(f20,axiom,(
% 0.17/0.55    ! [X0,X1] : (v1_relat_1(X1) => ~(! [X2] : ~r2_hidden(X2,k2_relat_1(X1)) & r2_hidden(X0,k1_relat_1(X1))))),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_relat_1)).
% 0.17/0.55  fof(f454,plain,(
% 0.17/0.55    ( ! [X0] : (~sP6(X0,k1_xboole_0)) )),
% 0.17/0.55    inference(unit_resulting_resolution,[],[f448,f43])).
% 0.17/0.55  fof(f43,plain,(
% 0.17/0.55    ( ! [X2,X0] : (r2_hidden(k4_tarski(sK7(X0,X2),X2),X0) | ~sP6(X2,X0)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f19])).
% 0.17/0.55  fof(f448,plain,(
% 0.17/0.55    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.17/0.55    inference(unit_resulting_resolution,[],[f132,f68])).
% 0.17/0.55  fof(f68,plain,(
% 0.17/0.55    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.17/0.55    inference(definition_unfolding,[],[f49,f65])).
% 0.17/0.55  fof(f65,plain,(
% 0.17/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.17/0.55    inference(definition_unfolding,[],[f32,f61])).
% 0.17/0.55  fof(f61,plain,(
% 0.17/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.17/0.55    inference(definition_unfolding,[],[f40,f60])).
% 0.17/0.55  fof(f60,plain,(
% 0.17/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.17/0.55    inference(definition_unfolding,[],[f54,f59])).
% 0.17/0.55  fof(f59,plain,(
% 0.17/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.17/0.55    inference(definition_unfolding,[],[f55,f57])).
% 0.17/0.55  fof(f57,plain,(
% 0.17/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f11])).
% 0.17/0.55  fof(f11,axiom,(
% 0.17/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.17/0.55  fof(f55,plain,(
% 0.17/0.55    ( ! [X4,X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f13])).
% 0.17/0.55  fof(f13,axiom,(
% 0.17/0.55    ! [X0,X1,X2,X3,X4] : k5_enumset1(X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_enumset1)).
% 0.17/0.55  fof(f54,plain,(
% 0.17/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f10])).
% 0.17/0.55  fof(f10,axiom,(
% 0.17/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.17/0.55  fof(f40,plain,(
% 0.17/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f12])).
% 0.17/0.55  fof(f12,axiom,(
% 0.17/0.55    ! [X0,X1] : k2_tarski(X0,X1) = k2_enumset1(X0,X0,X0,X1)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_enumset1)).
% 0.17/0.55  fof(f32,plain,(
% 0.17/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f9])).
% 0.17/0.55  fof(f9,axiom,(
% 0.17/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.17/0.55  fof(f49,plain,(
% 0.17/0.55    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f17])).
% 0.17/0.55  fof(f17,axiom,(
% 0.17/0.55    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 0.17/0.55  fof(f132,plain,(
% 0.17/0.55    ( ! [X0] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_xboole_0)) )),
% 0.17/0.55    inference(unit_resulting_resolution,[],[f107,f33])).
% 0.17/0.55  fof(f33,plain,(
% 0.17/0.55    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.17/0.55    inference(cnf_transformation,[],[f24])).
% 0.17/0.55  fof(f24,plain,(
% 0.17/0.55    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.17/0.55    inference(ennf_transformation,[],[f3])).
% 0.17/0.55  fof(f3,axiom,(
% 0.17/0.55    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.17/0.55  fof(f107,plain,(
% 0.17/0.55    ( ! [X1] : (k1_xboole_0 != k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) )),
% 0.17/0.55    inference(forward_demodulation,[],[f105,f30])).
% 0.17/0.55  fof(f30,plain,(
% 0.17/0.55    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f6])).
% 0.17/0.55  fof(f6,axiom,(
% 0.17/0.55    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.17/0.55  fof(f105,plain,(
% 0.17/0.55    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) )),
% 0.17/0.55    inference(backward_demodulation,[],[f75,f104])).
% 0.17/0.55  fof(f104,plain,(
% 0.17/0.55    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.17/0.55    inference(forward_demodulation,[],[f97,f31])).
% 0.17/0.55  fof(f31,plain,(
% 0.17/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.17/0.55    inference(cnf_transformation,[],[f4])).
% 0.17/0.55  fof(f4,axiom,(
% 0.17/0.55    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.17/0.55  fof(f97,plain,(
% 0.17/0.55    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 0.17/0.55    inference(superposition,[],[f88,f30])).
% 0.17/0.55  fof(f88,plain,(
% 0.17/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 0.17/0.55    inference(superposition,[],[f53,f30])).
% 0.17/0.55  fof(f53,plain,(
% 0.17/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.17/0.55    inference(cnf_transformation,[],[f5])).
% 0.17/0.55  fof(f5,axiom,(
% 0.17/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.17/0.55  fof(f75,plain,(
% 0.17/0.55    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 0.17/0.55    inference(forward_demodulation,[],[f74,f30])).
% 0.17/0.55  fof(f74,plain,(
% 0.17/0.55    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) )),
% 0.17/0.55    inference(forward_demodulation,[],[f73,f66])).
% 0.17/0.55  fof(f66,plain,(
% 0.17/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X3,X4,X5,X6,X7)))) )),
% 0.17/0.55    inference(definition_unfolding,[],[f58,f62,f61,f56])).
% 0.17/0.55  fof(f56,plain,(
% 0.17/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f14])).
% 0.17/0.55  fof(f14,axiom,(
% 0.17/0.55    ! [X0,X1,X2,X3,X4,X5] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_enumset1)).
% 0.17/0.55  fof(f62,plain,(
% 0.17/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.17/0.55    inference(definition_unfolding,[],[f38,f61])).
% 0.17/0.55  fof(f38,plain,(
% 0.17/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.17/0.55    inference(cnf_transformation,[],[f15])).
% 0.17/0.55  fof(f15,axiom,(
% 0.17/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.17/0.55  fof(f58,plain,(
% 0.17/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))) )),
% 0.17/0.55    inference(cnf_transformation,[],[f8])).
% 0.17/0.55  fof(f8,axiom,(
% 0.17/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_tarski(X0,X1),k4_enumset1(X2,X3,X4,X5,X6,X7))),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_enumset1)).
% 0.17/0.55  fof(f73,plain,(
% 0.17/0.55    ( ! [X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k5_xboole_0(k5_xboole_0(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 0.17/0.55    inference(equality_resolution,[],[f69])).
% 0.17/0.55  fof(f69,plain,(
% 0.17/0.55    ( ! [X0,X1] : (X0 != X1 | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k5_xboole_0(k5_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)),k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))))) )),
% 0.17/0.55    inference(definition_unfolding,[],[f52,f65,f64,f65,f65])).
% 0.17/0.55  fof(f64,plain,(
% 0.17/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 0.17/0.55    inference(definition_unfolding,[],[f39,f63])).
% 0.17/0.55  fof(f63,plain,(
% 0.17/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.17/0.55    inference(definition_unfolding,[],[f41,f62])).
% 0.17/0.55  fof(f41,plain,(
% 0.17/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.17/0.55    inference(cnf_transformation,[],[f7])).
% 0.17/0.55  fof(f7,axiom,(
% 0.17/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.17/0.55  fof(f39,plain,(
% 0.17/0.55    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.17/0.55    inference(cnf_transformation,[],[f2])).
% 0.17/0.55  fof(f2,axiom,(
% 0.17/0.55    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.17/0.55  fof(f52,plain,(
% 0.17/0.55    ( ! [X0,X1] : (X0 != X1 | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),k1_tarski(X1))) )),
% 0.17/0.55    inference(cnf_transformation,[],[f16])).
% 0.17/0.55  fof(f16,axiom,(
% 0.17/0.55    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),k1_tarski(X1)) <=> X0 != X1)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).
% 0.17/0.55  fof(f452,plain,(
% 0.17/0.55    v1_relat_1(k1_xboole_0)),
% 0.17/0.55    inference(unit_resulting_resolution,[],[f448,f35])).
% 0.17/0.55  fof(f35,plain,(
% 0.17/0.55    ( ! [X0] : (r2_hidden(sK0(X0),X0) | v1_relat_1(X0)) )),
% 0.17/0.55    inference(cnf_transformation,[],[f25])).
% 0.17/0.55  fof(f25,plain,(
% 0.17/0.55    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : (? [X2,X3] : k4_tarski(X2,X3) = X1 | ~r2_hidden(X1,X0)))),
% 0.17/0.55    inference(ennf_transformation,[],[f18])).
% 0.17/0.55  fof(f18,axiom,(
% 0.17/0.55    ! [X0] : (v1_relat_1(X0) <=> ! [X1] : ~(! [X2,X3] : k4_tarski(X2,X3) != X1 & r2_hidden(X1,X0)))),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).
% 0.17/0.55  fof(f476,plain,(
% 0.17/0.55    k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.17/0.55    inference(trivial_inequality_removal,[],[f475])).
% 0.17/0.55  fof(f475,plain,(
% 0.17/0.55    k1_xboole_0 != k1_xboole_0 | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.17/0.55    inference(backward_demodulation,[],[f29,f468])).
% 0.17/0.55  fof(f468,plain,(
% 0.17/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.17/0.55    inference(unit_resulting_resolution,[],[f448,f454,f47])).
% 0.17/0.55  fof(f47,plain,(
% 0.17/0.55    ( ! [X0,X1] : (sP6(sK5(X0,X1),X0) | r2_hidden(sK5(X0,X1),X1) | k2_relat_1(X0) = X1) )),
% 0.17/0.55    inference(cnf_transformation,[],[f19])).
% 0.17/0.55  fof(f29,plain,(
% 0.17/0.55    k1_xboole_0 != k1_relat_1(k1_xboole_0) | k1_xboole_0 != k2_relat_1(k1_xboole_0)),
% 0.17/0.55    inference(cnf_transformation,[],[f23])).
% 0.17/0.55  fof(f23,plain,(
% 0.17/0.55    k1_xboole_0 != k2_relat_1(k1_xboole_0) | k1_xboole_0 != k1_relat_1(k1_xboole_0)),
% 0.17/0.55    inference(ennf_transformation,[],[f22])).
% 0.17/0.55  fof(f22,negated_conjecture,(
% 0.17/0.55    ~(k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0))),
% 0.17/0.55    inference(negated_conjecture,[],[f21])).
% 0.17/0.55  fof(f21,conjecture,(
% 0.17/0.55    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.17/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.17/0.55  % SZS output end Proof for theBenchmark
% 0.17/0.55  % (5930)------------------------------
% 0.17/0.55  % (5930)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.17/0.56  % (5930)Termination reason: Refutation
% 0.17/0.56  
% 0.17/0.56  % (5930)Memory used [KB]: 6780
% 0.17/0.56  % (5930)Time elapsed: 0.174 s
% 0.17/0.56  % (5930)------------------------------
% 0.17/0.56  % (5930)------------------------------
% 0.17/0.56  % (5905)Success in time 0.229 s
%------------------------------------------------------------------------------
