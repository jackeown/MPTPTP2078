%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:37 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 306 expanded)
%              Number of leaves         :   19 ( 100 expanded)
%              Depth                    :   15
%              Number of atoms          :  118 ( 367 expanded)
%              Number of equality atoms :   50 ( 263 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1380,plain,(
    $false ),
    inference(global_subsumption,[],[f97,f1379])).

fof(f1379,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f1378,f592])).

fof(f592,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f591,f454])).

fof(f454,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(unit_resulting_resolution,[],[f438,f30])).

fof(f30,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f438,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,X1)) ),
    inference(forward_demodulation,[],[f434,f28])).

fof(f28,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f434,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0))) ),
    inference(unit_resulting_resolution,[],[f431,f69])).

fof(f69,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | sP4(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2 ) ),
    inference(definition_unfolding,[],[f48,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( sP4(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f431,plain,(
    ! [X0,X1] : ~ sP4(X0,k1_xboole_0,X1) ),
    inference(unit_resulting_resolution,[],[f425,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ sP4(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f425,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f27,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f40,f56])).

fof(f56,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f29,f54])).

fof(f54,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f51,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).

fof(f29,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f591,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f566,f28])).

fof(f566,plain,(
    ! [X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0)) ),
    inference(superposition,[],[f76,f454])).

fof(f76,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(forward_demodulation,[],[f75,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f62,f59])).

fof(f59,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f55])).

fof(f55,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f54])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f62,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) ),
    inference(definition_unfolding,[],[f41,f55])).

fof(f41,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f75,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1))) ),
    inference(forward_demodulation,[],[f63,f59])).

fof(f63,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f42,f55,f33])).

fof(f42,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

fof(f1378,plain,(
    ~ r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k1_xboole_0) ),
    inference(forward_demodulation,[],[f1370,f74])).

fof(f1370,plain,(
    ~ r1_tarski(k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f1328,f90])).

fof(f90,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,k1_xboole_0)
      | k1_xboole_0 = X1 ) ),
    inference(superposition,[],[f37,f28])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f1328,plain,(
    k1_xboole_0 != k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f1324,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1324,plain,(
    ~ r1_tarski(sK1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))) ),
    inference(unit_resulting_resolution,[],[f1281,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f1281,plain,(
    ~ r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    inference(unit_resulting_resolution,[],[f73,f80,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1) ) ),
    inference(forward_demodulation,[],[f64,f59])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) ) ),
    inference(definition_unfolding,[],[f43,f55])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X2,X1)
      | r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f80,plain,(
    ! [X0,X1] : r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X1,X0)))) ),
    inference(unit_resulting_resolution,[],[f72,f36])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0))) ),
    inference(backward_demodulation,[],[f58,f59])).

fof(f58,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f31,f55])).

fof(f31,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f73,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    inference(forward_demodulation,[],[f71,f59])).

fof(f71,plain,(
    ~ r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))) ),
    inference(backward_demodulation,[],[f57,f59])).

fof(f57,plain,(
    ~ r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(definition_unfolding,[],[f26,f55,f55])).

fof(f26,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

fof(f97,plain,(
    r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(unit_resulting_resolution,[],[f28,f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (17645)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.50  % (17639)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.50  % (17641)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.50  % (17670)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.50  % (17646)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.50  % (17653)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.50  % (17649)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.50  % (17648)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.50  % (17648)Refutation not found, incomplete strategy% (17648)------------------------------
% 0.21/0.50  % (17648)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (17648)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (17648)Memory used [KB]: 10618
% 0.21/0.50  % (17648)Time elapsed: 0.103 s
% 0.21/0.50  % (17648)------------------------------
% 0.21/0.50  % (17648)------------------------------
% 0.21/0.51  % (17643)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.51  % (17655)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.51  % (17664)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.51  % (17662)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.51  % (17647)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.51  % (17664)Refutation not found, incomplete strategy% (17664)------------------------------
% 0.21/0.51  % (17664)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17642)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (17644)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (17639)Refutation not found, incomplete strategy% (17639)------------------------------
% 0.21/0.51  % (17639)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17656)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.52  % (17639)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17639)Memory used [KB]: 1663
% 0.21/0.52  % (17639)Time elapsed: 0.117 s
% 0.21/0.52  % (17639)------------------------------
% 0.21/0.52  % (17639)------------------------------
% 0.21/0.52  % (17664)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17664)Memory used [KB]: 1791
% 0.21/0.52  % (17664)Time elapsed: 0.079 s
% 0.21/0.52  % (17664)------------------------------
% 0.21/0.52  % (17664)------------------------------
% 0.21/0.52  % (17663)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (17654)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.52  % (17663)Refutation not found, incomplete strategy% (17663)------------------------------
% 0.21/0.52  % (17663)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17663)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17663)Memory used [KB]: 10746
% 0.21/0.52  % (17663)Time elapsed: 0.127 s
% 0.21/0.52  % (17663)------------------------------
% 0.21/0.52  % (17663)------------------------------
% 0.21/0.52  % (17642)Refutation not found, incomplete strategy% (17642)------------------------------
% 0.21/0.52  % (17642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17642)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17642)Memory used [KB]: 10618
% 0.21/0.52  % (17642)Time elapsed: 0.126 s
% 0.21/0.52  % (17642)------------------------------
% 0.21/0.52  % (17642)------------------------------
% 0.21/0.52  % (17662)Refutation not found, incomplete strategy% (17662)------------------------------
% 0.21/0.52  % (17662)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (17662)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (17662)Memory used [KB]: 1663
% 0.21/0.52  % (17662)Time elapsed: 0.133 s
% 0.21/0.52  % (17662)------------------------------
% 0.21/0.52  % (17662)------------------------------
% 0.21/0.52  % (17666)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.52  % (17657)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.53  % (17667)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.53  % (17657)Refutation not found, incomplete strategy% (17657)------------------------------
% 0.21/0.53  % (17657)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (17657)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (17657)Memory used [KB]: 10618
% 0.21/0.53  % (17657)Time elapsed: 0.131 s
% 0.21/0.53  % (17657)------------------------------
% 0.21/0.53  % (17657)------------------------------
% 0.21/0.53  % (17650)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (17665)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.53  % (17651)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (17668)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (17669)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.53  % (17659)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.54  % (17652)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (17660)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (17661)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.58  % (17665)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.60  % SZS output start Proof for theBenchmark
% 0.21/0.60  fof(f1380,plain,(
% 0.21/0.60    $false),
% 0.21/0.60    inference(global_subsumption,[],[f97,f1379])).
% 0.21/0.60  fof(f1379,plain,(
% 0.21/0.60    ~r1_tarski(k1_xboole_0,k1_xboole_0)),
% 0.21/0.60    inference(forward_demodulation,[],[f1378,f592])).
% 0.21/0.60  fof(f592,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X0,X1),X0)) )),
% 0.21/0.60    inference(forward_demodulation,[],[f591,f454])).
% 0.21/0.60  fof(f454,plain,(
% 0.21/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f438,f30])).
% 0.21/0.60  fof(f30,plain,(
% 0.21/0.60    ( ! [X0] : (r2_hidden(sK2(X0),X0) | k1_xboole_0 = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f22])).
% 0.21/0.60  fof(f22,plain,(
% 0.21/0.60    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.21/0.60    inference(ennf_transformation,[],[f2])).
% 0.21/0.60  fof(f2,axiom,(
% 0.21/0.60    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.21/0.60  fof(f438,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,X1))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f434,f28])).
% 0.21/0.60  fof(f28,plain,(
% 0.21/0.60    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f4])).
% 0.21/0.60  fof(f4,axiom,(
% 0.21/0.60    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.60  fof(f434,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k4_xboole_0(X1,k1_xboole_0)))) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f431,f69])).
% 0.21/0.60  fof(f69,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | sP4(X3,X1,X0)) )),
% 0.21/0.60    inference(equality_resolution,[],[f67])).
% 0.21/0.60  fof(f67,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) != X2) )),
% 0.21/0.60    inference(definition_unfolding,[],[f48,f33])).
% 0.21/0.60  fof(f33,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f6])).
% 0.21/0.60  fof(f6,axiom,(
% 0.21/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.60  fof(f48,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (sP4(X3,X1,X0) | ~r2_hidden(X3,X2) | k3_xboole_0(X0,X1) != X2) )),
% 0.21/0.60    inference(cnf_transformation,[],[f1])).
% 0.21/0.60  fof(f1,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : (k3_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).
% 0.21/0.60  fof(f431,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~sP4(X0,k1_xboole_0,X1)) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f425,f46])).
% 0.21/0.60  fof(f46,plain,(
% 0.21/0.60    ( ! [X0,X3,X1] : (~sP4(X3,X1,X0) | r2_hidden(X3,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f1])).
% 0.21/0.60  fof(f425,plain,(
% 0.21/0.60    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f27,f60])).
% 0.21/0.60  fof(f60,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f40,f56])).
% 0.21/0.60  fof(f56,plain,(
% 0.21/0.60    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f29,f54])).
% 0.21/0.60  fof(f54,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f35,f53])).
% 0.21/0.60  fof(f53,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.60    inference(definition_unfolding,[],[f51,f52])).
% 0.21/0.60  fof(f52,plain,(
% 0.21/0.60    ( ! [X4,X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f15])).
% 0.21/0.60  fof(f15,axiom,(
% 0.21/0.60    ! [X0,X1,X2,X3,X4] : k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_enumset1)).
% 0.21/0.60  fof(f51,plain,(
% 0.21/0.60    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f13])).
% 0.21/0.60  fof(f13,axiom,(
% 0.21/0.60    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.60  fof(f35,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f14])).
% 0.21/0.60  fof(f14,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_enumset1(X0,X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_enumset1)).
% 0.21/0.60  fof(f29,plain,(
% 0.21/0.60    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f12])).
% 0.21/0.60  fof(f12,axiom,(
% 0.21/0.60    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.60  fof(f40,plain,(
% 0.21/0.60    ( ! [X0,X1] : (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0) )),
% 0.21/0.60    inference(cnf_transformation,[],[f17])).
% 0.21/0.60  fof(f17,axiom,(
% 0.21/0.60    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 0.21/0.60  fof(f27,plain,(
% 0.21/0.60    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f7])).
% 0.21/0.60  fof(f7,axiom,(
% 0.21/0.60    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.60  fof(f591,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f566,f28])).
% 0.21/0.60  fof(f566,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X0) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k1_xboole_0))) )),
% 0.21/0.60    inference(superposition,[],[f76,f454])).
% 0.21/0.60  fof(f76,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f75,f74])).
% 0.21/0.60  fof(f74,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f62,f59])).
% 0.21/0.60  fof(f59,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X1,X0)) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f34,f55])).
% 0.21/0.60  fof(f55,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f32,f54])).
% 0.21/0.60  fof(f32,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f16])).
% 0.21/0.60  fof(f16,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.60  fof(f34,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f11])).
% 0.21/0.60  fof(f11,axiom,(
% 0.21/0.60    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.60  fof(f62,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f41,f55])).
% 0.21/0.60  fof(f41,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f5])).
% 0.21/0.60  fof(f5,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.60  fof(f75,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) )),
% 0.21/0.60    inference(forward_demodulation,[],[f63,f59])).
% 0.21/0.60  fof(f63,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) = k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 0.21/0.60    inference(definition_unfolding,[],[f42,f55,f33])).
% 0.21/0.60  fof(f42,plain,(
% 0.21/0.60    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 0.21/0.60    inference(cnf_transformation,[],[f8])).
% 0.21/0.60  fof(f8,axiom,(
% 0.21/0.60    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k3_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).
% 0.21/0.60  fof(f1378,plain,(
% 0.21/0.60    ~r1_tarski(k4_xboole_0(k4_xboole_0(sK1,sK0),sK1),k1_xboole_0)),
% 0.21/0.60    inference(forward_demodulation,[],[f1370,f74])).
% 0.21/0.60  fof(f1370,plain,(
% 0.21/0.60    ~r1_tarski(k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),k1_xboole_0)),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f1328,f90])).
% 0.21/0.60  fof(f90,plain,(
% 0.21/0.60    ( ! [X1] : (~r1_tarski(X1,k1_xboole_0) | k1_xboole_0 = X1) )),
% 0.21/0.60    inference(superposition,[],[f37,f28])).
% 0.21/0.60  fof(f37,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) | ~r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f3])).
% 0.21/0.60  fof(f3,axiom,(
% 0.21/0.60    ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,X1) <=> r1_tarski(X0,X1))),
% 0.21/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.60  fof(f1328,plain,(
% 0.21/0.60    k1_xboole_0 != k4_xboole_0(sK1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 0.21/0.60    inference(unit_resulting_resolution,[],[f1324,f38])).
% 0.21/0.60  fof(f38,plain,(
% 0.21/0.60    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.21/0.60    inference(cnf_transformation,[],[f3])).
% 1.89/0.60  fof(f1324,plain,(
% 1.89/0.60    ~r1_tarski(sK1,k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)))),
% 1.89/0.60    inference(unit_resulting_resolution,[],[f1281,f36])).
% 1.89/0.60  fof(f36,plain,(
% 1.89/0.60    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.89/0.60    inference(cnf_transformation,[],[f23])).
% 1.89/0.60  fof(f23,plain,(
% 1.89/0.60    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.89/0.60    inference(ennf_transformation,[],[f18])).
% 1.89/0.60  fof(f18,axiom,(
% 1.89/0.60    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.89/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.89/0.60  fof(f1281,plain,(
% 1.89/0.60    ~r1_tarski(k1_zfmisc_1(sK1),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 1.89/0.60    inference(unit_resulting_resolution,[],[f73,f80,f77])).
% 1.89/0.60  fof(f77,plain,(
% 1.89/0.60    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k4_xboole_0(X2,X0)),X1) | ~r1_tarski(X0,X1) | ~r1_tarski(X2,X1)) )),
% 1.89/0.60    inference(forward_demodulation,[],[f64,f59])).
% 1.89/0.60  fof(f64,plain,(
% 1.89/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)) )),
% 1.89/0.60    inference(definition_unfolding,[],[f43,f55])).
% 1.89/0.60  fof(f43,plain,(
% 1.89/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X2,X1) | r1_tarski(k2_xboole_0(X0,X2),X1)) )),
% 1.89/0.60    inference(cnf_transformation,[],[f25])).
% 1.89/0.60  fof(f25,plain,(
% 1.89/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.89/0.60    inference(flattening,[],[f24])).
% 1.89/0.60  fof(f24,plain,(
% 1.89/0.60    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.89/0.60    inference(ennf_transformation,[],[f10])).
% 1.89/0.60  fof(f10,axiom,(
% 1.89/0.60    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 1.89/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 1.89/0.60  fof(f80,plain,(
% 1.89/0.60    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(k5_xboole_0(X0,k4_xboole_0(X1,X0))))) )),
% 1.89/0.60    inference(unit_resulting_resolution,[],[f72,f36])).
% 1.89/0.60  fof(f72,plain,(
% 1.89/0.60    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k4_xboole_0(X1,X0)))) )),
% 1.89/0.60    inference(backward_demodulation,[],[f58,f59])).
% 1.89/0.60  fof(f58,plain,(
% 1.89/0.60    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.89/0.60    inference(definition_unfolding,[],[f31,f55])).
% 1.89/0.60  fof(f31,plain,(
% 1.89/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.89/0.60    inference(cnf_transformation,[],[f9])).
% 1.89/0.60  fof(f9,axiom,(
% 1.89/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.89/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.89/0.60  fof(f73,plain,(
% 1.89/0.60    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(sK0),k4_xboole_0(k1_zfmisc_1(sK1),k1_zfmisc_1(sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 1.89/0.60    inference(forward_demodulation,[],[f71,f59])).
% 1.89/0.60  fof(f71,plain,(
% 1.89/0.60    ~r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))))),
% 1.89/0.60    inference(backward_demodulation,[],[f57,f59])).
% 1.89/0.60  fof(f57,plain,(
% 1.89/0.60    ~r1_tarski(k3_tarski(k6_enumset1(k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK0),k1_zfmisc_1(sK1))),k1_zfmisc_1(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.89/0.60    inference(definition_unfolding,[],[f26,f55,f55])).
% 1.89/0.60  fof(f26,plain,(
% 1.89/0.60    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(sK0),k1_zfmisc_1(sK1)),k1_zfmisc_1(k2_xboole_0(sK0,sK1)))),
% 1.89/0.60    inference(cnf_transformation,[],[f21])).
% 1.89/0.60  fof(f21,plain,(
% 1.89/0.60    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 1.89/0.60    inference(ennf_transformation,[],[f20])).
% 1.89/0.60  fof(f20,negated_conjecture,(
% 1.89/0.60    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 1.89/0.60    inference(negated_conjecture,[],[f19])).
% 1.89/0.60  fof(f19,conjecture,(
% 1.89/0.60    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(X0),k1_zfmisc_1(X1)),k1_zfmisc_1(k2_xboole_0(X0,X1)))),
% 1.89/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).
% 1.89/0.60  fof(f97,plain,(
% 1.89/0.60    r1_tarski(k1_xboole_0,k1_xboole_0)),
% 1.89/0.60    inference(unit_resulting_resolution,[],[f28,f38])).
% 1.89/0.60  % SZS output end Proof for theBenchmark
% 1.89/0.60  % (17665)------------------------------
% 1.89/0.60  % (17665)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.89/0.60  % (17665)Termination reason: Refutation
% 1.89/0.60  
% 1.89/0.60  % (17665)Memory used [KB]: 7419
% 1.89/0.60  % (17665)Time elapsed: 0.172 s
% 1.89/0.61  % (17665)------------------------------
% 1.89/0.61  % (17665)------------------------------
% 1.89/0.61  % (17635)Success in time 0.26 s
%------------------------------------------------------------------------------
