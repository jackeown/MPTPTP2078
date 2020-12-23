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
% DateTime   : Thu Dec  3 12:38:14 EST 2020

% Result     : Theorem 2.70s
% Output     : Refutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :  113 (1481 expanded)
%              Number of leaves         :   21 ( 470 expanded)
%              Depth                    :   30
%              Number of atoms          :  180 (2038 expanded)
%              Number of equality atoms :  101 (1554 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1282,plain,(
    $false ),
    inference(global_subsumption,[],[f27,f1281])).

fof(f1281,plain,(
    sK1 = sK2 ),
    inference(forward_demodulation,[],[f1277,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f1277,plain,(
    sK2 = k5_xboole_0(sK1,k1_xboole_0) ),
    inference(superposition,[],[f551,f1012])).

fof(f1012,plain,(
    k1_xboole_0 = k5_xboole_0(sK2,sK1) ),
    inference(global_subsumption,[],[f29,f1011])).

fof(f1011,plain,
    ( k1_xboole_0 = sK2
    | k1_xboole_0 = k5_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f1000,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f1000,plain,
    ( sK2 = k5_xboole_0(sK1,sK1)
    | k1_xboole_0 = k5_xboole_0(sK2,sK1) ),
    inference(superposition,[],[f551,f612])).

fof(f612,plain,
    ( sK1 = k5_xboole_0(sK2,sK1)
    | k1_xboole_0 = k5_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f603,f472])).

fof(f472,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK2,sK1))
    | sK1 = k5_xboole_0(sK2,sK1) ),
    inference(forward_demodulation,[],[f469,f447])).

fof(f447,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f439,f31])).

fof(f439,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0) ),
    inference(superposition,[],[f134,f30])).

fof(f134,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f49,f30])).

fof(f49,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f469,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(sK2,sK1))
    | sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1)) ),
    inference(backward_demodulation,[],[f398,f447])).

fof(f398,plain,
    ( sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1))
    | ~ r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1))) ),
    inference(forward_demodulation,[],[f397,f382])).

fof(f382,plain,(
    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f169,f231,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f231,plain,(
    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(backward_demodulation,[],[f174,f222])).

fof(f222,plain,(
    sK0 = sK3(sK1) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,
    ( sK0 = sK3(sK1)
    | sK0 = sK3(sK1) ),
    inference(resolution,[],[f212,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | X1 = X3
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f212,plain,(
    sP6(sK3(sK1),sK0,sK0) ),
    inference(unit_resulting_resolution,[],[f189,f81])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2 ) ),
    inference(definition_unfolding,[],[f54,f65])).

fof(f65,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f37,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f48,f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f57,f62])).

fof(f62,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f58,f61])).

fof(f61,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f59,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f59,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f58,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f37,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f11])).

fof(f189,plain,(
    r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(unit_resulting_resolution,[],[f79,f79,f169,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(sK1),X2)
      | ~ r1_tarski(X0,X1)
      | ~ r1_tarski(sK1,X0)
      | ~ r1_tarski(X1,X2) ) ),
    inference(resolution,[],[f99,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | r2_hidden(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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

fof(f99,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(sK1),X1)
      | ~ r1_tarski(sK1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(resolution,[],[f96,f43])).

fof(f96,plain,(
    ! [X5] :
      ( r2_hidden(sK3(sK1),X5)
      | ~ r1_tarski(sK1,X5) ) ),
    inference(resolution,[],[f43,f86])).

fof(f86,plain,(
    r2_hidden(sK3(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f28,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & X1 != X2
      & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & X1 != X2
          & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & X1 != X2
        & k1_tarski(X0) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

fof(f79,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f174,plain,(
    r1_tarski(k6_enumset1(sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f86,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f46,f69])).

fof(f69,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f65])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f169,plain,(
    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f71,f70])).

fof(f70,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    inference(definition_unfolding,[],[f26,f69,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f36,f65])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f26,plain,(
    k1_tarski(sK0) = k2_xboole_0(sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f34,f66])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f397,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1)))
    | sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f363,f382])).

fof(f363,plain,
    ( ~ r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))
    | sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(resolution,[],[f276,f42])).

fof(f276,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(superposition,[],[f141,f70])).

fof(f141,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(backward_demodulation,[],[f85,f134])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X0) ),
    inference(backward_demodulation,[],[f72,f49])).

fof(f72,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(definition_unfolding,[],[f35,f68])).

fof(f68,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f38,f67])).

fof(f67,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f66])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f603,plain,
    ( r1_tarski(sK1,k5_xboole_0(sK2,sK1))
    | k1_xboole_0 = k5_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f600,f412])).

fof(f412,plain,(
    ! [X4] :
      ( ~ r2_hidden(sK0,X4)
      | r1_tarski(sK1,X4) ) ),
    inference(superposition,[],[f74,f382])).

fof(f600,plain,
    ( r2_hidden(sK0,k5_xboole_0(sK2,sK1))
    | k1_xboole_0 = k5_xboole_0(sK2,sK1) ),
    inference(resolution,[],[f596,f470])).

fof(f470,plain,(
    r1_tarski(k5_xboole_0(sK2,sK1),sK1) ),
    inference(backward_demodulation,[],[f394,f447])).

fof(f394,plain,(
    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1)),sK1) ),
    inference(backward_demodulation,[],[f276,f382])).

fof(f596,plain,(
    ! [X2] :
      ( ~ r1_tarski(X2,sK1)
      | k1_xboole_0 = X2
      | r2_hidden(sK0,X2) ) ),
    inference(duplicate_literal_removal,[],[f592])).

fof(f592,plain,(
    ! [X2] :
      ( r2_hidden(sK0,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X2
      | ~ r1_tarski(X2,sK1) ) ),
    inference(superposition,[],[f33,f584])).

fof(f584,plain,(
    ! [X6] :
      ( sK0 = sK3(X6)
      | k1_xboole_0 = X6
      | ~ r1_tarski(X6,sK1) ) ),
    inference(resolution,[],[f94,f425])).

fof(f425,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | sK0 = X1 ) ),
    inference(duplicate_literal_removal,[],[f424])).

fof(f424,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | sK0 = X1
      | sK0 = X1 ) ),
    inference(resolution,[],[f410,f52])).

fof(f410,plain,(
    ! [X3] :
      ( sP6(X3,sK0,sK0)
      | ~ r2_hidden(X3,sK1) ) ),
    inference(superposition,[],[f81,f382])).

fof(f94,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0),X1)
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f43,f33])).

fof(f29,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f23])).

fof(f551,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    inference(forward_demodulation,[],[f540,f31])).

fof(f540,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f448,f137])).

fof(f137,plain,(
    ! [X4,X3] : k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4))) ),
    inference(superposition,[],[f49,f30])).

fof(f448,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(backward_demodulation,[],[f134,f447])).

fof(f27,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:31:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.21/0.52  % (9101)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (9111)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.53  % (9118)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % (9109)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.53  % (9095)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (9101)Refutation not found, incomplete strategy% (9101)------------------------------
% 0.21/0.53  % (9101)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (9094)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.53  % (9103)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (9117)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.54  % (9101)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (9101)Memory used [KB]: 10618
% 0.21/0.54  % (9101)Time elapsed: 0.114 s
% 0.21/0.54  % (9101)------------------------------
% 0.21/0.54  % (9101)------------------------------
% 0.21/0.54  % (9110)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.38/0.55  % (9119)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.55  % (9113)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.38/0.55  % (9102)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.38/0.55  % (9102)Refutation not found, incomplete strategy% (9102)------------------------------
% 1.38/0.55  % (9102)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (9102)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (9102)Memory used [KB]: 10618
% 1.38/0.55  % (9102)Time elapsed: 0.156 s
% 1.38/0.55  % (9102)------------------------------
% 1.38/0.55  % (9102)------------------------------
% 1.38/0.56  % (9096)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.38/0.56  % (9097)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.38/0.56  % (9112)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.38/0.56  % (9105)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.38/0.57  % (9106)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.38/0.57  % (9098)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.38/0.57  % (9104)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.38/0.57  % (9108)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.63/0.57  % (9091)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.63/0.57  % (9114)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.63/0.57  % (9100)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.63/0.58  % (9099)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.63/0.58  % (9120)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.63/0.58  % (9099)Refutation not found, incomplete strategy% (9099)------------------------------
% 1.63/0.58  % (9099)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (9099)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (9099)Memory used [KB]: 10746
% 1.63/0.58  % (9099)Time elapsed: 0.171 s
% 1.63/0.58  % (9099)------------------------------
% 1.63/0.58  % (9099)------------------------------
% 1.63/0.58  % (9093)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.63/0.58  % (9093)Refutation not found, incomplete strategy% (9093)------------------------------
% 1.63/0.58  % (9093)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (9093)Termination reason: Refutation not found, incomplete strategy
% 1.63/0.58  
% 1.63/0.58  % (9093)Memory used [KB]: 10746
% 1.63/0.58  % (9093)Time elapsed: 0.164 s
% 1.63/0.58  % (9093)------------------------------
% 1.63/0.58  % (9093)------------------------------
% 1.63/0.59  % (9092)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.63/0.59  % (9115)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.63/0.60  % (9107)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.63/0.60  % (9116)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 2.18/0.67  % (9139)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 2.18/0.67  % (9140)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 2.70/0.73  % (9141)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.70/0.73  % (9115)Refutation found. Thanks to Tanya!
% 2.70/0.73  % SZS status Theorem for theBenchmark
% 2.70/0.73  % SZS output start Proof for theBenchmark
% 2.70/0.73  fof(f1282,plain,(
% 2.70/0.73    $false),
% 2.70/0.73    inference(global_subsumption,[],[f27,f1281])).
% 2.70/0.73  fof(f1281,plain,(
% 2.70/0.73    sK1 = sK2),
% 2.70/0.73    inference(forward_demodulation,[],[f1277,f31])).
% 2.70/0.73  fof(f31,plain,(
% 2.70/0.73    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.70/0.73    inference(cnf_transformation,[],[f6])).
% 2.70/0.73  fof(f6,axiom,(
% 2.70/0.73    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 2.70/0.73  fof(f1277,plain,(
% 2.70/0.73    sK2 = k5_xboole_0(sK1,k1_xboole_0)),
% 2.70/0.73    inference(superposition,[],[f551,f1012])).
% 2.70/0.73  fof(f1012,plain,(
% 2.70/0.73    k1_xboole_0 = k5_xboole_0(sK2,sK1)),
% 2.70/0.73    inference(global_subsumption,[],[f29,f1011])).
% 2.70/0.73  fof(f1011,plain,(
% 2.70/0.73    k1_xboole_0 = sK2 | k1_xboole_0 = k5_xboole_0(sK2,sK1)),
% 2.70/0.73    inference(forward_demodulation,[],[f1000,f30])).
% 2.70/0.73  fof(f30,plain,(
% 2.70/0.73    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f9])).
% 2.70/0.73  fof(f9,axiom,(
% 2.70/0.73    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.70/0.73  fof(f1000,plain,(
% 2.70/0.73    sK2 = k5_xboole_0(sK1,sK1) | k1_xboole_0 = k5_xboole_0(sK2,sK1)),
% 2.70/0.73    inference(superposition,[],[f551,f612])).
% 2.70/0.73  fof(f612,plain,(
% 2.70/0.73    sK1 = k5_xboole_0(sK2,sK1) | k1_xboole_0 = k5_xboole_0(sK2,sK1)),
% 2.70/0.73    inference(resolution,[],[f603,f472])).
% 2.70/0.73  fof(f472,plain,(
% 2.70/0.73    ~r1_tarski(sK1,k5_xboole_0(sK2,sK1)) | sK1 = k5_xboole_0(sK2,sK1)),
% 2.70/0.73    inference(forward_demodulation,[],[f469,f447])).
% 2.70/0.73  fof(f447,plain,(
% 2.70/0.73    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.70/0.73    inference(forward_demodulation,[],[f439,f31])).
% 2.70/0.73  fof(f439,plain,(
% 2.70/0.73    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = k5_xboole_0(k1_xboole_0,X0)) )),
% 2.70/0.73    inference(superposition,[],[f134,f30])).
% 2.70/0.73  fof(f134,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.70/0.73    inference(superposition,[],[f49,f30])).
% 2.70/0.73  fof(f49,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f8])).
% 2.70/0.73  fof(f8,axiom,(
% 2.70/0.73    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.70/0.73  fof(f469,plain,(
% 2.70/0.73    ~r1_tarski(sK1,k5_xboole_0(sK2,sK1)) | sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1))),
% 2.70/0.73    inference(backward_demodulation,[],[f398,f447])).
% 2.70/0.73  fof(f398,plain,(
% 2.70/0.73    sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1)) | ~r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1)))),
% 2.70/0.73    inference(forward_demodulation,[],[f397,f382])).
% 2.70/0.73  fof(f382,plain,(
% 2.70/0.73    sK1 = k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f169,f231,f42])).
% 2.70/0.73  fof(f42,plain,(
% 2.70/0.73    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.70/0.73    inference(cnf_transformation,[],[f3])).
% 2.70/0.73  fof(f3,axiom,(
% 2.70/0.73    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.70/0.73  fof(f231,plain,(
% 2.70/0.73    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 2.70/0.73    inference(backward_demodulation,[],[f174,f222])).
% 2.70/0.73  fof(f222,plain,(
% 2.70/0.73    sK0 = sK3(sK1)),
% 2.70/0.73    inference(duplicate_literal_removal,[],[f221])).
% 2.70/0.73  fof(f221,plain,(
% 2.70/0.73    sK0 = sK3(sK1) | sK0 = sK3(sK1)),
% 2.70/0.73    inference(resolution,[],[f212,f52])).
% 2.70/0.73  fof(f52,plain,(
% 2.70/0.73    ( ! [X0,X3,X1] : (~sP6(X3,X1,X0) | X1 = X3 | X0 = X3) )),
% 2.70/0.73    inference(cnf_transformation,[],[f11])).
% 2.70/0.73  fof(f11,axiom,(
% 2.70/0.73    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 2.70/0.73  fof(f212,plain,(
% 2.70/0.73    sP6(sK3(sK1),sK0,sK0)),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f189,f81])).
% 2.70/0.73  fof(f81,plain,(
% 2.70/0.73    ( ! [X0,X3,X1] : (~r2_hidden(X3,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) | sP6(X3,X1,X0)) )),
% 2.70/0.73    inference(equality_resolution,[],[f77])).
% 2.70/0.73  fof(f77,plain,(
% 2.70/0.73    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) != X2) )),
% 2.70/0.73    inference(definition_unfolding,[],[f54,f65])).
% 2.70/0.73  fof(f65,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f37,f64])).
% 2.70/0.73  fof(f64,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f48,f63])).
% 2.70/0.73  fof(f63,plain,(
% 2.70/0.73    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f57,f62])).
% 2.70/0.73  fof(f62,plain,(
% 2.70/0.73    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f58,f61])).
% 2.70/0.73  fof(f61,plain,(
% 2.70/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f59,f60])).
% 2.70/0.73  fof(f60,plain,(
% 2.70/0.73    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f18])).
% 2.70/0.73  fof(f18,axiom,(
% 2.70/0.73    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 2.70/0.73  fof(f59,plain,(
% 2.70/0.73    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f17])).
% 2.70/0.73  fof(f17,axiom,(
% 2.70/0.73    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 2.70/0.73  fof(f58,plain,(
% 2.70/0.73    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f16])).
% 2.70/0.73  fof(f16,axiom,(
% 2.70/0.73    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 2.70/0.73  fof(f57,plain,(
% 2.70/0.73    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f15])).
% 2.70/0.73  fof(f15,axiom,(
% 2.70/0.73    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 2.70/0.73  fof(f48,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f14])).
% 2.70/0.73  fof(f14,axiom,(
% 2.70/0.73    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 2.70/0.73  fof(f37,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f13])).
% 2.70/0.73  fof(f13,axiom,(
% 2.70/0.73    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.70/0.73  fof(f54,plain,(
% 2.70/0.73    ( ! [X2,X0,X3,X1] : (sP6(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_tarski(X0,X1) != X2) )),
% 2.70/0.73    inference(cnf_transformation,[],[f11])).
% 2.70/0.73  fof(f189,plain,(
% 2.70/0.73    r2_hidden(sK3(sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f79,f79,f169,f103])).
% 2.70/0.73  fof(f103,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (r2_hidden(sK3(sK1),X2) | ~r1_tarski(X0,X1) | ~r1_tarski(sK1,X0) | ~r1_tarski(X1,X2)) )),
% 2.70/0.73    inference(resolution,[],[f99,f43])).
% 2.70/0.73  fof(f43,plain,(
% 2.70/0.73    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | r2_hidden(X2,X1) | ~r1_tarski(X0,X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f25])).
% 2.70/0.73  fof(f25,plain,(
% 2.70/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.70/0.73    inference(ennf_transformation,[],[f1])).
% 2.70/0.73  fof(f1,axiom,(
% 2.70/0.73    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 2.70/0.73  fof(f99,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r2_hidden(sK3(sK1),X1) | ~r1_tarski(sK1,X0) | ~r1_tarski(X0,X1)) )),
% 2.70/0.73    inference(resolution,[],[f96,f43])).
% 2.70/0.73  fof(f96,plain,(
% 2.70/0.73    ( ! [X5] : (r2_hidden(sK3(sK1),X5) | ~r1_tarski(sK1,X5)) )),
% 2.70/0.73    inference(resolution,[],[f43,f86])).
% 2.70/0.73  fof(f86,plain,(
% 2.70/0.73    r2_hidden(sK3(sK1),sK1)),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f28,f33])).
% 2.70/0.73  fof(f33,plain,(
% 2.70/0.73    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 2.70/0.73    inference(cnf_transformation,[],[f24])).
% 2.70/0.73  fof(f24,plain,(
% 2.70/0.73    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 2.70/0.73    inference(ennf_transformation,[],[f2])).
% 2.70/0.73  fof(f2,axiom,(
% 2.70/0.73    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 2.70/0.73  fof(f28,plain,(
% 2.70/0.73    k1_xboole_0 != sK1),
% 2.70/0.73    inference(cnf_transformation,[],[f23])).
% 2.70/0.73  fof(f23,plain,(
% 2.70/0.73    ? [X0,X1,X2] : (k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.70/0.73    inference(ennf_transformation,[],[f22])).
% 2.70/0.73  fof(f22,negated_conjecture,(
% 2.70/0.73    ~! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.70/0.73    inference(negated_conjecture,[],[f21])).
% 2.70/0.73  fof(f21,conjecture,(
% 2.70/0.73    ! [X0,X1,X2] : ~(k1_xboole_0 != X2 & k1_xboole_0 != X1 & X1 != X2 & k1_tarski(X0) = k2_xboole_0(X1,X2))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).
% 2.70/0.73  fof(f79,plain,(
% 2.70/0.73    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.70/0.73    inference(equality_resolution,[],[f41])).
% 2.70/0.73  fof(f41,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.70/0.73    inference(cnf_transformation,[],[f3])).
% 2.70/0.73  fof(f174,plain,(
% 2.70/0.73    r1_tarski(k6_enumset1(sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1),sK3(sK1)),sK1)),
% 2.70/0.73    inference(unit_resulting_resolution,[],[f86,f74])).
% 2.70/0.73  fof(f74,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f46,f69])).
% 2.70/0.73  fof(f69,plain,(
% 2.70/0.73    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f32,f65])).
% 2.70/0.73  fof(f32,plain,(
% 2.70/0.73    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f12])).
% 2.70/0.73  fof(f12,axiom,(
% 2.70/0.73    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.70/0.73  fof(f46,plain,(
% 2.70/0.73    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f19])).
% 2.70/0.73  fof(f19,axiom,(
% 2.70/0.73    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 2.70/0.73  fof(f169,plain,(
% 2.70/0.73    r1_tarski(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 2.70/0.73    inference(superposition,[],[f71,f70])).
% 2.70/0.73  fof(f70,plain,(
% 2.70/0.73    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.70/0.73    inference(definition_unfolding,[],[f26,f69,f66])).
% 2.70/0.73  fof(f66,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.70/0.73    inference(definition_unfolding,[],[f36,f65])).
% 2.70/0.73  fof(f36,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f20])).
% 2.70/0.73  fof(f20,axiom,(
% 2.70/0.73    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.70/0.73  fof(f26,plain,(
% 2.70/0.73    k1_tarski(sK0) = k2_xboole_0(sK1,sK2)),
% 2.70/0.73    inference(cnf_transformation,[],[f23])).
% 2.70/0.73  fof(f71,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.70/0.73    inference(definition_unfolding,[],[f34,f66])).
% 2.70/0.73  fof(f34,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f7])).
% 2.70/0.73  fof(f7,axiom,(
% 2.70/0.73    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.70/0.73  fof(f397,plain,(
% 2.70/0.73    ~r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1))) | sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.70/0.73    inference(backward_demodulation,[],[f363,f382])).
% 2.70/0.73  fof(f363,plain,(
% 2.70/0.73    ~r1_tarski(sK1,k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) | sK1 = k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 2.70/0.73    inference(resolution,[],[f276,f42])).
% 2.70/0.73  fof(f276,plain,(
% 2.70/0.73    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.70/0.73    inference(superposition,[],[f141,f70])).
% 2.70/0.73  fof(f141,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 2.70/0.73    inference(backward_demodulation,[],[f85,f134])).
% 2.70/0.73  fof(f85,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))),X0)) )),
% 2.70/0.73    inference(backward_demodulation,[],[f72,f49])).
% 2.70/0.73  fof(f72,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 2.70/0.73    inference(definition_unfolding,[],[f35,f68])).
% 2.70/0.73  fof(f68,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.70/0.73    inference(definition_unfolding,[],[f38,f67])).
% 2.70/0.73  fof(f67,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.70/0.73    inference(definition_unfolding,[],[f39,f66])).
% 2.70/0.73  fof(f39,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f10])).
% 2.70/0.73  fof(f10,axiom,(
% 2.70/0.73    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.70/0.73  fof(f38,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.70/0.73    inference(cnf_transformation,[],[f4])).
% 2.70/0.73  fof(f4,axiom,(
% 2.70/0.73    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.70/0.73  fof(f35,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.70/0.73    inference(cnf_transformation,[],[f5])).
% 2.70/0.73  fof(f5,axiom,(
% 2.70/0.73    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.70/0.73    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.70/0.73  fof(f603,plain,(
% 2.70/0.73    r1_tarski(sK1,k5_xboole_0(sK2,sK1)) | k1_xboole_0 = k5_xboole_0(sK2,sK1)),
% 2.70/0.73    inference(resolution,[],[f600,f412])).
% 2.70/0.73  fof(f412,plain,(
% 2.70/0.73    ( ! [X4] : (~r2_hidden(sK0,X4) | r1_tarski(sK1,X4)) )),
% 2.70/0.73    inference(superposition,[],[f74,f382])).
% 2.70/0.73  fof(f600,plain,(
% 2.70/0.73    r2_hidden(sK0,k5_xboole_0(sK2,sK1)) | k1_xboole_0 = k5_xboole_0(sK2,sK1)),
% 2.70/0.73    inference(resolution,[],[f596,f470])).
% 2.70/0.73  fof(f470,plain,(
% 2.70/0.73    r1_tarski(k5_xboole_0(sK2,sK1),sK1)),
% 2.70/0.73    inference(backward_demodulation,[],[f394,f447])).
% 2.70/0.73  fof(f394,plain,(
% 2.70/0.73    r1_tarski(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK2,sK1)),sK1)),
% 2.70/0.73    inference(backward_demodulation,[],[f276,f382])).
% 2.70/0.73  fof(f596,plain,(
% 2.70/0.73    ( ! [X2] : (~r1_tarski(X2,sK1) | k1_xboole_0 = X2 | r2_hidden(sK0,X2)) )),
% 2.70/0.73    inference(duplicate_literal_removal,[],[f592])).
% 2.70/0.73  fof(f592,plain,(
% 2.70/0.73    ( ! [X2] : (r2_hidden(sK0,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X2 | ~r1_tarski(X2,sK1)) )),
% 2.70/0.73    inference(superposition,[],[f33,f584])).
% 2.70/0.73  fof(f584,plain,(
% 2.70/0.73    ( ! [X6] : (sK0 = sK3(X6) | k1_xboole_0 = X6 | ~r1_tarski(X6,sK1)) )),
% 2.70/0.73    inference(resolution,[],[f94,f425])).
% 2.70/0.73  fof(f425,plain,(
% 2.70/0.73    ( ! [X1] : (~r2_hidden(X1,sK1) | sK0 = X1) )),
% 2.70/0.73    inference(duplicate_literal_removal,[],[f424])).
% 2.70/0.73  fof(f424,plain,(
% 2.70/0.73    ( ! [X1] : (~r2_hidden(X1,sK1) | sK0 = X1 | sK0 = X1) )),
% 2.70/0.73    inference(resolution,[],[f410,f52])).
% 2.70/0.73  fof(f410,plain,(
% 2.70/0.73    ( ! [X3] : (sP6(X3,sK0,sK0) | ~r2_hidden(X3,sK1)) )),
% 2.70/0.73    inference(superposition,[],[f81,f382])).
% 2.70/0.73  fof(f94,plain,(
% 2.70/0.73    ( ! [X0,X1] : (r2_hidden(sK3(X0),X1) | ~r1_tarski(X0,X1) | k1_xboole_0 = X0) )),
% 2.70/0.73    inference(resolution,[],[f43,f33])).
% 2.70/0.73  fof(f29,plain,(
% 2.70/0.73    k1_xboole_0 != sK2),
% 2.70/0.73    inference(cnf_transformation,[],[f23])).
% 2.70/0.73  fof(f551,plain,(
% 2.70/0.73    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) )),
% 2.70/0.73    inference(forward_demodulation,[],[f540,f31])).
% 2.70/0.73  fof(f540,plain,(
% 2.70/0.73    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) )),
% 2.70/0.73    inference(superposition,[],[f448,f137])).
% 2.70/0.73  fof(f137,plain,(
% 2.70/0.73    ( ! [X4,X3] : (k1_xboole_0 = k5_xboole_0(X3,k5_xboole_0(X4,k5_xboole_0(X3,X4)))) )),
% 2.70/0.73    inference(superposition,[],[f49,f30])).
% 2.70/0.73  fof(f448,plain,(
% 2.70/0.73    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 2.70/0.73    inference(backward_demodulation,[],[f134,f447])).
% 2.70/0.73  fof(f27,plain,(
% 2.70/0.73    sK1 != sK2),
% 2.70/0.73    inference(cnf_transformation,[],[f23])).
% 2.70/0.73  % SZS output end Proof for theBenchmark
% 2.70/0.73  % (9115)------------------------------
% 2.70/0.73  % (9115)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.70/0.73  % (9115)Termination reason: Refutation
% 2.70/0.73  
% 2.70/0.73  % (9115)Memory used [KB]: 8315
% 2.70/0.73  % (9115)Time elapsed: 0.325 s
% 2.70/0.73  % (9115)------------------------------
% 2.70/0.73  % (9115)------------------------------
% 2.70/0.73  % (9084)Success in time 0.374 s
%------------------------------------------------------------------------------
