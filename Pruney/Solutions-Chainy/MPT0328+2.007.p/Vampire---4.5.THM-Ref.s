%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:57 EST 2020

% Result     : Theorem 4.59s
% Output     : Refutation 4.59s
% Verified   : 
% Statistics : Number of formulae       :  108 ( 353 expanded)
%              Number of leaves         :   23 ( 116 expanded)
%              Depth                    :   22
%              Number of atoms          :  154 ( 422 expanded)
%              Number of equality atoms :   95 ( 345 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2782,plain,(
    $false ),
    inference(unit_resulting_resolution,[],[f490,f2742,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( sP3(X3,X1,X0)
      | ~ r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f2742,plain,(
    ~ sP3(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f936,f1303,f276])).

fof(f276,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_xboole_0(X1,X0))
      | ~ sP3(X2,X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(forward_demodulation,[],[f267,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f267,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0)))
      | ~ sP3(X2,X0,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(superposition,[],[f92,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f92,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))
      | ~ sP3(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != X2 ) ),
    inference(definition_unfolding,[],[f52,f68])).

fof(f68,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f37,f36])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP3(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f1303,plain,(
    ~ r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f890,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f43,f74])).

fof(f74,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f47,f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f56,f70])).

fof(f70,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f890,plain,(
    ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(trivial_inequality_removal,[],[f889])).

fof(f889,plain,
    ( sK1 != sK1
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f888,f31])).

fof(f888,plain,
    ( sK1 != k5_xboole_0(sK1,k1_xboole_0)
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f887,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f887,plain,
    ( sK1 != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f875,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f875,plain,
    ( sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))
    | ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(superposition,[],[f843,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f843,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))) ),
    inference(forward_demodulation,[],[f842,f380])).

fof(f380,plain,(
    ! [X14,X15] : k3_xboole_0(k5_xboole_0(X14,X15),X15) = k3_xboole_0(X15,k5_xboole_0(X14,X15)) ),
    inference(forward_demodulation,[],[f379,f170])).

fof(f170,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f154,f98])).

fof(f98,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f34,f31])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f154,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f48,f30])).

fof(f379,plain,(
    ! [X14,X15] : k3_xboole_0(k5_xboole_0(X14,X15),X15) = k5_xboole_0(X14,k5_xboole_0(X14,k3_xboole_0(X15,k5_xboole_0(X14,X15)))) ),
    inference(forward_demodulation,[],[f354,f221])).

fof(f221,plain,(
    ! [X6,X8,X7] : k5_xboole_0(k5_xboole_0(X6,X7),k5_xboole_0(X7,X8)) = k5_xboole_0(X6,X8) ),
    inference(superposition,[],[f48,f191])).

fof(f191,plain,(
    ! [X6,X5] : k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5 ),
    inference(superposition,[],[f174,f170])).

fof(f174,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f170,f34])).

fof(f354,plain,(
    ! [X14,X15] : k3_xboole_0(k5_xboole_0(X14,X15),X15) = k5_xboole_0(X14,k5_xboole_0(k5_xboole_0(X14,X15),k5_xboole_0(X15,k3_xboole_0(X15,k5_xboole_0(X14,X15))))) ),
    inference(superposition,[],[f75,f191])).

fof(f75,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f39,f68])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f842,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f841,f98])).

fof(f841,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(forward_demodulation,[],[f840,f162])).

fof(f162,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8)) ),
    inference(superposition,[],[f48,f34])).

fof(f840,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f451,f823])).

fof(f823,plain,(
    k1_xboole_0 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) ),
    inference(superposition,[],[f111,f572])).

fof(f572,plain,(
    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(unit_resulting_resolution,[],[f28,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0
      | r2_hidden(X1,X0) ) ),
    inference(definition_unfolding,[],[f45,f36,f74])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f28,plain,(
    ~ r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1] :
      ( k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1
      & ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
       => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    inference(negated_conjecture,[],[f23])).

fof(f23,conjecture,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

fof(f111,plain,(
    ! [X0,X1] : k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(unit_resulting_resolution,[],[f77,f42])).

fof(f77,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f33,f36])).

fof(f33,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f451,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(backward_demodulation,[],[f76,f420])).

fof(f420,plain,(
    ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3))) ),
    inference(superposition,[],[f78,f48])).

fof(f78,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f38,f68])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f76,plain,(
    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) ),
    inference(definition_unfolding,[],[f29,f36,f68,f74,f74])).

fof(f29,plain,(
    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f936,plain,(
    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(unit_resulting_resolution,[],[f834,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f834,plain,(
    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    inference(forward_demodulation,[],[f833,f30])).

fof(f833,plain,(
    k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(sK1,sK1) ),
    inference(forward_demodulation,[],[f817,f561])).

fof(f561,plain,(
    ! [X8,X7,X9] : k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X9)) ),
    inference(superposition,[],[f48,f192])).

fof(f192,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f174,f174])).

fof(f817,plain,(
    k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)) ),
    inference(superposition,[],[f75,f572])).

fof(f490,plain,(
    ! [X2,X0,X1] : r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0)) ),
    inference(unit_resulting_resolution,[],[f95,f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2))
      | ~ sP5(X4,X2,X1,X0) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3 ) ),
    inference(definition_unfolding,[],[f61,f72])).

fof(f61,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ sP5(X4,X2,X1,X0)
      | r2_hidden(X4,X3)
      | k1_enumset1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ( X2 = X4
            | X1 = X4
            | X0 = X4 ) ) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( k1_enumset1(X0,X1,X2) = X3
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ~ ( X2 != X4
              & X1 != X4
              & X0 != X4 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

fof(f95,plain,(
    ! [X4,X0,X1] : sP5(X4,X4,X1,X0) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( X2 != X4
      | sP5(X4,X2,X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 09:59:06 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.53  % (13324)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.22/0.54  % (13340)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.22/0.54  % (13341)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.56  % (13321)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.56  % (13322)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.57  % (13325)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.57  % (13320)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.57  % (13345)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.57  % (13328)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.58  % (13338)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.58  % (13337)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.58  % (13348)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.22/0.58  % (13338)Refutation not found, incomplete strategy% (13338)------------------------------
% 0.22/0.58  % (13338)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (13338)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.58  
% 0.22/0.58  % (13338)Memory used [KB]: 10618
% 0.22/0.58  % (13338)Time elapsed: 0.158 s
% 0.22/0.58  % (13338)------------------------------
% 0.22/0.58  % (13338)------------------------------
% 0.22/0.58  % (13343)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.58  % (13329)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.22/0.58  % (13332)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.58  % (13350)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.58  % (13334)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.58  % (13346)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.22/0.58  % (13344)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.22/0.59  % (13336)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.58/0.59  % (13336)Refutation not found, incomplete strategy% (13336)------------------------------
% 1.58/0.59  % (13336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (13336)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.59  
% 1.58/0.59  % (13336)Memory used [KB]: 6268
% 1.58/0.59  % (13336)Time elapsed: 0.168 s
% 1.58/0.59  % (13336)------------------------------
% 1.58/0.59  % (13336)------------------------------
% 1.58/0.59  % (13327)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.58/0.59  % (13330)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.58/0.59  % (13323)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.90/0.62  % (13331)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.90/0.62  % (13347)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.90/0.63  % (13339)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.90/0.65  % (13342)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.90/0.65  % (13349)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.90/0.66  % (13333)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.90/0.67  % (13326)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 2.39/0.76  % (13373)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 3.52/0.84  % (13374)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 3.52/0.86  % (13325)Time limit reached!
% 3.52/0.86  % (13325)------------------------------
% 3.52/0.86  % (13325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.52/0.86  % (13325)Termination reason: Time limit
% 3.52/0.86  
% 3.52/0.86  % (13325)Memory used [KB]: 8955
% 3.52/0.86  % (13325)Time elapsed: 0.412 s
% 3.52/0.86  % (13325)------------------------------
% 3.52/0.86  % (13325)------------------------------
% 4.06/0.91  % (13330)Time limit reached!
% 4.06/0.91  % (13330)------------------------------
% 4.06/0.91  % (13330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.06/0.91  % (13330)Termination reason: Time limit
% 4.06/0.91  
% 4.06/0.91  % (13330)Memory used [KB]: 14328
% 4.06/0.91  % (13330)Time elapsed: 0.502 s
% 4.06/0.91  % (13330)------------------------------
% 4.06/0.91  % (13330)------------------------------
% 4.06/0.94  % (13320)Time limit reached!
% 4.06/0.94  % (13320)------------------------------
% 4.06/0.94  % (13320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.06/0.94  % (13320)Termination reason: Time limit
% 4.06/0.94  
% 4.06/0.94  % (13320)Memory used [KB]: 4861
% 4.06/0.94  % (13320)Time elapsed: 0.527 s
% 4.06/0.94  % (13320)------------------------------
% 4.06/0.94  % (13320)------------------------------
% 4.06/0.97  % (13321)Time limit reached!
% 4.06/0.97  % (13321)------------------------------
% 4.06/0.97  % (13321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.59/0.98  % (13332)Time limit reached!
% 4.59/0.98  % (13332)------------------------------
% 4.59/0.98  % (13332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.59/0.98  % (13332)Termination reason: Time limit
% 4.59/0.98  % (13332)Termination phase: Saturation
% 4.59/0.98  
% 4.59/0.98  % (13332)Memory used [KB]: 10618
% 4.59/0.98  % (13332)Time elapsed: 0.500 s
% 4.59/0.98  % (13332)------------------------------
% 4.59/0.98  % (13332)------------------------------
% 4.59/0.98  % (13321)Termination reason: Time limit
% 4.59/0.98  
% 4.59/0.98  % (13321)Memory used [KB]: 9083
% 4.59/0.98  % (13321)Time elapsed: 0.532 s
% 4.59/0.98  % (13321)------------------------------
% 4.59/0.98  % (13321)------------------------------
% 4.59/0.99  % (13345)Refutation found. Thanks to Tanya!
% 4.59/0.99  % SZS status Theorem for theBenchmark
% 4.59/0.99  % SZS output start Proof for theBenchmark
% 4.59/0.99  fof(f2782,plain,(
% 4.59/0.99    $false),
% 4.59/0.99    inference(unit_resulting_resolution,[],[f490,f2742,f50])).
% 4.59/0.99  fof(f50,plain,(
% 4.59/0.99    ( ! [X0,X3,X1] : (sP3(X3,X1,X0) | ~r2_hidden(X3,X1)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f2])).
% 4.59/0.99  fof(f2,axiom,(
% 4.59/0.99    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).
% 4.59/0.99  fof(f2742,plain,(
% 4.59/0.99    ~sP3(sK0,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 4.59/0.99    inference(unit_resulting_resolution,[],[f936,f1303,f276])).
% 4.59/0.99  fof(f276,plain,(
% 4.59/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_xboole_0(X1,X0)) | ~sP3(X2,X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 4.59/0.99    inference(forward_demodulation,[],[f267,f31])).
% 4.59/0.99  fof(f31,plain,(
% 4.59/0.99    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 4.59/0.99    inference(cnf_transformation,[],[f6])).
% 4.59/0.99  fof(f6,axiom,(
% 4.59/0.99    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 4.59/0.99  fof(f267,plain,(
% 4.59/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,k5_xboole_0(X1,k5_xboole_0(X0,k1_xboole_0))) | ~sP3(X2,X0,X1) | ~r1_xboole_0(X0,X1)) )),
% 4.59/0.99    inference(superposition,[],[f92,f42])).
% 4.59/0.99  fof(f42,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f3])).
% 4.59/0.99  fof(f3,axiom,(
% 4.59/0.99    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).
% 4.59/0.99  fof(f92,plain,(
% 4.59/0.99    ( ! [X0,X3,X1] : (r2_hidden(X3,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) | ~sP3(X3,X1,X0)) )),
% 4.59/0.99    inference(equality_resolution,[],[f86])).
% 4.59/0.99  fof(f86,plain,(
% 4.59/0.99    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) != X2) )),
% 4.59/0.99    inference(definition_unfolding,[],[f52,f68])).
% 4.59/0.99  fof(f68,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 4.59/0.99    inference(definition_unfolding,[],[f37,f36])).
% 4.59/0.99  fof(f36,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 4.59/0.99    inference(cnf_transformation,[],[f4])).
% 4.59/0.99  fof(f4,axiom,(
% 4.59/0.99    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 4.59/0.99  fof(f37,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 4.59/0.99    inference(cnf_transformation,[],[f12])).
% 4.59/0.99  fof(f12,axiom,(
% 4.59/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 4.59/0.99  fof(f52,plain,(
% 4.59/0.99    ( ! [X2,X0,X3,X1] : (~sP3(X3,X1,X0) | r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 4.59/0.99    inference(cnf_transformation,[],[f2])).
% 4.59/0.99  fof(f1303,plain,(
% 4.59/0.99    ~r2_hidden(sK0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(unit_resulting_resolution,[],[f890,f80])).
% 4.59/0.99  fof(f80,plain,(
% 4.59/0.99    ( ! [X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 4.59/0.99    inference(definition_unfolding,[],[f43,f74])).
% 4.59/0.99  fof(f74,plain,(
% 4.59/0.99    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 4.59/0.99    inference(definition_unfolding,[],[f32,f73])).
% 4.59/0.99  fof(f73,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.59/0.99    inference(definition_unfolding,[],[f35,f72])).
% 4.59/0.99  fof(f72,plain,(
% 4.59/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.59/0.99    inference(definition_unfolding,[],[f47,f71])).
% 4.59/0.99  fof(f71,plain,(
% 4.59/0.99    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.59/0.99    inference(definition_unfolding,[],[f56,f70])).
% 4.59/0.99  fof(f70,plain,(
% 4.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.59/0.99    inference(definition_unfolding,[],[f65,f69])).
% 4.59/0.99  fof(f69,plain,(
% 4.59/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.59/0.99    inference(definition_unfolding,[],[f66,f67])).
% 4.59/0.99  fof(f67,plain,(
% 4.59/0.99    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f20])).
% 4.59/0.99  fof(f20,axiom,(
% 4.59/0.99    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 4.59/0.99  fof(f66,plain,(
% 4.59/0.99    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f19])).
% 4.59/0.99  fof(f19,axiom,(
% 4.59/0.99    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 4.59/0.99  fof(f65,plain,(
% 4.59/0.99    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f18])).
% 4.59/0.99  fof(f18,axiom,(
% 4.59/0.99    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 4.59/0.99  fof(f56,plain,(
% 4.59/0.99    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f17])).
% 4.59/0.99  fof(f17,axiom,(
% 4.59/0.99    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 4.59/0.99  fof(f47,plain,(
% 4.59/0.99    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f16])).
% 4.59/0.99  fof(f16,axiom,(
% 4.59/0.99    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 4.59/0.99  fof(f35,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f15])).
% 4.59/0.99  fof(f15,axiom,(
% 4.59/0.99    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.59/0.99  fof(f32,plain,(
% 4.59/0.99    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f14])).
% 4.59/0.99  fof(f14,axiom,(
% 4.59/0.99    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 4.59/0.99  fof(f43,plain,(
% 4.59/0.99    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f21])).
% 4.59/0.99  fof(f21,axiom,(
% 4.59/0.99    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 4.59/0.99  fof(f890,plain,(
% 4.59/0.99    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(trivial_inequality_removal,[],[f889])).
% 4.59/0.99  fof(f889,plain,(
% 4.59/0.99    sK1 != sK1 | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(forward_demodulation,[],[f888,f31])).
% 4.59/0.99  fof(f888,plain,(
% 4.59/0.99    sK1 != k5_xboole_0(sK1,k1_xboole_0) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(forward_demodulation,[],[f887,f30])).
% 4.59/0.99  fof(f30,plain,(
% 4.59/0.99    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f9])).
% 4.59/0.99  fof(f9,axiom,(
% 4.59/0.99    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 4.59/0.99  fof(f887,plain,(
% 4.59/0.99    sK1 != k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(forward_demodulation,[],[f875,f48])).
% 4.59/0.99  fof(f48,plain,(
% 4.59/0.99    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 4.59/0.99    inference(cnf_transformation,[],[f8])).
% 4.59/0.99  fof(f8,axiom,(
% 4.59/0.99    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 4.59/0.99  fof(f875,plain,(
% 4.59/0.99    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)) | ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(superposition,[],[f843,f40])).
% 4.59/0.99  fof(f40,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f26])).
% 4.59/0.99  fof(f26,plain,(
% 4.59/0.99    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.59/0.99    inference(ennf_transformation,[],[f5])).
% 4.59/0.99  fof(f5,axiom,(
% 4.59/0.99    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.59/0.99  fof(f843,plain,(
% 4.59/0.99    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))))),
% 4.59/0.99    inference(forward_demodulation,[],[f842,f380])).
% 4.59/0.99  fof(f380,plain,(
% 4.59/0.99    ( ! [X14,X15] : (k3_xboole_0(k5_xboole_0(X14,X15),X15) = k3_xboole_0(X15,k5_xboole_0(X14,X15))) )),
% 4.59/0.99    inference(forward_demodulation,[],[f379,f170])).
% 4.59/0.99  fof(f170,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 4.59/0.99    inference(forward_demodulation,[],[f154,f98])).
% 4.59/0.99  fof(f98,plain,(
% 4.59/0.99    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 4.59/0.99    inference(superposition,[],[f34,f31])).
% 4.59/0.99  fof(f34,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f1])).
% 4.59/0.99  fof(f1,axiom,(
% 4.59/0.99    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 4.59/0.99  fof(f154,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 4.59/0.99    inference(superposition,[],[f48,f30])).
% 4.59/0.99  fof(f379,plain,(
% 4.59/0.99    ( ! [X14,X15] : (k3_xboole_0(k5_xboole_0(X14,X15),X15) = k5_xboole_0(X14,k5_xboole_0(X14,k3_xboole_0(X15,k5_xboole_0(X14,X15))))) )),
% 4.59/0.99    inference(forward_demodulation,[],[f354,f221])).
% 4.59/0.99  fof(f221,plain,(
% 4.59/0.99    ( ! [X6,X8,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),k5_xboole_0(X7,X8)) = k5_xboole_0(X6,X8)) )),
% 4.59/0.99    inference(superposition,[],[f48,f191])).
% 4.59/0.99  fof(f191,plain,(
% 4.59/0.99    ( ! [X6,X5] : (k5_xboole_0(k5_xboole_0(X5,X6),X6) = X5) )),
% 4.59/0.99    inference(superposition,[],[f174,f170])).
% 4.59/0.99  fof(f174,plain,(
% 4.59/0.99    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 4.59/0.99    inference(superposition,[],[f170,f34])).
% 4.59/0.99  fof(f354,plain,(
% 4.59/0.99    ( ! [X14,X15] : (k3_xboole_0(k5_xboole_0(X14,X15),X15) = k5_xboole_0(X14,k5_xboole_0(k5_xboole_0(X14,X15),k5_xboole_0(X15,k3_xboole_0(X15,k5_xboole_0(X14,X15)))))) )),
% 4.59/0.99    inference(superposition,[],[f75,f191])).
% 4.59/0.99  fof(f75,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 4.59/0.99    inference(definition_unfolding,[],[f39,f68])).
% 4.59/0.99  fof(f39,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 4.59/0.99    inference(cnf_transformation,[],[f11])).
% 4.59/0.99  fof(f11,axiom,(
% 4.59/0.99    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 4.59/0.99  fof(f842,plain,(
% 4.59/0.99    sK1 != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k3_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(forward_demodulation,[],[f841,f98])).
% 4.59/0.99  fof(f841,plain,(
% 4.59/0.99    sK1 != k5_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k3_xboole_0(k5_xboole_0(k1_xboole_0,k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(forward_demodulation,[],[f840,f162])).
% 4.59/0.99  fof(f162,plain,(
% 4.59/0.99    ( ! [X8,X7,X9] : (k5_xboole_0(X7,k5_xboole_0(X8,X9)) = k5_xboole_0(X9,k5_xboole_0(X7,X8))) )),
% 4.59/0.99    inference(superposition,[],[f48,f34])).
% 4.59/0.99  fof(f840,plain,(
% 4.59/0.99    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k1_xboole_0)),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(backward_demodulation,[],[f451,f823])).
% 4.59/0.99  fof(f823,plain,(
% 4.59/0.99    k1_xboole_0 = k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),
% 4.59/0.99    inference(superposition,[],[f111,f572])).
% 4.59/0.99  fof(f572,plain,(
% 4.59/0.99    sK1 = k5_xboole_0(sK1,k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(unit_resulting_resolution,[],[f28,f82])).
% 4.59/0.99  fof(f82,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0 | r2_hidden(X1,X0)) )),
% 4.59/0.99    inference(definition_unfolding,[],[f45,f36,f74])).
% 4.59/0.99  fof(f45,plain,(
% 4.59/0.99    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 4.59/0.99    inference(cnf_transformation,[],[f22])).
% 4.59/0.99  fof(f22,axiom,(
% 4.59/0.99    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 4.59/0.99  fof(f28,plain,(
% 4.59/0.99    ~r2_hidden(sK0,sK1)),
% 4.59/0.99    inference(cnf_transformation,[],[f25])).
% 4.59/0.99  fof(f25,plain,(
% 4.59/0.99    ? [X0,X1] : (k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) != X1 & ~r2_hidden(X0,X1))),
% 4.59/0.99    inference(ennf_transformation,[],[f24])).
% 4.59/0.99  fof(f24,negated_conjecture,(
% 4.59/0.99    ~! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 4.59/0.99    inference(negated_conjecture,[],[f23])).
% 4.59/0.99  fof(f23,conjecture,(
% 4.59/0.99    ! [X0,X1] : (~r2_hidden(X0,X1) => k4_xboole_0(k2_xboole_0(X1,k1_tarski(X0)),k1_tarski(X0)) = X1)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).
% 4.59/0.99  fof(f111,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k1_xboole_0 = k3_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 4.59/0.99    inference(unit_resulting_resolution,[],[f77,f42])).
% 4.59/0.99  fof(f77,plain,(
% 4.59/0.99    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 4.59/0.99    inference(definition_unfolding,[],[f33,f36])).
% 4.59/0.99  fof(f33,plain,(
% 4.59/0.99    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f7])).
% 4.59/0.99  fof(f7,axiom,(
% 4.59/0.99    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 4.59/0.99  fof(f451,plain,(
% 4.59/0.99    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(backward_demodulation,[],[f76,f420])).
% 4.59/0.99  fof(f420,plain,(
% 4.59/0.99    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X3,X2))) = k5_xboole_0(X2,k5_xboole_0(X3,k3_xboole_0(X2,X3)))) )),
% 4.59/0.99    inference(superposition,[],[f78,f48])).
% 4.59/0.99  fof(f78,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 4.59/0.99    inference(definition_unfolding,[],[f38,f68])).
% 4.59/0.99  fof(f38,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 4.59/0.99    inference(cnf_transformation,[],[f10])).
% 4.59/0.99  fof(f10,axiom,(
% 4.59/0.99    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 4.59/0.99  fof(f76,plain,(
% 4.59/0.99    sK1 != k5_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k3_xboole_0(k5_xboole_0(sK1,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))),
% 4.59/0.99    inference(definition_unfolding,[],[f29,f36,f68,f74,f74])).
% 4.59/0.99  fof(f29,plain,(
% 4.59/0.99    sK1 != k4_xboole_0(k2_xboole_0(sK1,k1_tarski(sK0)),k1_tarski(sK0))),
% 4.59/0.99    inference(cnf_transformation,[],[f25])).
% 4.59/0.99  fof(f936,plain,(
% 4.59/0.99    r1_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 4.59/0.99    inference(unit_resulting_resolution,[],[f834,f41])).
% 4.59/0.99  fof(f41,plain,(
% 4.59/0.99    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f3])).
% 4.59/0.99  fof(f834,plain,(
% 4.59/0.99    k1_xboole_0 = k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 4.59/0.99    inference(forward_demodulation,[],[f833,f30])).
% 4.59/0.99  fof(f833,plain,(
% 4.59/0.99    k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(sK1,sK1)),
% 4.59/0.99    inference(forward_demodulation,[],[f817,f561])).
% 4.59/0.99  fof(f561,plain,(
% 4.59/0.99    ( ! [X8,X7,X9] : (k5_xboole_0(X8,X9) = k5_xboole_0(k5_xboole_0(X7,X8),k5_xboole_0(X7,X9))) )),
% 4.59/0.99    inference(superposition,[],[f48,f192])).
% 4.59/0.99  fof(f192,plain,(
% 4.59/0.99    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 4.59/0.99    inference(superposition,[],[f174,f174])).
% 4.59/0.99  fof(f817,plain,(
% 4.59/0.99    k3_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1),k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1))),
% 4.59/0.99    inference(superposition,[],[f75,f572])).
% 4.59/0.99  fof(f490,plain,(
% 4.59/0.99    ( ! [X2,X0,X1] : (r2_hidden(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X2,X0))) )),
% 4.59/0.99    inference(unit_resulting_resolution,[],[f95,f94])).
% 4.59/0.99  fof(f94,plain,(
% 4.59/0.99    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) | ~sP5(X4,X2,X1,X0)) )),
% 4.59/0.99    inference(equality_resolution,[],[f90])).
% 4.59/0.99  fof(f90,plain,(
% 4.59/0.99    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) != X3) )),
% 4.59/0.99    inference(definition_unfolding,[],[f61,f72])).
% 4.59/0.99  fof(f61,plain,(
% 4.59/0.99    ( ! [X4,X2,X0,X3,X1] : (~sP5(X4,X2,X1,X0) | r2_hidden(X4,X3) | k1_enumset1(X0,X1,X2) != X3) )),
% 4.59/0.99    inference(cnf_transformation,[],[f27])).
% 4.59/0.99  fof(f27,plain,(
% 4.59/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> (X2 = X4 | X1 = X4 | X0 = X4)))),
% 4.59/0.99    inference(ennf_transformation,[],[f13])).
% 4.59/0.99  fof(f13,axiom,(
% 4.59/0.99    ! [X0,X1,X2,X3] : (k1_enumset1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ~(X2 != X4 & X1 != X4 & X0 != X4)))),
% 4.59/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).
% 4.59/0.99  fof(f95,plain,(
% 4.59/0.99    ( ! [X4,X0,X1] : (sP5(X4,X4,X1,X0)) )),
% 4.59/0.99    inference(equality_resolution,[],[f59])).
% 4.59/0.99  fof(f59,plain,(
% 4.59/0.99    ( ! [X4,X2,X0,X1] : (X2 != X4 | sP5(X4,X2,X1,X0)) )),
% 4.59/0.99    inference(cnf_transformation,[],[f27])).
% 4.59/0.99  % SZS output end Proof for theBenchmark
% 4.59/0.99  % (13345)------------------------------
% 4.59/0.99  % (13345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.59/0.99  % (13345)Termination reason: Refutation
% 4.59/0.99  
% 4.59/0.99  % (13345)Memory used [KB]: 9338
% 4.59/0.99  % (13345)Time elapsed: 0.546 s
% 4.59/0.99  % (13345)------------------------------
% 4.59/0.99  % (13345)------------------------------
% 4.59/0.99  % (13318)Success in time 0.616 s
%------------------------------------------------------------------------------
