%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:40:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 481 expanded)
%              Number of leaves         :   26 ( 167 expanded)
%              Depth                    :   16
%              Number of atoms          :  164 ( 583 expanded)
%              Number of equality atoms :   79 ( 457 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f127,f149,f192,f307])).

fof(f307,plain,
    ( spl3_4
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f305,f84])).

fof(f84,plain,(
    ! [X1] : k5_xboole_0(X1,k1_xboole_0) = X1 ),
    inference(superposition,[],[f37,f73])).

fof(f73,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f72,f34])).

fof(f34,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f72,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f65,f64])).

fof(f64,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f33,f61])).

fof(f61,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f58,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f42,f56])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f48,f55])).

fof(f55,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f49,f54])).

fof(f54,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f50,f52])).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f50,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f49,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f39,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f33,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f65,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f36,f60])).

fof(f60,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f40,f59])).

fof(f59,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f38,f58])).

fof(f38,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f36,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f37,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f305,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k1_xboole_0)
    | spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f304,f34])).

fof(f304,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,sK1))
    | spl3_4
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f303,f242])).

fof(f242,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f241,f163])).

fof(f163,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X5) ),
    inference(superposition,[],[f71,f62])).

fof(f62,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f53,f59,f55,f57])).

fof(f53,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).

fof(f71,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f51,f54,f59,f55,f61])).

fof(f51,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).

fof(f241,plain,
    ( sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f237,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f47,f56,f56])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).

fof(f237,plain,
    ( sK1 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f191,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f41,f59])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f191,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f189])).

fof(f189,plain,
    ( spl3_6
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f303,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))))
    | spl3_4 ),
    inference(forward_demodulation,[],[f285,f163])).

fof(f285,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))))
    | spl3_4 ),
    inference(superposition,[],[f148,f90])).

fof(f90,plain,(
    ! [X6,X4,X5] : k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6) ),
    inference(superposition,[],[f43,f37])).

fof(f43,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f148,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl3_4
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f192,plain,
    ( spl3_6
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f111,f80,f75,f189])).

fof(f75,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f80,plain,
    ( spl3_2
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f111,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(unit_resulting_resolution,[],[f77,f82,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f46,f58])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f82,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f80])).

fof(f77,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f75])).

fof(f149,plain,
    ( ~ spl3_4
    | spl3_3 ),
    inference(avatar_split_clause,[],[f129,f124,f146])).

fof(f124,plain,
    ( spl3_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f129,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))
    | spl3_3 ),
    inference(forward_demodulation,[],[f128,f37])).

fof(f128,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))
    | spl3_3 ),
    inference(forward_demodulation,[],[f126,f70])).

fof(f126,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)))
    | spl3_3 ),
    inference(avatar_component_clause,[],[f124])).

fof(f127,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f63,f124])).

fof(f63,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))) ),
    inference(definition_unfolding,[],[f32,f58,f60,f58])).

fof(f32,plain,(
    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,
    ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
    & r2_hidden(sK2,sK1)
    & r2_hidden(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f26])).

fof(f26,plain,
    ( ? [X0,X1,X2] :
        ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
        & r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
   => ( k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)
      & r2_hidden(sK2,sK1)
      & r2_hidden(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1)
      & r2_hidden(X2,X1)
      & r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( r2_hidden(X2,X1)
          & r2_hidden(X0,X1) )
       => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f83,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    r2_hidden(sK2,sK1) ),
    inference(cnf_transformation,[],[f27])).

fof(f78,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f75])).

fof(f30,plain,(
    r2_hidden(sK0,sK1) ),
    inference(cnf_transformation,[],[f27])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.44  % (11312)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.44  % (11314)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.45  % (11321)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (11321)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f308,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f78,f83,f127,f149,f192,f307])).
% 0.20/0.47  fof(f307,plain,(
% 0.20/0.47    spl3_4 | ~spl3_6),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f306])).
% 0.20/0.47  fof(f306,plain,(
% 0.20/0.47    $false | (spl3_4 | ~spl3_6)),
% 0.20/0.47    inference(subsumption_resolution,[],[f305,f84])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ( ! [X1] : (k5_xboole_0(X1,k1_xboole_0) = X1) )),
% 0.20/0.47    inference(superposition,[],[f37,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 0.20/0.47    inference(forward_demodulation,[],[f72,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 0.20/0.47    inference(forward_demodulation,[],[f65,f64])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f33,f61])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f35,f58])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f39,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f42,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f48,f55])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f49,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f50,f52])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.47  fof(f50,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k4_enumset1(X0,X0,X1,X2,X3,X4)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f11])).
% 0.20/0.47  fof(f11,axiom,(
% 0.20/0.47    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,axiom,(
% 0.20/0.47    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 0.20/0.47    inference(definition_unfolding,[],[f36,f60])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f40,f59])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f38,f58])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,axiom,(
% 0.20/0.47    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.47    inference(rectify,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.20/0.47  fof(f305,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k1_xboole_0) | (spl3_4 | ~spl3_6)),
% 0.20/0.47    inference(forward_demodulation,[],[f304,f34])).
% 0.20/0.47  fof(f304,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,sK1)) | (spl3_4 | ~spl3_6)),
% 0.20/0.47    inference(forward_demodulation,[],[f303,f242])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | ~spl3_6),
% 0.20/0.47    inference(forward_demodulation,[],[f241,f163])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X1,X2,X3,X4,X5,X5,X5)) )),
% 0.20/0.47    inference(superposition,[],[f71,f62])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X6,X7)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f53,f59,f55,f57])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_enumset1)).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X5)))) )),
% 0.20/0.47    inference(definition_unfolding,[],[f51,f54,f59,f55,f61])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_tarski(X5))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_enumset1)).
% 0.20/0.47  fof(f241,plain,(
% 0.20/0.47    sK1 = k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))) | ~spl3_6),
% 0.20/0.47    inference(forward_demodulation,[],[f237,f70])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f47,f56,f56])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_enumset1)).
% 0.20/0.47  fof(f237,plain,(
% 0.20/0.47    sK1 = k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)) | ~spl3_6),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f191,f66])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 0.20/0.47    inference(definition_unfolding,[],[f41,f59])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f189])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    spl3_6 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f303,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))) | spl3_4),
% 0.20/0.47    inference(forward_demodulation,[],[f285,f163])).
% 0.20/0.47  fof(f285,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k5_xboole_0(sK1,k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))) | spl3_4),
% 0.20/0.47    inference(superposition,[],[f148,f90])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    ( ! [X6,X4,X5] : (k5_xboole_0(X4,k5_xboole_0(X5,X6)) = k5_xboole_0(k5_xboole_0(X5,X4),X6)) )),
% 0.20/0.47    inference(superposition,[],[f43,f37])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))) | spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f146])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    spl3_4 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) = k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    spl3_6 | ~spl3_1 | ~spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f111,f80,f75,f189])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    spl3_1 <=> r2_hidden(sK0,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl3_2 <=> r2_hidden(sK2,sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1) | (~spl3_1 | ~spl3_2)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f77,f82,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.47    inference(definition_unfolding,[],[f46,f58])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.47    inference(flattening,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.47    inference(nnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    r2_hidden(sK2,sK1) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    r2_hidden(sK0,sK1) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f75])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    ~spl3_4 | spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f129,f124,f146])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl3_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))) | spl3_3),
% 0.20/0.47    inference(forward_demodulation,[],[f128,f37])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_tarski(k6_enumset1(sK1,sK1,sK1,sK1,sK1,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2)))) | spl3_3),
% 0.20/0.47    inference(forward_demodulation,[],[f126,f70])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1))) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f124])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f63,f124])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2) != k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK2),sK1)))),
% 0.20/0.47    inference(definition_unfolding,[],[f32,f58,f60,f58])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1)) => (k2_tarski(sK0,sK2) != k3_xboole_0(k2_tarski(sK0,sK2),sK1) & r2_hidden(sK2,sK1) & r2_hidden(sK0,sK1))),
% 0.20/0.47    introduced(choice_axiom,[])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & r2_hidden(X2,X1) & r2_hidden(X0,X1))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ? [X0,X1,X2] : (k2_tarski(X0,X2) != k3_xboole_0(k2_tarski(X0,X2),X1) & (r2_hidden(X2,X1) & r2_hidden(X0,X1)))),
% 0.20/0.47    inference(ennf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,negated_conjecture,(
% 0.20/0.47    ~! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.20/0.47    inference(negated_conjecture,[],[f20])).
% 0.20/0.47  fof(f20,conjecture,(
% 0.20/0.47    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f80])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    r2_hidden(sK2,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f75])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    r2_hidden(sK0,sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (11321)------------------------------
% 0.20/0.47  % (11321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (11321)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (11321)Memory used [KB]: 11001
% 0.20/0.47  % (11321)Time elapsed: 0.048 s
% 0.20/0.47  % (11321)------------------------------
% 0.20/0.47  % (11321)------------------------------
% 0.20/0.48  % (11305)Success in time 0.116 s
%------------------------------------------------------------------------------
