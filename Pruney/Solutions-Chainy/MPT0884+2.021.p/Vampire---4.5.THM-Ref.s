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
% DateTime   : Thu Dec  3 12:58:58 EST 2020

% Result     : Theorem 2.84s
% Output     : Refutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 221 expanded)
%              Number of leaves         :   17 (  87 expanded)
%              Depth                    :   11
%              Number of atoms          :   78 ( 246 expanded)
%              Number of equality atoms :   58 ( 221 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1603,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f95,f326,f1602])).

fof(f1602,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f1601])).

fof(f1601,plain,
    ( $false
    | spl5_3 ),
    inference(trivial_inequality_removal,[],[f1600])).

fof(f1600,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
    | spl5_3 ),
    inference(forward_demodulation,[],[f1593,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f30,f22,f37,f22])).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f21,f22])).

fof(f21,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f1593,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | spl5_3 ),
    inference(superposition,[],[f325,f191])).

fof(f191,plain,(
    ! [X19,X17,X20,X18,X16] : k2_zfmisc_1(k1_enumset1(k4_tarski(X16,X17),k4_tarski(X16,X17),X18),k1_enumset1(X19,X19,X20)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X16,X16,X16),k1_enumset1(X17,X17,X17)),k1_enumset1(X19,X19,X19)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X16,X16,X16),k1_enumset1(X17,X17,X17)),k1_enumset1(X19,X19,X19)),k1_enumset1(k4_tarski(k4_tarski(X16,X17),X20),k4_tarski(X18,X19),k4_tarski(X18,X20)))) ),
    inference(superposition,[],[f190,f44])).

fof(f190,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)))) ),
    inference(forward_demodulation,[],[f47,f44])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)))) ),
    inference(definition_unfolding,[],[f33,f22,f22,f38])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
    inference(definition_unfolding,[],[f31,f36,f37])).

fof(f36,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f23,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f325,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f323])).

fof(f323,plain,
    ( spl5_3
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f326,plain,
    ( ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f299,f92,f323])).

fof(f92,plain,
    ( spl5_2
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f299,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_2 ),
    inference(backward_demodulation,[],[f94,f289])).

fof(f289,plain,(
    ! [X10,X11,X9] : k1_enumset1(X10,X9,X11) = k1_enumset1(X9,X10,X11) ),
    inference(superposition,[],[f175,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f28,f36,f22,f22])).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).

fof(f175,plain,(
    ! [X14,X15,X13] : k3_tarski(k1_enumset1(k1_enumset1(X15,X15,X13),k1_enumset1(X15,X15,X13),k1_enumset1(X14,X14,X13))) = k1_enumset1(X15,X13,X14) ),
    inference(forward_demodulation,[],[f169,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f27,f36,f37,f22])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).

fof(f169,plain,(
    ! [X14,X15,X13] : k3_tarski(k1_enumset1(k1_enumset1(X15,X15,X13),k1_enumset1(X15,X15,X13),k1_enumset1(X14,X14,X13))) = k3_tarski(k1_enumset1(k1_enumset1(X15,X15,X15),k1_enumset1(X15,X15,X15),k1_enumset1(X13,X13,X14))) ),
    inference(superposition,[],[f48,f43])).

fof(f48,plain,(
    ! [X4,X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ),
    inference(definition_unfolding,[],[f35,f39,f36,f22])).

fof(f39,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))))) ),
    inference(definition_unfolding,[],[f34,f36,f37,f38])).

fof(f34,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).

fof(f94,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f95,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f90,f50,f92])).

fof(f50,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f90,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f89,f44])).

fof(f89,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f52,f44])).

fof(f52,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f53,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f41,f50])).

fof(f41,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    inference(definition_unfolding,[],[f20,f24,f22,f37,f22,f38,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f20,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).

fof(f18,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:47:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.46  % (16690)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (16700)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (16685)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (16692)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (16691)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (16687)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (16688)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.48  % (16694)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (16698)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (16695)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (16702)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (16699)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.49  % (16686)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (16696)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (16696)Refutation not found, incomplete strategy% (16696)------------------------------
% 0.20/0.49  % (16696)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (16696)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (16696)Memory used [KB]: 10618
% 0.20/0.49  % (16696)Time elapsed: 0.082 s
% 0.20/0.49  % (16696)------------------------------
% 0.20/0.49  % (16696)------------------------------
% 0.20/0.50  % (16697)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.50  % (16689)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (16693)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.51  % (16701)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 2.84/0.74  % (16691)Refutation found. Thanks to Tanya!
% 2.84/0.74  % SZS status Theorem for theBenchmark
% 2.84/0.74  % SZS output start Proof for theBenchmark
% 2.84/0.74  fof(f1603,plain,(
% 2.84/0.74    $false),
% 2.84/0.74    inference(avatar_sat_refutation,[],[f53,f95,f326,f1602])).
% 2.84/0.74  fof(f1602,plain,(
% 2.84/0.74    spl5_3),
% 2.84/0.74    inference(avatar_contradiction_clause,[],[f1601])).
% 2.84/0.74  fof(f1601,plain,(
% 2.84/0.74    $false | spl5_3),
% 2.84/0.74    inference(trivial_inequality_removal,[],[f1600])).
% 2.84/0.75  fof(f1600,plain,(
% 2.84/0.75    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) | spl5_3),
% 2.84/0.75    inference(forward_demodulation,[],[f1593,f44])).
% 2.84/0.75  fof(f44,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 2.84/0.75    inference(definition_unfolding,[],[f30,f22,f37,f22])).
% 2.84/0.75  fof(f37,plain,(
% 2.84/0.75    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 2.84/0.75    inference(definition_unfolding,[],[f21,f22])).
% 2.84/0.75  fof(f21,plain,(
% 2.84/0.75    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f7])).
% 2.84/0.75  fof(f7,axiom,(
% 2.84/0.75    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 2.84/0.75  fof(f22,plain,(
% 2.84/0.75    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f8])).
% 2.84/0.75  fof(f8,axiom,(
% 2.84/0.75    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 2.84/0.75  fof(f30,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 2.84/0.75    inference(cnf_transformation,[],[f12])).
% 2.84/0.75  fof(f12,axiom,(
% 2.84/0.75    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 2.84/0.75  fof(f1593,plain,(
% 2.84/0.75    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) | spl5_3),
% 2.84/0.75    inference(superposition,[],[f325,f191])).
% 2.84/0.75  fof(f191,plain,(
% 2.84/0.75    ( ! [X19,X17,X20,X18,X16] : (k2_zfmisc_1(k1_enumset1(k4_tarski(X16,X17),k4_tarski(X16,X17),X18),k1_enumset1(X19,X19,X20)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X16,X16,X16),k1_enumset1(X17,X17,X17)),k1_enumset1(X19,X19,X19)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X16,X16,X16),k1_enumset1(X17,X17,X17)),k1_enumset1(X19,X19,X19)),k1_enumset1(k4_tarski(k4_tarski(X16,X17),X20),k4_tarski(X18,X19),k4_tarski(X18,X20))))) )),
% 2.84/0.75    inference(superposition,[],[f190,f44])).
% 2.84/0.75  fof(f190,plain,(
% 2.84/0.75    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))))) )),
% 2.84/0.75    inference(forward_demodulation,[],[f47,f44])).
% 2.84/0.75  fof(f47,plain,(
% 2.84/0.75    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))))) )),
% 2.84/0.75    inference(definition_unfolding,[],[f33,f22,f22,f38])).
% 2.84/0.75  fof(f38,plain,(
% 2.84/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)))) )),
% 2.84/0.75    inference(definition_unfolding,[],[f31,f36,f37])).
% 2.84/0.75  fof(f36,plain,(
% 2.84/0.75    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.84/0.75    inference(definition_unfolding,[],[f23,f22])).
% 2.84/0.75  fof(f23,plain,(
% 2.84/0.75    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f10])).
% 2.84/0.75  fof(f10,axiom,(
% 2.84/0.75    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.84/0.75  fof(f31,plain,(
% 2.84/0.75    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))) )),
% 2.84/0.75    inference(cnf_transformation,[],[f4])).
% 2.84/0.75  fof(f4,axiom,(
% 2.84/0.75    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_enumset1)).
% 2.84/0.75  fof(f33,plain,(
% 2.84/0.75    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 2.84/0.75    inference(cnf_transformation,[],[f11])).
% 2.84/0.75  fof(f11,axiom,(
% 2.84/0.75    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 2.84/0.75  fof(f325,plain,(
% 2.84/0.75    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_3),
% 2.84/0.75    inference(avatar_component_clause,[],[f323])).
% 2.84/0.75  fof(f323,plain,(
% 2.84/0.75    spl5_3 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.84/0.75  fof(f326,plain,(
% 2.84/0.75    ~spl5_3 | spl5_2),
% 2.84/0.75    inference(avatar_split_clause,[],[f299,f92,f323])).
% 2.84/0.75  fof(f92,plain,(
% 2.84/0.75    spl5_2 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 2.84/0.75    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.84/0.75  fof(f299,plain,(
% 2.84/0.75    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_2),
% 2.84/0.75    inference(backward_demodulation,[],[f94,f289])).
% 2.84/0.75  fof(f289,plain,(
% 2.84/0.75    ( ! [X10,X11,X9] : (k1_enumset1(X10,X9,X11) = k1_enumset1(X9,X10,X11)) )),
% 2.84/0.75    inference(superposition,[],[f175,f43])).
% 2.84/0.75  fof(f43,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0)))) )),
% 2.84/0.75    inference(definition_unfolding,[],[f28,f36,f22,f22])).
% 2.84/0.75  fof(f28,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 2.84/0.75    inference(cnf_transformation,[],[f2])).
% 2.84/0.75  fof(f2,axiom,(
% 2.84/0.75    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_enumset1)).
% 2.84/0.75  fof(f175,plain,(
% 2.84/0.75    ( ! [X14,X15,X13] : (k3_tarski(k1_enumset1(k1_enumset1(X15,X15,X13),k1_enumset1(X15,X15,X13),k1_enumset1(X14,X14,X13))) = k1_enumset1(X15,X13,X14)) )),
% 2.84/0.75    inference(forward_demodulation,[],[f169,f42])).
% 2.84/0.75  fof(f42,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)))) )),
% 2.84/0.75    inference(definition_unfolding,[],[f27,f36,f37,f22])).
% 2.84/0.75  fof(f27,plain,(
% 2.84/0.75    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.84/0.75    inference(cnf_transformation,[],[f3])).
% 2.84/0.75  fof(f3,axiom,(
% 2.84/0.75    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 2.84/0.75    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_enumset1)).
% 2.84/0.75  fof(f169,plain,(
% 2.84/0.75    ( ! [X14,X15,X13] : (k3_tarski(k1_enumset1(k1_enumset1(X15,X15,X13),k1_enumset1(X15,X15,X13),k1_enumset1(X14,X14,X13))) = k3_tarski(k1_enumset1(k1_enumset1(X15,X15,X15),k1_enumset1(X15,X15,X15),k1_enumset1(X13,X13,X14)))) )),
% 2.84/0.75    inference(superposition,[],[f48,f43])).
% 2.84/0.75  fof(f48,plain,(
% 2.84/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4))))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)))) )),
% 2.84/0.75    inference(definition_unfolding,[],[f35,f39,f36,f22])).
% 2.84/0.75  fof(f39,plain,(
% 2.84/0.75    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k1_enumset1(X2,X3,X4)))))) )),
% 2.84/0.75    inference(definition_unfolding,[],[f34,f36,f37,f38])).
% 2.84/0.76  fof(f34,plain,(
% 2.84/0.76    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))) )),
% 2.84/0.76    inference(cnf_transformation,[],[f5])).
% 2.84/0.76  fof(f5,axiom,(
% 2.84/0.76    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k1_tarski(X0),k2_enumset1(X1,X2,X3,X4))),
% 2.84/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_enumset1)).
% 2.84/0.76  fof(f35,plain,(
% 2.84/0.76    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 2.84/0.76    inference(cnf_transformation,[],[f6])).
% 2.84/0.76  fof(f6,axiom,(
% 2.84/0.76    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 2.84/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_enumset1)).
% 2.84/0.76  fof(f94,plain,(
% 2.84/0.76    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_2),
% 2.84/0.76    inference(avatar_component_clause,[],[f92])).
% 2.84/0.76  fof(f95,plain,(
% 2.84/0.76    ~spl5_2 | spl5_1),
% 2.84/0.76    inference(avatar_split_clause,[],[f90,f50,f92])).
% 2.84/0.76  fof(f50,plain,(
% 2.84/0.76    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 2.84/0.76    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.84/0.76  fof(f90,plain,(
% 2.84/0.76    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_1),
% 2.84/0.76    inference(forward_demodulation,[],[f89,f44])).
% 2.84/0.76  fof(f89,plain,(
% 2.84/0.76    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_1),
% 2.84/0.76    inference(forward_demodulation,[],[f52,f44])).
% 2.84/0.76  fof(f52,plain,(
% 2.84/0.76    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_1),
% 2.84/0.76    inference(avatar_component_clause,[],[f50])).
% 2.84/0.76  fof(f53,plain,(
% 2.84/0.76    ~spl5_1),
% 2.84/0.76    inference(avatar_split_clause,[],[f41,f50])).
% 2.84/0.76  fof(f41,plain,(
% 2.84/0.76    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 2.84/0.76    inference(definition_unfolding,[],[f20,f24,f22,f37,f22,f38,f25,f25,f25,f25])).
% 2.84/0.76  fof(f25,plain,(
% 2.84/0.76    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 2.84/0.76    inference(cnf_transformation,[],[f13])).
% 2.84/0.76  fof(f13,axiom,(
% 2.84/0.76    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 2.84/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 2.84/0.76  fof(f24,plain,(
% 2.84/0.76    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 2.84/0.76    inference(cnf_transformation,[],[f14])).
% 2.84/0.76  fof(f14,axiom,(
% 2.84/0.76    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 2.84/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 2.84/0.76  fof(f20,plain,(
% 2.84/0.76    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 2.84/0.76    inference(cnf_transformation,[],[f19])).
% 2.84/0.76  fof(f19,plain,(
% 2.84/0.76    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 2.84/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f17,f18])).
% 2.84/0.76  fof(f18,plain,(
% 2.84/0.76    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 2.84/0.76    introduced(choice_axiom,[])).
% 2.84/0.76  fof(f17,plain,(
% 2.84/0.76    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 2.84/0.76    inference(ennf_transformation,[],[f16])).
% 2.84/0.76  fof(f16,negated_conjecture,(
% 2.84/0.76    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 2.84/0.76    inference(negated_conjecture,[],[f15])).
% 2.84/0.76  fof(f15,conjecture,(
% 2.84/0.76    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 2.84/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 2.84/0.76  % SZS output end Proof for theBenchmark
% 2.84/0.76  % (16691)------------------------------
% 2.84/0.76  % (16691)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.84/0.76  % (16691)Termination reason: Refutation
% 2.84/0.76  
% 2.84/0.76  % (16691)Memory used [KB]: 8571
% 2.84/0.76  % (16691)Time elapsed: 0.327 s
% 2.84/0.76  % (16691)------------------------------
% 2.84/0.76  % (16691)------------------------------
% 2.84/0.76  % (16684)Success in time 0.396 s
%------------------------------------------------------------------------------
