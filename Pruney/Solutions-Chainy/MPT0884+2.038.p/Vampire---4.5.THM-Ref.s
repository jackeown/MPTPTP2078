%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 287 expanded)
%              Number of leaves         :   18 (  99 expanded)
%              Depth                    :   16
%              Number of atoms          :   70 ( 302 expanded)
%              Number of equality atoms :   62 ( 293 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f168])).

fof(f168,plain,(
    spl5_1 ),
    inference(avatar_contradiction_clause,[],[f167])).

fof(f167,plain,
    ( $false
    | spl5_1 ),
    inference(subsumption_resolution,[],[f163,f132])).

fof(f132,plain,(
    ! [X19,X17,X20,X18,X16] : k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k6_enumset1(k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X20),k3_mcart_1(X18,X17,X19),k3_mcart_1(X18,X17,X20)) ),
    inference(forward_demodulation,[],[f131,f57])).

fof(f57,plain,(
    ! [X6,X4,X5] : k4_tarski(k4_tarski(X4,X5),X6) = k3_mcart_1(X4,X5,X6) ),
    inference(forward_demodulation,[],[f55,f24])).

fof(f24,plain,(
    ! [X0,X1] : k1_mcart_1(k4_tarski(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( k2_mcart_1(k4_tarski(X0,X1)) = X1
      & k1_mcart_1(k4_tarski(X0,X1)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

fof(f55,plain,(
    ! [X6,X4,X7,X5] : k4_tarski(k4_tarski(X4,X5),X6) = k1_mcart_1(k4_tarski(k3_mcart_1(X4,X5,X6),X7)) ),
    inference(superposition,[],[f24,f50])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(definition_unfolding,[],[f34,f32])).

fof(f32,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).

fof(f131,plain,(
    ! [X19,X17,X20,X18,X16] : k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k6_enumset1(k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k3_mcart_1(X16,X17,X20),k3_mcart_1(X18,X17,X19),k3_mcart_1(X18,X17,X20)) ),
    inference(forward_demodulation,[],[f130,f57])).

fof(f130,plain,(
    ! [X19,X17,X20,X18,X16] : k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k6_enumset1(k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X20),k3_mcart_1(X18,X17,X19),k3_mcart_1(X18,X17,X20)) ),
    inference(forward_demodulation,[],[f129,f57])).

fof(f129,plain,(
    ! [X19,X17,X20,X18,X16] : k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k6_enumset1(k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X20),k4_tarski(k4_tarski(X18,X17),X19),k3_mcart_1(X18,X17,X20)) ),
    inference(forward_demodulation,[],[f107,f57])).

fof(f107,plain,(
    ! [X19,X17,X20,X18,X16] : k6_enumset1(k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X20),k4_tarski(k4_tarski(X18,X17),X19),k4_tarski(k4_tarski(X18,X17),X20)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) ),
    inference(superposition,[],[f51,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f29,f43,f44,f43])).

fof(f44,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f22,f43])).

fof(f22,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f23,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f33,f40])).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f36,f39])).

fof(f39,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f37,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f36,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f23,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f51,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f35,f43,f43,f41])).

fof(f35,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f163,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4))
    | spl5_1 ),
    inference(superposition,[],[f72,f61])).

fof(f61,plain,(
    ! [X10,X8,X11,X9] : k6_enumset1(X8,X8,X8,X8,X8,X11,X9,X10) = k6_enumset1(X8,X8,X8,X8,X8,X9,X11,X10) ),
    inference(superposition,[],[f49,f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1) ),
    inference(definition_unfolding,[],[f30,f41,f41])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2) ),
    inference(definition_unfolding,[],[f31,f41,f41])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).

fof(f72,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f73,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f45,f70])).

fof(f45,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(definition_unfolding,[],[f21,f26,f43,f44,f43,f41])).

fof(f26,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f21,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:39:46 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.46  % (11371)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (11363)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (11372)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (11364)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (11370)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (11361)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (11358)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (11369)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (11359)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (11369)Refutation not found, incomplete strategy% (11369)------------------------------
% 0.20/0.47  % (11369)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (11369)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (11369)Memory used [KB]: 10618
% 0.20/0.47  % (11369)Time elapsed: 0.063 s
% 0.20/0.47  % (11369)------------------------------
% 0.20/0.47  % (11369)------------------------------
% 0.20/0.48  % (11368)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (11366)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (11373)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (11375)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.49  % (11362)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.49  % (11360)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (11365)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.51  % (11373)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  fof(f169,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f73,f168])).
% 0.20/0.51  fof(f168,plain,(
% 0.20/0.51    spl5_1),
% 0.20/0.51    inference(avatar_contradiction_clause,[],[f167])).
% 0.20/0.51  fof(f167,plain,(
% 0.20/0.51    $false | spl5_1),
% 0.20/0.51    inference(subsumption_resolution,[],[f163,f132])).
% 0.20/0.51  fof(f132,plain,(
% 0.20/0.51    ( ! [X19,X17,X20,X18,X16] : (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k6_enumset1(k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X19),k3_mcart_1(X16,X17,X20),k3_mcart_1(X18,X17,X19),k3_mcart_1(X18,X17,X20))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f131,f57])).
% 0.20/0.51  fof(f57,plain,(
% 0.20/0.51    ( ! [X6,X4,X5] : (k4_tarski(k4_tarski(X4,X5),X6) = k3_mcart_1(X4,X5,X6)) )),
% 0.20/0.51    inference(forward_demodulation,[],[f55,f24])).
% 0.20/0.51  fof(f24,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_mcart_1(k4_tarski(X0,X1)) = X0) )),
% 0.20/0.51    inference(cnf_transformation,[],[f15])).
% 0.20/0.51  fof(f15,axiom,(
% 0.20/0.51    ! [X0,X1] : (k2_mcart_1(k4_tarski(X0,X1)) = X1 & k1_mcart_1(k4_tarski(X0,X1)) = X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).
% 0.20/0.51  fof(f55,plain,(
% 0.20/0.51    ( ! [X6,X4,X7,X5] : (k4_tarski(k4_tarski(X4,X5),X6) = k1_mcart_1(k4_tarski(k3_mcart_1(X4,X5,X6),X7))) )),
% 0.20/0.51    inference(superposition,[],[f24,f50])).
% 0.20/0.51  fof(f50,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_tarski(k3_mcart_1(X0,X1,X2),X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f34,f32])).
% 0.20/0.51  fof(f32,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f13])).
% 0.20/0.51  fof(f13,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_mcart_1)).
% 0.20/0.51  fof(f34,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f14])).
% 0.20/0.51  fof(f14,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k4_tarski(k4_tarski(X0,X1),X2),X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_mcart_1)).
% 0.20/0.51  fof(f131,plain,(
% 0.20/0.51    ( ! [X19,X17,X20,X18,X16] : (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k6_enumset1(k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k3_mcart_1(X16,X17,X20),k3_mcart_1(X18,X17,X19),k3_mcart_1(X18,X17,X20))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f130,f57])).
% 0.20/0.51  fof(f130,plain,(
% 0.20/0.51    ( ! [X19,X17,X20,X18,X16] : (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k6_enumset1(k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X20),k3_mcart_1(X18,X17,X19),k3_mcart_1(X18,X17,X20))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f129,f57])).
% 0.20/0.51  fof(f129,plain,(
% 0.20/0.51    ( ! [X19,X17,X20,X18,X16] : (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20)) = k6_enumset1(k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X20),k4_tarski(k4_tarski(X18,X17),X19),k3_mcart_1(X18,X17,X20))) )),
% 0.20/0.51    inference(forward_demodulation,[],[f107,f57])).
% 0.20/0.51  fof(f107,plain,(
% 0.20/0.51    ( ! [X19,X17,X20,X18,X16] : (k6_enumset1(k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X19),k4_tarski(k4_tarski(X16,X17),X20),k4_tarski(k4_tarski(X18,X17),X19),k4_tarski(k4_tarski(X18,X17),X20)) = k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X16,X16,X16,X16,X16,X16,X16,X18),k6_enumset1(X17,X17,X17,X17,X17,X17,X17,X17)),k6_enumset1(X19,X19,X19,X19,X19,X19,X19,X20))) )),
% 0.20/0.51    inference(superposition,[],[f51,f46])).
% 0.20/0.51  fof(f46,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f29,f43,f44,f43])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f22,f43])).
% 0.20/0.51  fof(f22,plain,(
% 0.20/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f3])).
% 0.20/0.51  fof(f3,axiom,(
% 0.20/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.51  fof(f43,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f23,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f27,f41])).
% 0.20/0.51  fof(f41,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f33,f40])).
% 0.20/0.51  fof(f40,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f36,f39])).
% 0.20/0.51  fof(f39,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f37,f38])).
% 0.20/0.51  fof(f38,plain,(
% 0.20/0.51    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f9])).
% 0.20/0.51  fof(f9,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.51  fof(f37,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f8])).
% 0.20/0.51  fof(f8,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.51  fof(f36,plain,(
% 0.20/0.51    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f7])).
% 0.20/0.51  fof(f7,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.51  fof(f33,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.51  fof(f27,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f5])).
% 0.20/0.51  fof(f5,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.51  fof(f23,plain,(
% 0.20/0.51    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f4])).
% 0.20/0.51  fof(f4,axiom,(
% 0.20/0.51    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.51  fof(f29,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f11])).
% 0.20/0.51  fof(f11,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.20/0.51  fof(f51,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.20/0.51    inference(definition_unfolding,[],[f35,f43,f43,f41])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.20/0.51    inference(cnf_transformation,[],[f10])).
% 0.20/0.51  fof(f10,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 0.20/0.51  fof(f163,plain,(
% 0.20/0.51    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK1,sK2,sK4)) | spl5_1),
% 0.20/0.51    inference(superposition,[],[f72,f61])).
% 0.20/0.51  fof(f61,plain,(
% 0.20/0.51    ( ! [X10,X8,X11,X9] : (k6_enumset1(X8,X8,X8,X8,X8,X11,X9,X10) = k6_enumset1(X8,X8,X8,X8,X8,X9,X11,X10)) )),
% 0.20/0.51    inference(superposition,[],[f49,f48])).
% 0.20/0.51  fof(f48,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X3,X1)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f30,f41,f41])).
% 0.20/0.51  fof(f30,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f2])).
% 0.20/0.51  fof(f2,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X3,X1)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_enumset1)).
% 0.20/0.51  fof(f49,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X3,X2)) )),
% 0.20/0.51    inference(definition_unfolding,[],[f31,f41,f41])).
% 0.20/0.51  fof(f31,plain,(
% 0.20/0.51    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f1])).
% 0.20/0.51  fof(f1,axiom,(
% 0.20/0.51    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X1,X3,X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_enumset1)).
% 0.20/0.51  fof(f72,plain,(
% 0.20/0.51    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) | spl5_1),
% 0.20/0.51    inference(avatar_component_clause,[],[f70])).
% 0.20/0.51  fof(f70,plain,(
% 0.20/0.51    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) = k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.51  fof(f73,plain,(
% 0.20/0.51    ~spl5_1),
% 0.20/0.51    inference(avatar_split_clause,[],[f45,f70])).
% 0.20/0.51  fof(f45,plain,(
% 0.20/0.51    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.20/0.51    inference(definition_unfolding,[],[f21,f26,f43,f44,f43,f41])).
% 0.20/0.51  fof(f26,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f12])).
% 0.20/0.51  fof(f12,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.51  fof(f21,plain,(
% 0.20/0.51    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.20/0.51    inference(cnf_transformation,[],[f20])).
% 0.20/0.51  fof(f20,plain,(
% 0.20/0.51    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f18,f19])).
% 0.20/0.51  fof(f19,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.20/0.51    introduced(choice_axiom,[])).
% 0.20/0.51  fof(f18,plain,(
% 0.20/0.51    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 0.20/0.51    inference(ennf_transformation,[],[f17])).
% 0.20/0.51  fof(f17,negated_conjecture,(
% 0.20/0.51    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 0.20/0.51    inference(negated_conjecture,[],[f16])).
% 0.20/0.51  fof(f16,conjecture,(
% 0.20/0.51    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
% 0.20/0.51  % SZS output end Proof for theBenchmark
% 0.20/0.51  % (11373)------------------------------
% 0.20/0.51  % (11373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (11373)Termination reason: Refutation
% 0.20/0.51  
% 0.20/0.51  % (11373)Memory used [KB]: 10874
% 0.20/0.51  % (11373)Time elapsed: 0.087 s
% 0.20/0.51  % (11373)------------------------------
% 0.20/0.51  % (11373)------------------------------
% 0.20/0.51  % (11355)Success in time 0.148 s
%------------------------------------------------------------------------------
