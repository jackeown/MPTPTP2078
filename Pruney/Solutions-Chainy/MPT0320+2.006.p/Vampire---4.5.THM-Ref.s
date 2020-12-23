%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:27 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 303 expanded)
%              Number of leaves         :   13 ( 104 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 ( 322 expanded)
%              Number of equality atoms :   57 ( 312 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f52])).

fof(f52,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f51])).

fof(f51,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f50])).

fof(f50,plain,
    ( k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | spl3_1 ),
    inference(forward_demodulation,[],[f49,f35])).

fof(f35,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f26,f34])).

fof(f34,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X7))) ),
    inference(definition_unfolding,[],[f27,f32,f33])).

fof(f33,plain,(
    ! [X0] : k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f17,f31])).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f19,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f20,f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f23,f28])).

fof(f28,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f24,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f19,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f17,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f18,f31])).

fof(f18,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f27,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).

fof(f26,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f49,plain,
    ( k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | spl3_1 ),
    inference(superposition,[],[f47,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f21,f32,f32])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f47,plain,
    ( k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl3_1
  <=> k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f48,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f41,f45])).

fof(f41,plain,(
    k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(trivial_inequality_removal,[],[f40])).

fof(f40,plain,
    ( k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(forward_demodulation,[],[f39,f35])).

fof(f39,plain,
    ( k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(backward_demodulation,[],[f36,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k5_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f22,f32,f32])).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f36,plain,
    ( k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k3_tarski(k5_enumset1(k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))))
    | k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f16,f31,f32,f33,f33,f31,f32,f33,f33])).

fof(f16,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
      | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:00:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (16315)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.44  % (16315)Refutation found. Thanks to Tanya!
% 0.22/0.44  % SZS status Theorem for theBenchmark
% 0.22/0.44  % SZS output start Proof for theBenchmark
% 0.22/0.44  fof(f53,plain,(
% 0.22/0.44    $false),
% 0.22/0.44    inference(avatar_sat_refutation,[],[f48,f52])).
% 0.22/0.44  fof(f52,plain,(
% 0.22/0.44    spl3_1),
% 0.22/0.44    inference(avatar_contradiction_clause,[],[f51])).
% 0.22/0.44  fof(f51,plain,(
% 0.22/0.44    $false | spl3_1),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f50])).
% 0.22/0.44  fof(f50,plain,(
% 0.22/0.44    k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | spl3_1),
% 0.22/0.44    inference(forward_demodulation,[],[f49,f35])).
% 0.22/0.44  fof(f35,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k5_enumset1(k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X0,X0,X1,X2,X3,X4,X5),k5_enumset1(X6,X6,X6,X6,X6,X6,X6)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f26,f34])).
% 0.22/0.44  fof(f34,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k5_enumset1(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k5_enumset1(X7,X7,X7,X7,X7,X7,X7)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f27,f32,f33])).
% 0.22/0.44  fof(f33,plain,(
% 0.22/0.44    ( ! [X0] : (k1_tarski(X0) = k5_enumset1(X0,X0,X0,X0,X0,X0,X0)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f17,f31])).
% 0.22/0.44  fof(f31,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f19,f30])).
% 0.22/0.44  fof(f30,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f20,f29])).
% 0.22/0.44  fof(f29,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f23,f28])).
% 0.22/0.44  fof(f28,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.22/0.44    inference(definition_unfolding,[],[f24,f25])).
% 0.22/0.44  fof(f25,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f7])).
% 0.22/0.44  fof(f7,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.22/0.44  fof(f24,plain,(
% 0.22/0.44    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f6])).
% 0.22/0.44  fof(f6,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.22/0.44  fof(f23,plain,(
% 0.22/0.44    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f5])).
% 0.22/0.44  fof(f5,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.22/0.44  fof(f20,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f4])).
% 0.22/0.44  fof(f4,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.22/0.44  fof(f19,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f3])).
% 0.22/0.44  fof(f3,axiom,(
% 0.22/0.44    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.22/0.44  fof(f17,plain,(
% 0.22/0.44    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f2])).
% 0.22/0.44  fof(f2,axiom,(
% 0.22/0.44    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.44  fof(f32,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f18,f31])).
% 0.22/0.44  fof(f18,plain,(
% 0.22/0.44    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f9])).
% 0.22/0.44  fof(f9,axiom,(
% 0.22/0.44    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.22/0.44  fof(f27,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f1])).
% 0.22/0.44  fof(f1,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k5_enumset1(X0,X1,X2,X3,X4,X5,X6),k1_tarski(X7))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_enumset1)).
% 0.22/0.44  fof(f26,plain,(
% 0.22/0.44    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 0.22/0.44    inference(cnf_transformation,[],[f8])).
% 0.22/0.44  fof(f8,axiom,(
% 0.22/0.44    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.22/0.44  fof(f49,plain,(
% 0.22/0.44    k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1))),sK2) | spl3_1),
% 0.22/0.44    inference(superposition,[],[f47,f38])).
% 0.22/0.44  fof(f38,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f21,f32,f32])).
% 0.22/0.44  fof(f21,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f10,axiom,(
% 0.22/0.44    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.22/0.44  fof(f47,plain,(
% 0.22/0.44    k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2))) | spl3_1),
% 0.22/0.44    inference(avatar_component_clause,[],[f45])).
% 0.22/0.44  fof(f45,plain,(
% 0.22/0.44    spl3_1 <=> k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.22/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.22/0.44  fof(f48,plain,(
% 0.22/0.44    ~spl3_1),
% 0.22/0.44    inference(avatar_split_clause,[],[f41,f45])).
% 0.22/0.44  fof(f41,plain,(
% 0.22/0.44    k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.22/0.44    inference(trivial_inequality_removal,[],[f40])).
% 0.22/0.44  fof(f40,plain,(
% 0.22/0.44    k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.22/0.44    inference(forward_demodulation,[],[f39,f35])).
% 0.22/0.44  fof(f39,plain,(
% 0.22/0.44    k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k3_tarski(k5_enumset1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.22/0.44    inference(backward_demodulation,[],[f36,f37])).
% 0.22/0.44  fof(f37,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) = k3_tarski(k5_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 0.22/0.44    inference(definition_unfolding,[],[f22,f32,f32])).
% 0.22/0.44  fof(f22,plain,(
% 0.22/0.44    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.22/0.44    inference(cnf_transformation,[],[f10])).
% 0.22/0.44  fof(f36,plain,(
% 0.22/0.44    k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) != k3_tarski(k5_enumset1(k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1)))) | k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k5_enumset1(k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k5_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.22/0.44    inference(definition_unfolding,[],[f16,f31,f32,f33,f33,f31,f32,f33,f33])).
% 0.22/0.44  fof(f16,plain,(
% 0.22/0.44    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.22/0.44    inference(cnf_transformation,[],[f15])).
% 0.22/0.44  fof(f15,plain,(
% 0.22/0.44    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.22/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 0.22/0.44  fof(f14,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))) => (k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 0.22/0.44    introduced(choice_axiom,[])).
% 0.22/0.44  fof(f13,plain,(
% 0.22/0.44    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.44    inference(ennf_transformation,[],[f12])).
% 0.22/0.44  fof(f12,negated_conjecture,(
% 0.22/0.44    ~! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.44    inference(negated_conjecture,[],[f11])).
% 0.22/0.44  fof(f11,conjecture,(
% 0.22/0.44    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.22/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).
% 0.22/0.44  % SZS output end Proof for theBenchmark
% 0.22/0.44  % (16315)------------------------------
% 0.22/0.44  % (16315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.44  % (16315)Termination reason: Refutation
% 0.22/0.44  
% 0.22/0.44  % (16315)Memory used [KB]: 10618
% 0.22/0.44  % (16315)Time elapsed: 0.028 s
% 0.22/0.44  % (16315)------------------------------
% 0.22/0.44  % (16315)------------------------------
% 0.22/0.45  % (16299)Success in time 0.084 s
%------------------------------------------------------------------------------
