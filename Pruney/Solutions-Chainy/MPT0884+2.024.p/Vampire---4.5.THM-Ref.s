%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:58:58 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 280 expanded)
%              Number of leaves         :   17 ( 109 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 305 expanded)
%              Number of equality atoms :   60 ( 280 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1023,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f50,f67,f334,f1022])).

fof(f1022,plain,(
    spl5_3 ),
    inference(avatar_contradiction_clause,[],[f1021])).

fof(f1021,plain,
    ( $false
    | spl5_3 ),
    inference(trivial_inequality_removal,[],[f1020])).

fof(f1020,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4))
    | spl5_3 ),
    inference(forward_demodulation,[],[f1013,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f28,f21,f38,f21])).

fof(f38,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f20,f21])).

fof(f20,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f21,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f28,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).

fof(f1013,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4))
    | spl5_3 ),
    inference(superposition,[],[f333,f99])).

fof(f99,plain,(
    ! [X4,X2,X0,X3,X1] : k2_zfmisc_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),X2),k1_enumset1(X3,X3,X4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k1_enumset1(X3,X3,X3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k1_enumset1(X3,X3,X3)),k1_enumset1(k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X2,X3),k4_tarski(X2,X4)))) ),
    inference(superposition,[],[f98,f42])).

fof(f98,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)))) ),
    inference(forward_demodulation,[],[f45,f42])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)))) ),
    inference(definition_unfolding,[],[f31,f21,f21,f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) ),
    inference(definition_unfolding,[],[f29,f35])).

fof(f35,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4))) ),
    inference(definition_unfolding,[],[f32,f34,f21])).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f22,f21])).

fof(f22,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f32,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).

fof(f29,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f31,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f333,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_3 ),
    inference(avatar_component_clause,[],[f331])).

fof(f331,plain,
    ( spl5_3
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f334,plain,
    ( ~ spl5_3
    | spl5_2 ),
    inference(avatar_split_clause,[],[f307,f64,f331])).

fof(f64,plain,
    ( spl5_2
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f307,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_2 ),
    inference(backward_demodulation,[],[f66,f287])).

fof(f287,plain,(
    ! [X10,X11,X9] : k1_enumset1(X9,X10,X11) = k1_enumset1(X10,X9,X11) ),
    inference(superposition,[],[f107,f80])).

fof(f80,plain,(
    ! [X6,X7,X5] : k1_enumset1(X6,X5,X7) = k3_tarski(k1_enumset1(k1_enumset1(X5,X5,X5),k1_enumset1(X5,X5,X5),k1_enumset1(X6,X7,X6))) ),
    inference(superposition,[],[f44,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0))) ),
    inference(definition_unfolding,[],[f26,f34,f21,f21])).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3))) ),
    inference(definition_unfolding,[],[f30,f36,f34,f21,f21])).

fof(f30,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

fof(f107,plain,(
    ! [X19,X20,X18] : k1_enumset1(X20,X18,X19) = k3_tarski(k1_enumset1(k1_enumset1(X20,X20,X20),k1_enumset1(X20,X20,X20),k1_enumset1(X18,X19,X18))) ),
    inference(superposition,[],[f72,f93])).

fof(f93,plain,(
    ! [X8,X9] : k1_enumset1(X8,X8,X9) = k1_enumset1(X8,X9,X8) ),
    inference(superposition,[],[f72,f41])).

fof(f72,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2))) ),
    inference(superposition,[],[f44,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2))) ),
    inference(definition_unfolding,[],[f24,f36])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f66,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_2 ),
    inference(avatar_component_clause,[],[f64])).

fof(f67,plain,
    ( ~ spl5_2
    | spl5_1 ),
    inference(avatar_split_clause,[],[f62,f47,f64])).

fof(f47,plain,
    ( spl5_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f62,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f61,f42])).

fof(f61,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_1 ),
    inference(forward_demodulation,[],[f49,f42])).

fof(f49,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f47])).

fof(f50,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f40,f47])).

fof(f40,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) ),
    inference(definition_unfolding,[],[f19,f23,f21,f38,f21,f36,f25,f25,f25,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f19,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (10311)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.45  % (10303)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (10302)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (10307)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.47  % (10301)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.48  % (10310)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (10309)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (10310)Refutation not found, incomplete strategy% (10310)------------------------------
% 0.20/0.48  % (10310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (10310)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (10310)Memory used [KB]: 10618
% 0.20/0.48  % (10310)Time elapsed: 0.072 s
% 0.20/0.48  % (10310)------------------------------
% 0.20/0.48  % (10310)------------------------------
% 0.20/0.48  % (10300)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (10305)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (10313)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (10306)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (10304)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.50  % (10299)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.50  % (10312)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.50  % (10316)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (10315)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (10314)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.51  % (10308)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.63/0.58  % (10305)Refutation found. Thanks to Tanya!
% 1.63/0.58  % SZS status Theorem for theBenchmark
% 1.63/0.58  % SZS output start Proof for theBenchmark
% 1.63/0.58  fof(f1023,plain,(
% 1.63/0.58    $false),
% 1.63/0.58    inference(avatar_sat_refutation,[],[f50,f67,f334,f1022])).
% 1.63/0.58  fof(f1022,plain,(
% 1.63/0.58    spl5_3),
% 1.63/0.58    inference(avatar_contradiction_clause,[],[f1021])).
% 1.63/0.58  fof(f1021,plain,(
% 1.63/0.58    $false | spl5_3),
% 1.63/0.58    inference(trivial_inequality_removal,[],[f1020])).
% 1.63/0.58  fof(f1020,plain,(
% 1.63/0.58    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) | spl5_3),
% 1.63/0.58    inference(forward_demodulation,[],[f1013,f42])).
% 1.63/0.58  fof(f42,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X2)) = k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.63/0.58    inference(definition_unfolding,[],[f28,f21,f38,f21])).
% 1.63/0.58  fof(f38,plain,(
% 1.63/0.58    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 1.63/0.58    inference(definition_unfolding,[],[f20,f21])).
% 1.63/0.58  fof(f20,plain,(
% 1.63/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f5])).
% 1.63/0.58  fof(f5,axiom,(
% 1.63/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.63/0.58  fof(f21,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f6])).
% 1.63/0.58  fof(f6,axiom,(
% 1.63/0.58    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.63/0.58  fof(f28,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f11])).
% 1.63/0.58  fof(f11,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 1.63/0.58  fof(f1013,plain,(
% 1.63/0.58    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK1,sK2)),k1_enumset1(sK3,sK3,sK4)) | spl5_3),
% 1.63/0.58    inference(superposition,[],[f333,f99])).
% 1.63/0.58  fof(f99,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (k2_zfmisc_1(k1_enumset1(k4_tarski(X0,X1),k4_tarski(X0,X1),X2),k1_enumset1(X3,X3,X4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k1_enumset1(X3,X3,X3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X1)),k1_enumset1(X3,X3,X3)),k1_enumset1(k4_tarski(k4_tarski(X0,X1),X4),k4_tarski(X2,X3),k4_tarski(X2,X4))))) )),
% 1.63/0.58    inference(superposition,[],[f98,f42])).
% 1.63/0.58  fof(f98,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k2_zfmisc_1(k1_enumset1(X0,X0,X0),k1_enumset1(X2,X2,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))))) )),
% 1.63/0.58    inference(forward_demodulation,[],[f45,f42])).
% 1.63/0.58  fof(f45,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2)),k1_enumset1(k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))))) )),
% 1.63/0.58    inference(definition_unfolding,[],[f31,f21,f21,f36])).
% 1.63/0.58  fof(f36,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3)))) )),
% 1.63/0.58    inference(definition_unfolding,[],[f29,f35])).
% 1.63/0.58  fof(f35,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X3,X4)))) )),
% 1.63/0.58    inference(definition_unfolding,[],[f32,f34,f21])).
% 1.63/0.58  fof(f34,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 1.63/0.58    inference(definition_unfolding,[],[f22,f21])).
% 1.63/0.58  fof(f22,plain,(
% 1.63/0.58    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f9])).
% 1.63/0.58  fof(f9,axiom,(
% 1.63/0.58    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.63/0.58  fof(f32,plain,(
% 1.63/0.58    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f3])).
% 1.63/0.58  fof(f3,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k2_xboole_0(k2_tarski(X0,X1),k1_enumset1(X2,X3,X4))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_enumset1)).
% 1.63/0.58  fof(f29,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f8])).
% 1.63/0.58  fof(f8,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.63/0.58  fof(f31,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f10])).
% 1.63/0.58  fof(f10,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 1.63/0.58  fof(f333,plain,(
% 1.63/0.58    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_3),
% 1.63/0.58    inference(avatar_component_clause,[],[f331])).
% 1.63/0.58  fof(f331,plain,(
% 1.63/0.58    spl5_3 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.63/0.58  fof(f334,plain,(
% 1.63/0.58    ~spl5_3 | spl5_2),
% 1.63/0.58    inference(avatar_split_clause,[],[f307,f64,f331])).
% 1.63/0.58  fof(f64,plain,(
% 1.63/0.58    spl5_2 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.63/0.58  fof(f307,plain,(
% 1.63/0.58    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_2),
% 1.63/0.58    inference(backward_demodulation,[],[f66,f287])).
% 1.63/0.58  fof(f287,plain,(
% 1.63/0.58    ( ! [X10,X11,X9] : (k1_enumset1(X9,X10,X11) = k1_enumset1(X10,X9,X11)) )),
% 1.63/0.58    inference(superposition,[],[f107,f80])).
% 1.63/0.58  fof(f80,plain,(
% 1.63/0.58    ( ! [X6,X7,X5] : (k1_enumset1(X6,X5,X7) = k3_tarski(k1_enumset1(k1_enumset1(X5,X5,X5),k1_enumset1(X5,X5,X5),k1_enumset1(X6,X7,X6)))) )),
% 1.63/0.58    inference(superposition,[],[f44,f41])).
% 1.63/0.58  fof(f41,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X0),k1_enumset1(X1,X1,X0),k1_enumset1(X2,X2,X0)))) )),
% 1.63/0.58    inference(definition_unfolding,[],[f26,f34,f21,f21])).
% 1.63/0.58  fof(f26,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f2])).
% 1.63/0.58  fof(f2,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : k2_xboole_0(k2_tarski(X1,X0),k2_tarski(X2,X0)) = k1_enumset1(X0,X1,X2)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t137_enumset1)).
% 1.63/0.58  fof(f44,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X2,X3))) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k1_enumset1(X2,X2,X3)))) )),
% 1.63/0.58    inference(definition_unfolding,[],[f30,f36,f34,f21,f21])).
% 1.63/0.58  fof(f30,plain,(
% 1.63/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))) )),
% 1.63/0.58    inference(cnf_transformation,[],[f1])).
% 1.63/0.58  fof(f1,axiom,(
% 1.63/0.58    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).
% 1.63/0.58  fof(f107,plain,(
% 1.63/0.58    ( ! [X19,X20,X18] : (k1_enumset1(X20,X18,X19) = k3_tarski(k1_enumset1(k1_enumset1(X20,X20,X20),k1_enumset1(X20,X20,X20),k1_enumset1(X18,X19,X18)))) )),
% 1.63/0.58    inference(superposition,[],[f72,f93])).
% 1.63/0.58  fof(f93,plain,(
% 1.63/0.58    ( ! [X8,X9] : (k1_enumset1(X8,X8,X9) = k1_enumset1(X8,X9,X8)) )),
% 1.63/0.58    inference(superposition,[],[f72,f41])).
% 1.63/0.58  fof(f72,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X1,X1,X2)))) )),
% 1.63/0.58    inference(superposition,[],[f44,f39])).
% 1.63/0.58  fof(f39,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k1_enumset1(X0,X1,X2)))) )),
% 1.63/0.58    inference(definition_unfolding,[],[f24,f36])).
% 1.63/0.58  fof(f24,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f7])).
% 1.63/0.58  fof(f7,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.63/0.58  fof(f66,plain,(
% 1.63/0.58    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_2),
% 1.63/0.58    inference(avatar_component_clause,[],[f64])).
% 1.63/0.58  fof(f67,plain,(
% 1.63/0.58    ~spl5_2 | spl5_1),
% 1.63/0.58    inference(avatar_split_clause,[],[f62,f47,f64])).
% 1.63/0.58  fof(f47,plain,(
% 1.63/0.58    spl5_1 <=> k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) = k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 1.63/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.63/0.58  fof(f62,plain,(
% 1.63/0.58    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_1),
% 1.63/0.58    inference(forward_demodulation,[],[f61,f42])).
% 1.63/0.58  fof(f61,plain,(
% 1.63/0.58    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k2_zfmisc_1(k1_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK2),k4_tarski(sK0,sK2)),k1_enumset1(sK3,sK3,sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_1),
% 1.63/0.58    inference(forward_demodulation,[],[f49,f42])).
% 1.63/0.58  fof(f49,plain,(
% 1.63/0.58    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)))) | spl5_1),
% 1.63/0.58    inference(avatar_component_clause,[],[f47])).
% 1.63/0.58  fof(f50,plain,(
% 1.63/0.58    ~spl5_1),
% 1.63/0.58    inference(avatar_split_clause,[],[f40,f47])).
% 1.63/0.58  fof(f40,plain,(
% 1.63/0.58    k2_zfmisc_1(k2_zfmisc_1(k1_enumset1(sK0,sK0,sK1),k1_enumset1(sK2,sK2,sK2)),k1_enumset1(sK3,sK3,sK4)) != k3_tarski(k1_enumset1(k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3)),k1_enumset1(k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))))),
% 1.63/0.58    inference(definition_unfolding,[],[f19,f23,f21,f38,f21,f36,f25,f25,f25,f25])).
% 1.63/0.58  fof(f25,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f12])).
% 1.63/0.58  fof(f12,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).
% 1.63/0.58  fof(f23,plain,(
% 1.63/0.58    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 1.63/0.58    inference(cnf_transformation,[],[f13])).
% 1.63/0.58  fof(f13,axiom,(
% 1.63/0.58    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 1.63/0.58  fof(f19,plain,(
% 1.63/0.58    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 1.63/0.58    inference(cnf_transformation,[],[f18])).
% 1.63/0.58  fof(f18,plain,(
% 1.63/0.58    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 1.63/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f16,f17])).
% 1.63/0.58  fof(f17,plain,(
% 1.63/0.58    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 1.63/0.58    introduced(choice_axiom,[])).
% 1.63/0.58  fof(f16,plain,(
% 1.63/0.58    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 1.63/0.58    inference(ennf_transformation,[],[f15])).
% 1.63/0.58  fof(f15,negated_conjecture,(
% 1.63/0.58    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 1.63/0.58    inference(negated_conjecture,[],[f14])).
% 1.63/0.58  fof(f14,conjecture,(
% 1.63/0.58    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 1.63/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_mcart_1)).
% 1.63/0.58  % SZS output end Proof for theBenchmark
% 1.63/0.58  % (10305)------------------------------
% 1.63/0.58  % (10305)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.58  % (10305)Termination reason: Refutation
% 1.63/0.58  
% 1.63/0.58  % (10305)Memory used [KB]: 7547
% 1.63/0.58  % (10305)Time elapsed: 0.168 s
% 1.63/0.58  % (10305)------------------------------
% 1.63/0.58  % (10305)------------------------------
% 1.63/0.59  % (10298)Success in time 0.234 s
%------------------------------------------------------------------------------
