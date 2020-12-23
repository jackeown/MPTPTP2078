%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:40 EST 2020

% Result     : Theorem 1.57s
% Output     : Refutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 190 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :   22
%              Number of atoms          :  125 ( 233 expanded)
%              Number of equality atoms :   34 ( 127 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2469,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1097,f1101,f1105,f2468])).

fof(f2468,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f2465])).

fof(f2465,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f2464,f51])).

fof(f51,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X2,X1),X1) ),
    inference(superposition,[],[f29,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f2464,plain,
    ( ~ r1_tarski(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl2_6 ),
    inference(resolution,[],[f2345,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

fof(f2345,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_6 ),
    inference(resolution,[],[f1092,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f1092,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f1090])).

fof(f1090,plain,
    ( spl2_6
  <=> r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f1105,plain,
    ( ~ spl2_1
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f1104])).

fof(f1104,plain,
    ( $false
    | ~ spl2_1
    | spl2_5 ),
    inference(resolution,[],[f1102,f1088])).

fof(f1088,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f1086])).

fof(f1086,plain,
    ( spl2_5
  <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f1102,plain,
    ( r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ spl2_1 ),
    inference(forward_demodulation,[],[f186,f206])).

fof(f206,plain,(
    ! [X2,X1] : k5_xboole_0(X2,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,k5_xboole_0(X2,X1)) ),
    inference(superposition,[],[f86,f30])).

fof(f86,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f74,f30])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f39,f28])).

fof(f28,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f39,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f186,plain,
    ( r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl2_1
  <=> r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1101,plain,
    ( ~ spl2_6
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f1100,f1086,f1090])).

fof(f1100,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1099,f206])).

fof(f1099,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f1098,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f1098,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f229,f206])).

fof(f229,plain,
    ( ~ r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(resolution,[],[f221,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k5_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k5_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

fof(f221,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f220,f31])).

fof(f220,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f219,f31])).

fof(f219,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f218,f86])).

fof(f218,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f204,f31])).

fof(f204,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(backward_demodulation,[],[f182,f86])).

fof(f182,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f181,f30])).

fof(f181,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f180,f65])).

fof(f65,plain,(
    ! [X4,X5,X3] : k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4)) ),
    inference(superposition,[],[f38,f31])).

fof(f38,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f180,plain,(
    ~ r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k5_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f179,f65])).

fof(f179,plain,(
    ~ r1_tarski(k5_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f178,f31])).

fof(f178,plain,(
    ~ r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(forward_demodulation,[],[f48,f49])).

fof(f49,plain,(
    ! [X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f32,f46])).

fof(f46,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f33,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f37,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f48,plain,(
    ~ r1_tarski(k3_tarski(k4_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f27,f47,f34,f34])).

fof(f34,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f27,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).

fof(f25,plain,
    ( ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))
   => ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1] : ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

fof(f1097,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f1094])).

fof(f1094,plain,
    ( $false
    | spl2_1 ),
    inference(resolution,[],[f1015,f51])).

fof(f1015,plain,
    ( ~ r1_tarski(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(backward_demodulation,[],[f193,f206])).

fof(f193,plain,
    ( ~ r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(resolution,[],[f187,f36])).

fof(f187,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:59:30 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.45  % (25640)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.46  % (25649)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (25649)Refutation not found, incomplete strategy% (25649)------------------------------
% 0.22/0.47  % (25649)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (25649)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (25649)Memory used [KB]: 10618
% 0.22/0.47  % (25649)Time elapsed: 0.005 s
% 0.22/0.47  % (25649)------------------------------
% 0.22/0.47  % (25649)------------------------------
% 0.22/0.47  % (25642)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (25646)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.47  % (25643)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.48  % (25647)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.48  % (25652)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.48  % (25650)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (25651)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (25638)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (25641)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.49  % (25655)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.49  % (25654)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.50  % (25645)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (25644)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (25648)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.51  % (25639)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.53  % (25653)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.57/0.58  % (25642)Refutation found. Thanks to Tanya!
% 1.57/0.58  % SZS status Theorem for theBenchmark
% 1.57/0.58  % SZS output start Proof for theBenchmark
% 1.57/0.58  fof(f2469,plain,(
% 1.57/0.58    $false),
% 1.57/0.58    inference(avatar_sat_refutation,[],[f1097,f1101,f1105,f2468])).
% 1.57/0.58  fof(f2468,plain,(
% 1.57/0.58    spl2_6),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f2465])).
% 1.57/0.58  fof(f2465,plain,(
% 1.57/0.58    $false | spl2_6),
% 1.57/0.58    inference(resolution,[],[f2464,f51])).
% 1.57/0.58  fof(f51,plain,(
% 1.57/0.58    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X2,X1),X1)) )),
% 1.57/0.58    inference(superposition,[],[f29,f30])).
% 1.57/0.58  fof(f30,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f1])).
% 1.57/0.58  fof(f1,axiom,(
% 1.57/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.57/0.58  fof(f29,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f8])).
% 1.57/0.58  fof(f8,axiom,(
% 1.57/0.58    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.57/0.58  fof(f2464,plain,(
% 1.57/0.58    ~r1_tarski(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) | spl2_6),
% 1.57/0.58    inference(resolution,[],[f2345,f36])).
% 1.57/0.58  fof(f36,plain,(
% 1.57/0.58    ( ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f21])).
% 1.57/0.58  fof(f21,plain,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 1.57/0.58    inference(ennf_transformation,[],[f16])).
% 1.57/0.58  fof(f16,axiom,(
% 1.57/0.58    ! [X0,X1] : (r1_tarski(X0,X1) => r1_tarski(k1_zfmisc_1(X0),k1_zfmisc_1(X1)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).
% 1.57/0.58  fof(f2345,plain,(
% 1.57/0.58    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_6),
% 1.57/0.58    inference(resolution,[],[f1092,f40])).
% 1.57/0.58  fof(f40,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f22])).
% 1.57/0.58  fof(f22,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.57/0.58    inference(ennf_transformation,[],[f5])).
% 1.57/0.58  fof(f5,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.57/0.58  fof(f1092,plain,(
% 1.57/0.58    ~r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_6),
% 1.57/0.58    inference(avatar_component_clause,[],[f1090])).
% 1.57/0.58  fof(f1090,plain,(
% 1.57/0.58    spl2_6 <=> r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.57/0.58  fof(f1105,plain,(
% 1.57/0.58    ~spl2_1 | spl2_5),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f1104])).
% 1.57/0.58  fof(f1104,plain,(
% 1.57/0.58    $false | (~spl2_1 | spl2_5)),
% 1.57/0.58    inference(resolution,[],[f1102,f1088])).
% 1.57/0.58  fof(f1088,plain,(
% 1.57/0.58    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_5),
% 1.57/0.58    inference(avatar_component_clause,[],[f1086])).
% 1.57/0.58  fof(f1086,plain,(
% 1.57/0.58    spl2_5 <=> r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.57/0.58  fof(f1102,plain,(
% 1.57/0.58    r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~spl2_1),
% 1.57/0.58    inference(forward_demodulation,[],[f186,f206])).
% 1.57/0.58  fof(f206,plain,(
% 1.57/0.58    ( ! [X2,X1] : (k5_xboole_0(X2,k3_xboole_0(X2,X1)) = k3_xboole_0(X2,k5_xboole_0(X2,X1))) )),
% 1.57/0.58    inference(superposition,[],[f86,f30])).
% 1.57/0.58  fof(f86,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.57/0.58    inference(forward_demodulation,[],[f74,f30])).
% 1.57/0.58  fof(f74,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 1.57/0.58    inference(superposition,[],[f39,f28])).
% 1.57/0.58  fof(f28,plain,(
% 1.57/0.58    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.57/0.58    inference(cnf_transformation,[],[f19])).
% 1.57/0.58  fof(f19,plain,(
% 1.57/0.58    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 1.57/0.58    inference(rectify,[],[f3])).
% 1.57/0.58  fof(f3,axiom,(
% 1.57/0.58    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 1.57/0.58  fof(f39,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f7])).
% 1.57/0.58  fof(f7,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 1.57/0.58  fof(f186,plain,(
% 1.57/0.58    r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~spl2_1),
% 1.57/0.58    inference(avatar_component_clause,[],[f185])).
% 1.57/0.58  fof(f185,plain,(
% 1.57/0.58    spl2_1 <=> r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.57/0.58  fof(f1101,plain,(
% 1.57/0.58    ~spl2_6 | ~spl2_5),
% 1.57/0.58    inference(avatar_split_clause,[],[f1100,f1086,f1090])).
% 1.57/0.58  fof(f1100,plain,(
% 1.57/0.58    ~r1_tarski(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f1099,f206])).
% 1.57/0.58  fof(f1099,plain,(
% 1.57/0.58    ~r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f1098,f31])).
% 1.57/0.58  fof(f31,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f2])).
% 1.57/0.58  fof(f2,axiom,(
% 1.57/0.58    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.57/0.58  fof(f1098,plain,(
% 1.57/0.58    ~r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f229,f206])).
% 1.57/0.58  fof(f229,plain,(
% 1.57/0.58    ~r1_tarski(k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(resolution,[],[f221,f41])).
% 1.57/0.58  fof(f41,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f24])).
% 1.57/0.58  fof(f24,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 1.57/0.58    inference(flattening,[],[f23])).
% 1.57/0.58  fof(f23,plain,(
% 1.57/0.58    ! [X0,X1,X2] : (r1_tarski(k5_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 1.57/0.58    inference(ennf_transformation,[],[f6])).
% 1.57/0.58  fof(f6,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k5_xboole_0(X0,X2),X1))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).
% 1.57/0.58  fof(f221,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f220,f31])).
% 1.57/0.58  fof(f220,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))),k5_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f219,f31])).
% 1.57/0.58  fof(f219,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k3_xboole_0(sK1,k5_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f218,f86])).
% 1.57/0.58  fof(f218,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f204,f31])).
% 1.57/0.58  fof(f204,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(backward_demodulation,[],[f182,f86])).
% 1.57/0.58  fof(f182,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f181,f30])).
% 1.57/0.58  fof(f181,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f180,f65])).
% 1.57/0.58  fof(f65,plain,(
% 1.57/0.58    ( ! [X4,X5,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,X5)) = k5_xboole_0(X5,k5_xboole_0(X3,X4))) )),
% 1.57/0.58    inference(superposition,[],[f38,f31])).
% 1.57/0.58  fof(f38,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f9])).
% 1.57/0.58  fof(f9,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.57/0.58  fof(f180,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k5_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f179,f65])).
% 1.57/0.58  fof(f179,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f178,f31])).
% 1.57/0.58  fof(f178,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(k5_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))),k3_xboole_0(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(forward_demodulation,[],[f48,f49])).
% 1.57/0.58  fof(f49,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.57/0.58    inference(definition_unfolding,[],[f35,f47])).
% 1.57/0.58  fof(f47,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.57/0.58    inference(definition_unfolding,[],[f32,f46])).
% 1.57/0.58  fof(f46,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.57/0.58    inference(definition_unfolding,[],[f33,f45])).
% 1.57/0.58  fof(f45,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.57/0.58    inference(definition_unfolding,[],[f37,f44])).
% 1.57/0.58  fof(f44,plain,(
% 1.57/0.58    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.57/0.58    inference(definition_unfolding,[],[f42,f43])).
% 1.57/0.58  fof(f43,plain,(
% 1.57/0.58    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f14])).
% 1.57/0.58  fof(f14,axiom,(
% 1.57/0.58    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.57/0.58  fof(f42,plain,(
% 1.57/0.58    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f13])).
% 1.57/0.58  fof(f13,axiom,(
% 1.57/0.58    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.57/0.58  fof(f37,plain,(
% 1.57/0.58    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f12])).
% 1.57/0.58  fof(f12,axiom,(
% 1.57/0.58    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.57/0.58  fof(f33,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.57/0.58    inference(cnf_transformation,[],[f11])).
% 1.57/0.58  fof(f11,axiom,(
% 1.57/0.58    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.57/0.58  fof(f32,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f15])).
% 1.57/0.58  fof(f15,axiom,(
% 1.57/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.57/0.58  fof(f35,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f10])).
% 1.57/0.58  fof(f10,axiom,(
% 1.57/0.58    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 1.57/0.58  fof(f48,plain,(
% 1.57/0.58    ~r1_tarski(k3_tarski(k4_enumset1(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(definition_unfolding,[],[f27,f47,f34,f34])).
% 1.57/0.58  fof(f34,plain,(
% 1.57/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.57/0.58    inference(cnf_transformation,[],[f4])).
% 1.57/0.58  fof(f4,axiom,(
% 1.57/0.58    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.57/0.58  fof(f27,plain,(
% 1.57/0.58    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(cnf_transformation,[],[f26])).
% 1.57/0.58  fof(f26,plain,(
% 1.57/0.58    ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f25])).
% 1.57/0.58  fof(f25,plain,(
% 1.57/0.58    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1))) => ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(sK0,sK1)),k1_zfmisc_1(k4_xboole_0(sK1,sK0))),k1_zfmisc_1(k5_xboole_0(sK0,sK1)))),
% 1.57/0.58    introduced(choice_axiom,[])).
% 1.57/0.58  fof(f20,plain,(
% 1.57/0.58    ? [X0,X1] : ~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.57/0.58    inference(ennf_transformation,[],[f18])).
% 1.57/0.58  fof(f18,negated_conjecture,(
% 1.57/0.58    ~! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.57/0.58    inference(negated_conjecture,[],[f17])).
% 1.57/0.58  fof(f17,conjecture,(
% 1.57/0.58    ! [X0,X1] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(X0,X1)),k1_zfmisc_1(k4_xboole_0(X1,X0))),k1_zfmisc_1(k5_xboole_0(X0,X1)))),
% 1.57/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).
% 1.57/0.58  fof(f1097,plain,(
% 1.57/0.58    spl2_1),
% 1.57/0.58    inference(avatar_contradiction_clause,[],[f1094])).
% 1.57/0.58  fof(f1094,plain,(
% 1.57/0.58    $false | spl2_1),
% 1.57/0.58    inference(resolution,[],[f1015,f51])).
% 1.57/0.58  fof(f1015,plain,(
% 1.57/0.58    ~r1_tarski(k3_xboole_0(sK0,k5_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) | spl2_1),
% 1.57/0.58    inference(backward_demodulation,[],[f193,f206])).
% 1.57/0.58  fof(f193,plain,(
% 1.57/0.58    ~r1_tarski(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)),k5_xboole_0(sK0,sK1)) | spl2_1),
% 1.57/0.58    inference(resolution,[],[f187,f36])).
% 1.57/0.58  fof(f187,plain,(
% 1.57/0.58    ~r1_tarski(k1_zfmisc_1(k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),k1_zfmisc_1(k5_xboole_0(sK0,sK1))) | spl2_1),
% 1.57/0.58    inference(avatar_component_clause,[],[f185])).
% 1.57/0.58  % SZS output end Proof for theBenchmark
% 1.57/0.58  % (25642)------------------------------
% 1.57/0.58  % (25642)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.57/0.58  % (25642)Termination reason: Refutation
% 1.57/0.58  
% 1.57/0.58  % (25642)Memory used [KB]: 8315
% 1.57/0.58  % (25642)Time elapsed: 0.165 s
% 1.57/0.58  % (25642)------------------------------
% 1.57/0.58  % (25642)------------------------------
% 1.57/0.58  % (25637)Success in time 0.215 s
%------------------------------------------------------------------------------
