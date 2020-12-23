%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:30 EST 2020

% Result     : Theorem 1.67s
% Output     : Refutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :  160 (1367 expanded)
%              Number of leaves         :   27 ( 457 expanded)
%              Depth                    :   18
%              Number of atoms          :  383 (1948 expanded)
%              Number of equality atoms :  241 (1739 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    8 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f837,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f236,f250,f263,f286,f379,f434,f477,f790,f801,f816,f829,f836])).

fof(f836,plain,
    ( ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f835])).

fof(f835,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f245,f832])).

fof(f832,plain,
    ( sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f831,f117])).

fof(f117,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f109,f101])).

% (24875)Refutation not found, incomplete strategy% (24875)------------------------------
% (24875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24875)Termination reason: Refutation not found, incomplete strategy

% (24875)Memory used [KB]: 6140
% (24875)Time elapsed: 0.186 s
% (24875)------------------------------
% (24875)------------------------------
% (24937)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
fof(f101,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(forward_demodulation,[],[f100,f42])).

fof(f42,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f100,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0 ),
    inference(forward_demodulation,[],[f84,f83])).

fof(f83,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f43,f76])).

fof(f76,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f45,f72])).

fof(f72,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f50,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f57,f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f64,f69])).

fof(f69,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f65,f68])).

fof(f68,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f66,f67])).

fof(f67,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f66,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f65,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f64,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f57,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f50,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f45,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f43,plain,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] : k3_tarski(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

fof(f84,plain,(
    ! [X0] : k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0 ),
    inference(definition_unfolding,[],[f46,f74])).

fof(f74,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f52,f73])).

fof(f73,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f49,f72])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f52,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f46,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f109,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1) ),
    inference(superposition,[],[f58,f42])).

fof(f58,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f831,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))
    | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f830,f42])).

fof(f830,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f105,f789])).

fof(f789,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f787])).

fof(f787,plain,
    ( spl3_15
  <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f105,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    inference(backward_demodulation,[],[f78,f58])).

fof(f78,plain,
    ( sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f39,f76,f75,f72])).

fof(f75,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f51,f74])).

fof(f51,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f39,plain,
    ( sK0 != k1_tarski(sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ( sK0 != k2_tarski(sK1,sK2)
        & sK0 != k1_tarski(sK2)
        & sK0 != k1_tarski(sK1)
        & k1_xboole_0 != sK0 )
      | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
    & ( sK0 = k2_tarski(sK1,sK2)
      | sK0 = k1_tarski(sK2)
      | sK0 = k1_tarski(sK1)
      | k1_xboole_0 = sK0
      | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1,X2] :
        ( ( ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
        & ( k2_tarski(X1,X2) = X0
          | k1_tarski(X2) = X0
          | k1_tarski(X1) = X0
          | k1_xboole_0 = X0
          | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) )
   => ( ( ( sK0 != k2_tarski(sK1,sK2)
          & sK0 != k1_tarski(sK2)
          & sK0 != k1_tarski(sK1)
          & k1_xboole_0 != sK0 )
        | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) )
      & ( sK0 = k2_tarski(sK1,sK2)
        | sK0 = k1_tarski(sK2)
        | sK0 = k1_tarski(sK1)
        | k1_xboole_0 = sK0
        | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( ( ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2)) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <~> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
      <=> ~ ( k2_tarski(X1,X2) != X0
            & k1_tarski(X2) != X0
            & k1_tarski(X1) != X0
            & k1_xboole_0 != X0 ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).

fof(f245,plain,
    ( sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl3_4
  <=> sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f829,plain,
    ( ~ spl3_3
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f828])).

fof(f828,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f241,f820])).

fof(f820,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f819,f117])).

fof(f819,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))
    | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f818,f42])).

fof(f818,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f104,f789])).

fof(f104,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    inference(backward_demodulation,[],[f79,f58])).

fof(f79,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f38,f76,f75,f72])).

fof(f38,plain,
    ( sK0 != k1_tarski(sK1)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f241,plain,
    ( sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f239])).

fof(f239,plain,
    ( spl3_3
  <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f816,plain,
    ( ~ spl3_5
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f815])).

fof(f815,plain,
    ( $false
    | ~ spl3_5
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f249,f813])).

fof(f813,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f812,f117])).

fof(f812,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0))
    | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f811,f42])).

fof(f811,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl3_15 ),
    inference(forward_demodulation,[],[f106,f789])).

fof(f106,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    inference(backward_demodulation,[],[f77,f58])).

fof(f77,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f40,f72,f75,f72])).

fof(f40,plain,
    ( sK0 != k2_tarski(sK1,sK2)
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f249,plain,
    ( sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f247])).

fof(f247,plain,
    ( spl3_5
  <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f801,plain,
    ( spl3_13
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f800])).

fof(f800,plain,
    ( $false
    | spl3_13
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f798,f476])).

fof(f476,plain,
    ( ~ r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f474])).

fof(f474,plain,
    ( spl3_13
  <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f798,plain,
    ( r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_15 ),
    inference(superposition,[],[f85,f789])).

fof(f85,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f47,f73])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f790,plain,
    ( spl3_15
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f590,f233,f787])).

fof(f233,plain,
    ( spl3_2
  <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f590,plain,
    ( k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f589,f44])).

fof(f44,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f589,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f575,f117])).

fof(f575,plain,
    ( k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f467,f42])).

fof(f467,plain,
    ( ! [X0] : k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),X0)))) = X0
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f466,f101])).

fof(f466,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),X0))))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f465,f58])).

fof(f465,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),X0)))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f459,f58])).

fof(f459,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))),X0))
    | ~ spl3_2 ),
    inference(superposition,[],[f58,f234])).

fof(f234,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f233])).

fof(f477,plain,
    ( ~ spl3_13
    | spl3_1
    | spl3_3
    | spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f436,f247,f243,f239,f229,f474])).

fof(f229,plain,
    ( spl3_1
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f436,plain,
    ( ~ r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | spl3_1
    | spl3_3
    | spl3_4
    | spl3_5 ),
    inference(unit_resulting_resolution,[],[f231,f248,f240,f244,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0 ) ),
    inference(definition_unfolding,[],[f59,f72,f76,f76,f72])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X1,X2) = X0
      | k1_tarski(X2) = X0
      | k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,k2_tarski(X1,X2))
        | ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k2_tarski(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ( k2_tarski(X1,X2) = X0
        | k1_tarski(X2) = X0
        | k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
    <=> ~ ( k2_tarski(X1,X2) != X0
          & k1_tarski(X2) != X0
          & k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

fof(f244,plain,
    ( sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f243])).

fof(f240,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f239])).

fof(f248,plain,
    ( sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | spl3_5 ),
    inference(avatar_component_clause,[],[f247])).

fof(f231,plain,
    ( k1_xboole_0 != sK0
    | spl3_1 ),
    inference(avatar_component_clause,[],[f229])).

fof(f434,plain,
    ( spl3_2
    | ~ spl3_4 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl3_2
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f429,f42])).

fof(f429,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | spl3_2
    | ~ spl3_4 ),
    inference(backward_demodulation,[],[f237,f417])).

fof(f417,plain,
    ( ! [X0] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f324,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f53,f73])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f324,plain,
    ( ! [X2] : r1_tarski(sK0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,sK2))
    | ~ spl3_4 ),
    inference(superposition,[],[f96,f245])).

fof(f96,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0 ) ),
    inference(definition_unfolding,[],[f62,f72,f76])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X2) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f237,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | spl3_2 ),
    inference(superposition,[],[f235,f117])).

fof(f235,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f233])).

fof(f379,plain,
    ( spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | spl3_2
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f374,f42])).

fof(f374,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | spl3_2
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f237,f362])).

fof(f362,plain,
    ( ! [X0] : k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))
    | ~ spl3_3 ),
    inference(unit_resulting_resolution,[],[f268,f87])).

fof(f268,plain,
    ( ! [X0] : r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))
    | ~ spl3_3 ),
    inference(superposition,[],[f97,f241])).

fof(f97,plain,(
    ! [X2,X1] : r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0 ) ),
    inference(definition_unfolding,[],[f61,f72,f76])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_tarski(X1) != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f286,plain,
    ( spl3_2
    | ~ spl3_5 ),
    inference(avatar_contradiction_clause,[],[f285])).

fof(f285,plain,
    ( $false
    | spl3_2
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f284,f42])).

fof(f284,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,sK0)
    | spl3_2
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f279,f83])).

fof(f279,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0)))
    | spl3_2
    | ~ spl3_5 ),
    inference(backward_demodulation,[],[f237,f249])).

fof(f263,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl3_1
    | spl3_2 ),
    inference(subsumption_resolution,[],[f261,f42])).

fof(f261,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))
    | ~ spl3_1
    | spl3_2 ),
    inference(forward_demodulation,[],[f252,f181])).

fof(f181,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(unit_resulting_resolution,[],[f98,f87])).

fof(f98,plain,(
    ! [X2,X1] : r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(definition_unfolding,[],[f60,f72])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_tarski(X1,X2))
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f252,plain,
    ( k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))
    | ~ spl3_1
    | spl3_2 ),
    inference(backward_demodulation,[],[f237,f230])).

fof(f230,plain,
    ( k1_xboole_0 = sK0
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f229])).

fof(f250,plain,
    ( spl3_1
    | spl3_3
    | spl3_4
    | spl3_5
    | spl3_2 ),
    inference(avatar_split_clause,[],[f102,f233,f247,f243,f239,f229])).

fof(f102,plain,
    ( k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0 ),
    inference(backward_demodulation,[],[f81,f58])).

fof(f81,plain,
    ( sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)
    | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)
    | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f36,f72,f76,f76,f75,f72])).

fof(f36,plain,
    ( sK0 = k2_tarski(sK1,sK2)
    | sK0 = k1_tarski(sK2)
    | sK0 = k1_tarski(sK1)
    | k1_xboole_0 = sK0
    | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).

fof(f236,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f103,f233,f229])).

fof(f103,plain,
    ( k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))
    | k1_xboole_0 != sK0 ),
    inference(backward_demodulation,[],[f80,f58])).

fof(f80,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))) ),
    inference(definition_unfolding,[],[f37,f75,f72])).

fof(f37,plain,
    ( k1_xboole_0 != sK0
    | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2)) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:33:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (24875)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (24872)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (24876)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (24883)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.52  % (24877)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (24899)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (24874)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (24880)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.52  % (24899)Refutation not found, incomplete strategy% (24899)------------------------------
% 0.21/0.52  % (24899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24899)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24899)Memory used [KB]: 6268
% 0.21/0.52  % (24899)Time elapsed: 0.106 s
% 0.21/0.52  % (24899)------------------------------
% 0.21/0.52  % (24899)------------------------------
% 0.21/0.53  % (24883)Refutation not found, incomplete strategy% (24883)------------------------------
% 0.21/0.53  % (24883)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (24883)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (24883)Memory used [KB]: 6268
% 0.21/0.53  % (24883)Time elapsed: 0.107 s
% 0.21/0.53  % (24883)------------------------------
% 0.21/0.53  % (24883)------------------------------
% 0.21/0.53  % (24888)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (24882)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (24895)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (24891)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (24884)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (24879)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (24878)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (24881)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (24885)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (24898)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (24886)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (24886)Refutation not found, incomplete strategy% (24886)------------------------------
% 0.21/0.54  % (24886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24886)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24886)Memory used [KB]: 1663
% 0.21/0.54  % (24886)Time elapsed: 0.130 s
% 0.21/0.54  % (24886)------------------------------
% 0.21/0.54  % (24886)------------------------------
% 0.21/0.54  % (24873)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (24898)Refutation not found, incomplete strategy% (24898)------------------------------
% 0.21/0.54  % (24898)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24898)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24898)Memory used [KB]: 6268
% 0.21/0.54  % (24898)Time elapsed: 0.130 s
% 0.21/0.54  % (24898)------------------------------
% 0.21/0.54  % (24898)------------------------------
% 0.21/0.54  % (24892)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (24873)Refutation not found, incomplete strategy% (24873)------------------------------
% 0.21/0.54  % (24873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24896)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.55  % (24900)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (24889)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.55  % (24889)Refutation not found, incomplete strategy% (24889)------------------------------
% 0.21/0.55  % (24889)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24901)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (24902)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (24893)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (24891)Refutation not found, incomplete strategy% (24891)------------------------------
% 0.21/0.55  % (24891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (24891)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (24891)Memory used [KB]: 1663
% 0.21/0.55  % (24891)Time elapsed: 0.142 s
% 0.21/0.55  % (24891)------------------------------
% 0.21/0.55  % (24891)------------------------------
% 0.21/0.55  % (24894)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (24897)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (24897)Refutation not found, incomplete strategy% (24897)------------------------------
% 0.21/0.56  % (24897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24873)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24873)Memory used [KB]: 1791
% 0.21/0.56  % (24873)Time elapsed: 0.129 s
% 0.21/0.56  % (24873)------------------------------
% 0.21/0.56  % (24873)------------------------------
% 0.21/0.56  % (24890)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  % (24902)Refutation not found, incomplete strategy% (24902)------------------------------
% 0.21/0.56  % (24902)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24902)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24902)Memory used [KB]: 1663
% 0.21/0.56  % (24902)Time elapsed: 0.149 s
% 0.21/0.56  % (24902)------------------------------
% 0.21/0.56  % (24902)------------------------------
% 0.21/0.56  % (24890)Refutation not found, incomplete strategy% (24890)------------------------------
% 0.21/0.56  % (24890)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (24889)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (24889)Memory used [KB]: 10618
% 0.21/0.56  % (24889)Time elapsed: 0.143 s
% 0.21/0.56  % (24889)------------------------------
% 0.21/0.56  % (24889)------------------------------
% 1.49/0.57  % (24890)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (24890)Memory used [KB]: 1791
% 1.49/0.57  % (24890)Time elapsed: 0.154 s
% 1.49/0.57  % (24890)------------------------------
% 1.49/0.57  % (24890)------------------------------
% 1.49/0.57  % (24897)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (24897)Memory used [KB]: 10746
% 1.49/0.57  % (24897)Time elapsed: 0.142 s
% 1.49/0.57  % (24897)------------------------------
% 1.49/0.57  % (24897)------------------------------
% 1.49/0.57  % (24900)Refutation not found, incomplete strategy% (24900)------------------------------
% 1.49/0.57  % (24900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.49/0.57  % (24900)Termination reason: Refutation not found, incomplete strategy
% 1.49/0.57  
% 1.49/0.57  % (24900)Memory used [KB]: 6268
% 1.49/0.57  % (24900)Time elapsed: 0.160 s
% 1.49/0.57  % (24900)------------------------------
% 1.49/0.57  % (24900)------------------------------
% 1.67/0.62  % (24893)Refutation found. Thanks to Tanya!
% 1.67/0.62  % SZS status Theorem for theBenchmark
% 1.67/0.62  % SZS output start Proof for theBenchmark
% 1.67/0.62  fof(f837,plain,(
% 1.67/0.62    $false),
% 1.67/0.62    inference(avatar_sat_refutation,[],[f236,f250,f263,f286,f379,f434,f477,f790,f801,f816,f829,f836])).
% 1.67/0.62  fof(f836,plain,(
% 1.67/0.62    ~spl3_4 | ~spl3_15),
% 1.67/0.62    inference(avatar_contradiction_clause,[],[f835])).
% 1.67/0.62  fof(f835,plain,(
% 1.67/0.62    $false | (~spl3_4 | ~spl3_15)),
% 1.67/0.62    inference(subsumption_resolution,[],[f245,f832])).
% 1.67/0.62  fof(f832,plain,(
% 1.67/0.62    sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl3_15),
% 1.67/0.62    inference(subsumption_resolution,[],[f831,f117])).
% 1.67/0.62  fof(f117,plain,(
% 1.67/0.62    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.67/0.62    inference(forward_demodulation,[],[f109,f101])).
% 1.67/0.62  % (24875)Refutation not found, incomplete strategy% (24875)------------------------------
% 1.67/0.62  % (24875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.67/0.62  % (24875)Termination reason: Refutation not found, incomplete strategy
% 1.67/0.62  
% 1.67/0.62  % (24875)Memory used [KB]: 6140
% 1.67/0.62  % (24875)Time elapsed: 0.186 s
% 1.67/0.62  % (24875)------------------------------
% 1.67/0.62  % (24875)------------------------------
% 2.01/0.64  % (24937)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.01/0.64  fof(f101,plain,(
% 2.01/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 2.01/0.64    inference(forward_demodulation,[],[f100,f42])).
% 2.01/0.64  fof(f42,plain,(
% 2.01/0.64    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f9])).
% 2.01/0.64  fof(f9,axiom,(
% 2.01/0.64    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.01/0.64  fof(f100,plain,(
% 2.01/0.64    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),X0) = X0) )),
% 2.01/0.64    inference(forward_demodulation,[],[f84,f83])).
% 2.01/0.64  fof(f83,plain,(
% 2.01/0.64    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 2.01/0.64    inference(definition_unfolding,[],[f43,f76])).
% 2.01/0.64  fof(f76,plain,(
% 2.01/0.64    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 2.01/0.64    inference(definition_unfolding,[],[f45,f72])).
% 2.01/0.64  fof(f72,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 2.01/0.64    inference(definition_unfolding,[],[f50,f71])).
% 2.01/0.64  fof(f71,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 2.01/0.64    inference(definition_unfolding,[],[f57,f70])).
% 2.01/0.64  fof(f70,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 2.01/0.64    inference(definition_unfolding,[],[f64,f69])).
% 2.01/0.64  fof(f69,plain,(
% 2.01/0.64    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.01/0.64    inference(definition_unfolding,[],[f65,f68])).
% 2.01/0.64  fof(f68,plain,(
% 2.01/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 2.01/0.64    inference(definition_unfolding,[],[f66,f67])).
% 2.01/0.64  fof(f67,plain,(
% 2.01/0.64    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f18])).
% 2.01/0.64  fof(f18,axiom,(
% 2.01/0.64    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 2.01/0.64  fof(f66,plain,(
% 2.01/0.64    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f17])).
% 2.01/0.64  fof(f17,axiom,(
% 2.01/0.64    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 2.01/0.64  fof(f65,plain,(
% 2.01/0.64    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f16])).
% 2.01/0.64  fof(f16,axiom,(
% 2.01/0.64    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 2.01/0.64  fof(f64,plain,(
% 2.01/0.64    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f15])).
% 2.01/0.64  fof(f15,axiom,(
% 2.01/0.64    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 2.01/0.64  fof(f57,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f14])).
% 2.01/0.64  fof(f14,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 2.01/0.64  fof(f50,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f13])).
% 2.01/0.64  fof(f13,axiom,(
% 2.01/0.64    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.01/0.64  fof(f45,plain,(
% 2.01/0.64    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f12])).
% 2.01/0.64  fof(f12,axiom,(
% 2.01/0.64    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 2.01/0.64  fof(f43,plain,(
% 2.01/0.64    ( ! [X0] : (k3_tarski(k1_tarski(X0)) = X0) )),
% 2.01/0.64    inference(cnf_transformation,[],[f21])).
% 2.01/0.64  fof(f21,axiom,(
% 2.01/0.64    ! [X0] : k3_tarski(k1_tarski(X0)) = X0),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).
% 2.01/0.64  fof(f84,plain,(
% 2.01/0.64    ( ! [X0] : (k5_xboole_0(k5_xboole_0(X0,X0),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = X0) )),
% 2.01/0.64    inference(definition_unfolding,[],[f46,f74])).
% 2.01/0.64  fof(f74,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.01/0.64    inference(definition_unfolding,[],[f52,f73])).
% 2.01/0.64  fof(f73,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 2.01/0.64    inference(definition_unfolding,[],[f49,f72])).
% 2.01/0.64  fof(f49,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f20])).
% 2.01/0.64  fof(f20,axiom,(
% 2.01/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.01/0.64  fof(f52,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f10])).
% 2.01/0.64  fof(f10,axiom,(
% 2.01/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 2.01/0.64  fof(f46,plain,(
% 2.01/0.64    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.01/0.64    inference(cnf_transformation,[],[f24])).
% 2.01/0.64  fof(f24,plain,(
% 2.01/0.64    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.01/0.64    inference(rectify,[],[f1])).
% 2.01/0.64  fof(f1,axiom,(
% 2.01/0.64    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.01/0.64  fof(f109,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) )),
% 2.01/0.64    inference(superposition,[],[f58,f42])).
% 2.01/0.64  fof(f58,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f8])).
% 2.01/0.64  fof(f8,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 2.01/0.64  fof(f831,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl3_15),
% 2.01/0.64    inference(forward_demodulation,[],[f830,f42])).
% 2.01/0.64  fof(f830,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl3_15),
% 2.01/0.64    inference(forward_demodulation,[],[f105,f789])).
% 2.01/0.64  fof(f789,plain,(
% 2.01/0.64    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | ~spl3_15),
% 2.01/0.64    inference(avatar_component_clause,[],[f787])).
% 2.01/0.64  fof(f787,plain,(
% 2.01/0.64    spl3_15 <=> k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.01/0.64  fof(f105,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 2.01/0.64    inference(backward_demodulation,[],[f78,f58])).
% 2.01/0.64  fof(f78,plain,(
% 2.01/0.64    sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 2.01/0.64    inference(definition_unfolding,[],[f39,f76,f75,f72])).
% 2.01/0.64  fof(f75,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))))) )),
% 2.01/0.64    inference(definition_unfolding,[],[f51,f74])).
% 2.01/0.64  fof(f51,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f3])).
% 2.01/0.64  fof(f3,axiom,(
% 2.01/0.64    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.01/0.64  fof(f39,plain,(
% 2.01/0.64    sK0 != k1_tarski(sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.01/0.64    inference(cnf_transformation,[],[f31])).
% 2.01/0.64  fof(f31,plain,(
% 2.01/0.64    ((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2)))),
% 2.01/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f30])).
% 2.01/0.64  fof(f30,plain,(
% 2.01/0.64    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)))) => (((sK0 != k2_tarski(sK1,sK2) & sK0 != k1_tarski(sK2) & sK0 != k1_tarski(sK1) & k1_xboole_0 != sK0) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))) & (sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))))),
% 2.01/0.64    introduced(choice_axiom,[])).
% 2.01/0.64  fof(f29,plain,(
% 2.01/0.64    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 2.01/0.64    inference(flattening,[],[f28])).
% 2.01/0.64  fof(f28,plain,(
% 2.01/0.64    ? [X0,X1,X2] : (((k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0) | k1_xboole_0 != k4_xboole_0(X0,k2_tarski(X1,X2))) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2))))),
% 2.01/0.64    inference(nnf_transformation,[],[f25])).
% 2.01/0.64  fof(f25,plain,(
% 2.01/0.64    ? [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <~> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.01/0.64    inference(ennf_transformation,[],[f23])).
% 2.01/0.64  fof(f23,negated_conjecture,(
% 2.01/0.64    ~! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.01/0.64    inference(negated_conjecture,[],[f22])).
% 2.01/0.64  fof(f22,conjecture,(
% 2.01/0.64    ! [X0,X1,X2] : (k1_xboole_0 = k4_xboole_0(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_zfmisc_1)).
% 2.01/0.64  fof(f245,plain,(
% 2.01/0.64    sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | ~spl3_4),
% 2.01/0.64    inference(avatar_component_clause,[],[f243])).
% 2.01/0.64  fof(f243,plain,(
% 2.01/0.64    spl3_4 <=> sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.01/0.64  fof(f829,plain,(
% 2.01/0.64    ~spl3_3 | ~spl3_15),
% 2.01/0.64    inference(avatar_contradiction_clause,[],[f828])).
% 2.01/0.64  fof(f828,plain,(
% 2.01/0.64    $false | (~spl3_3 | ~spl3_15)),
% 2.01/0.64    inference(subsumption_resolution,[],[f241,f820])).
% 2.01/0.64  fof(f820,plain,(
% 2.01/0.64    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_15),
% 2.01/0.64    inference(subsumption_resolution,[],[f819,f117])).
% 2.01/0.64  fof(f819,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_15),
% 2.01/0.64    inference(forward_demodulation,[],[f818,f42])).
% 2.01/0.64  fof(f818,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_15),
% 2.01/0.64    inference(forward_demodulation,[],[f104,f789])).
% 2.01/0.64  fof(f104,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 2.01/0.64    inference(backward_demodulation,[],[f79,f58])).
% 2.01/0.64  fof(f79,plain,(
% 2.01/0.64    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 2.01/0.64    inference(definition_unfolding,[],[f38,f76,f75,f72])).
% 2.01/0.64  fof(f38,plain,(
% 2.01/0.64    sK0 != k1_tarski(sK1) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.01/0.64    inference(cnf_transformation,[],[f31])).
% 2.01/0.64  fof(f241,plain,(
% 2.01/0.64    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | ~spl3_3),
% 2.01/0.64    inference(avatar_component_clause,[],[f239])).
% 2.01/0.64  fof(f239,plain,(
% 2.01/0.64    spl3_3 <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.01/0.64  fof(f816,plain,(
% 2.01/0.64    ~spl3_5 | ~spl3_15),
% 2.01/0.64    inference(avatar_contradiction_clause,[],[f815])).
% 2.01/0.64  fof(f815,plain,(
% 2.01/0.64    $false | (~spl3_5 | ~spl3_15)),
% 2.01/0.64    inference(subsumption_resolution,[],[f249,f813])).
% 2.01/0.64  fof(f813,plain,(
% 2.01/0.64    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl3_15),
% 2.01/0.64    inference(subsumption_resolution,[],[f812,f117])).
% 2.01/0.64  fof(f812,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k1_xboole_0)) | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl3_15),
% 2.01/0.64    inference(forward_demodulation,[],[f811,f42])).
% 2.01/0.64  fof(f811,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl3_15),
% 2.01/0.64    inference(forward_demodulation,[],[f106,f789])).
% 2.01/0.64  fof(f106,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 2.01/0.64    inference(backward_demodulation,[],[f77,f58])).
% 2.01/0.64  fof(f77,plain,(
% 2.01/0.64    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 2.01/0.64    inference(definition_unfolding,[],[f40,f72,f75,f72])).
% 2.01/0.64  fof(f40,plain,(
% 2.01/0.64    sK0 != k2_tarski(sK1,sK2) | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.01/0.64    inference(cnf_transformation,[],[f31])).
% 2.01/0.64  fof(f249,plain,(
% 2.01/0.64    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | ~spl3_5),
% 2.01/0.64    inference(avatar_component_clause,[],[f247])).
% 2.01/0.64  fof(f247,plain,(
% 2.01/0.64    spl3_5 <=> sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.01/0.64  fof(f801,plain,(
% 2.01/0.64    spl3_13 | ~spl3_15),
% 2.01/0.64    inference(avatar_contradiction_clause,[],[f800])).
% 2.01/0.64  fof(f800,plain,(
% 2.01/0.64    $false | (spl3_13 | ~spl3_15)),
% 2.01/0.64    inference(subsumption_resolution,[],[f798,f476])).
% 2.01/0.64  fof(f476,plain,(
% 2.01/0.64    ~r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | spl3_13),
% 2.01/0.64    inference(avatar_component_clause,[],[f474])).
% 2.01/0.64  fof(f474,plain,(
% 2.01/0.64    spl3_13 <=> r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.01/0.64  fof(f798,plain,(
% 2.01/0.64    r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | ~spl3_15),
% 2.01/0.64    inference(superposition,[],[f85,f789])).
% 2.01/0.64  fof(f85,plain,(
% 2.01/0.64    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.01/0.64    inference(definition_unfolding,[],[f47,f73])).
% 2.01/0.64  fof(f47,plain,(
% 2.01/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f7])).
% 2.01/0.64  fof(f7,axiom,(
% 2.01/0.64    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.01/0.64  fof(f790,plain,(
% 2.01/0.64    spl3_15 | ~spl3_2),
% 2.01/0.64    inference(avatar_split_clause,[],[f590,f233,f787])).
% 2.01/0.64  fof(f233,plain,(
% 2.01/0.64    spl3_2 <=> k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))))),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.01/0.64  fof(f590,plain,(
% 2.01/0.64    k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) | ~spl3_2),
% 2.01/0.64    inference(forward_demodulation,[],[f589,f44])).
% 2.01/0.64  fof(f44,plain,(
% 2.01/0.64    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.01/0.64    inference(cnf_transformation,[],[f6])).
% 2.01/0.64  fof(f6,axiom,(
% 2.01/0.64    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 2.01/0.64  fof(f589,plain,(
% 2.01/0.64    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0) | ~spl3_2),
% 2.01/0.64    inference(forward_demodulation,[],[f575,f117])).
% 2.01/0.64  fof(f575,plain,(
% 2.01/0.64    k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k1_xboole_0))) | ~spl3_2),
% 2.01/0.64    inference(superposition,[],[f467,f42])).
% 2.01/0.64  fof(f467,plain,(
% 2.01/0.64    ( ! [X0] : (k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),X0)))) = X0) ) | ~spl3_2),
% 2.01/0.64    inference(forward_demodulation,[],[f466,f101])).
% 2.01/0.64  fof(f466,plain,(
% 2.01/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k5_xboole_0(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))),X0))))) ) | ~spl3_2),
% 2.01/0.64    inference(forward_demodulation,[],[f465,f58])).
% 2.01/0.64  fof(f465,plain,(
% 2.01/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))),X0)))) ) | ~spl3_2),
% 2.01/0.64    inference(forward_demodulation,[],[f459,f58])).
% 2.01/0.64  fof(f459,plain,(
% 2.01/0.64    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2))))),X0))) ) | ~spl3_2),
% 2.01/0.64    inference(superposition,[],[f58,f234])).
% 2.01/0.64  fof(f234,plain,(
% 2.01/0.64    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | ~spl3_2),
% 2.01/0.64    inference(avatar_component_clause,[],[f233])).
% 2.01/0.64  fof(f477,plain,(
% 2.01/0.64    ~spl3_13 | spl3_1 | spl3_3 | spl3_4 | spl3_5),
% 2.01/0.64    inference(avatar_split_clause,[],[f436,f247,f243,f239,f229,f474])).
% 2.01/0.64  fof(f229,plain,(
% 2.01/0.64    spl3_1 <=> k1_xboole_0 = sK0),
% 2.01/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.01/0.64  fof(f436,plain,(
% 2.01/0.64    ~r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | (spl3_1 | spl3_3 | spl3_4 | spl3_5)),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f231,f248,f240,f244,f92])).
% 2.01/0.64  fof(f92,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2) = X0) )),
% 2.01/0.64    inference(definition_unfolding,[],[f59,f72,f76,f76,f72])).
% 2.01/0.64  fof(f59,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))) )),
% 2.01/0.64    inference(cnf_transformation,[],[f35])).
% 2.01/0.64  fof(f35,plain,(
% 2.01/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.01/0.64    inference(flattening,[],[f34])).
% 2.01/0.64  fof(f34,plain,(
% 2.01/0.64    ! [X0,X1,X2] : ((r1_tarski(X0,k2_tarski(X1,X2)) | (k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k2_tarski(X1,X2))))),
% 2.01/0.64    inference(nnf_transformation,[],[f27])).
% 2.01/0.64  fof(f27,plain,(
% 2.01/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> (k2_tarski(X1,X2) = X0 | k1_tarski(X2) = X0 | k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.01/0.64    inference(ennf_transformation,[],[f19])).
% 2.01/0.64  fof(f19,axiom,(
% 2.01/0.64    ! [X0,X1,X2] : (r1_tarski(X0,k2_tarski(X1,X2)) <=> ~(k2_tarski(X1,X2) != X0 & k1_tarski(X2) != X0 & k1_tarski(X1) != X0 & k1_xboole_0 != X0))),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).
% 2.01/0.64  fof(f244,plain,(
% 2.01/0.64    sK0 != k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | spl3_4),
% 2.01/0.64    inference(avatar_component_clause,[],[f243])).
% 2.01/0.64  fof(f240,plain,(
% 2.01/0.64    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | spl3_3),
% 2.01/0.64    inference(avatar_component_clause,[],[f239])).
% 2.01/0.64  fof(f248,plain,(
% 2.01/0.64    sK0 != k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | spl3_5),
% 2.01/0.64    inference(avatar_component_clause,[],[f247])).
% 2.01/0.64  fof(f231,plain,(
% 2.01/0.64    k1_xboole_0 != sK0 | spl3_1),
% 2.01/0.64    inference(avatar_component_clause,[],[f229])).
% 2.01/0.64  fof(f434,plain,(
% 2.01/0.64    spl3_2 | ~spl3_4),
% 2.01/0.64    inference(avatar_contradiction_clause,[],[f433])).
% 2.01/0.64  fof(f433,plain,(
% 2.01/0.64    $false | (spl3_2 | ~spl3_4)),
% 2.01/0.64    inference(subsumption_resolution,[],[f429,f42])).
% 2.01/0.64  fof(f429,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | (spl3_2 | ~spl3_4)),
% 2.01/0.64    inference(backward_demodulation,[],[f237,f417])).
% 2.01/0.64  fof(f417,plain,(
% 2.01/0.64    ( ! [X0] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,sK2)))) ) | ~spl3_4),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f324,f87])).
% 2.01/0.64  fof(f87,plain,(
% 2.01/0.64    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 2.01/0.64    inference(definition_unfolding,[],[f53,f73])).
% 2.01/0.64  fof(f53,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 2.01/0.64    inference(cnf_transformation,[],[f26])).
% 2.01/0.64  fof(f26,plain,(
% 2.01/0.64    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 2.01/0.64    inference(ennf_transformation,[],[f4])).
% 2.01/0.64  fof(f4,axiom,(
% 2.01/0.64    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 2.01/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 2.01/0.64  fof(f324,plain,(
% 2.01/0.64    ( ! [X2] : (r1_tarski(sK0,k6_enumset1(X2,X2,X2,X2,X2,X2,X2,sK2))) ) | ~spl3_4),
% 2.01/0.64    inference(superposition,[],[f96,f245])).
% 2.01/0.64  fof(f96,plain,(
% 2.01/0.64    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 2.01/0.64    inference(equality_resolution,[],[f89])).
% 2.01/0.64  fof(f89,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2) != X0) )),
% 2.01/0.64    inference(definition_unfolding,[],[f62,f72,f76])).
% 2.01/0.64  fof(f62,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X2) != X0) )),
% 2.01/0.64    inference(cnf_transformation,[],[f35])).
% 2.01/0.64  fof(f237,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | spl3_2),
% 2.01/0.64    inference(superposition,[],[f235,f117])).
% 2.01/0.64  fof(f235,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | spl3_2),
% 2.01/0.64    inference(avatar_component_clause,[],[f233])).
% 2.01/0.64  fof(f379,plain,(
% 2.01/0.64    spl3_2 | ~spl3_3),
% 2.01/0.64    inference(avatar_contradiction_clause,[],[f378])).
% 2.01/0.64  fof(f378,plain,(
% 2.01/0.64    $false | (spl3_2 | ~spl3_3)),
% 2.01/0.64    inference(subsumption_resolution,[],[f374,f42])).
% 2.01/0.64  fof(f374,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | (spl3_2 | ~spl3_3)),
% 2.01/0.64    inference(backward_demodulation,[],[f237,f362])).
% 2.01/0.64  fof(f362,plain,(
% 2.01/0.64    ( ! [X0] : (k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0) = k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0)))) ) | ~spl3_3),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f268,f87])).
% 2.01/0.64  fof(f268,plain,(
% 2.01/0.64    ( ! [X0] : (r1_tarski(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,X0))) ) | ~spl3_3),
% 2.01/0.64    inference(superposition,[],[f97,f241])).
% 2.01/0.64  fof(f97,plain,(
% 2.01/0.64    ( ! [X2,X1] : (r1_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 2.01/0.64    inference(equality_resolution,[],[f90])).
% 2.01/0.64  fof(f90,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != X0) )),
% 2.01/0.64    inference(definition_unfolding,[],[f61,f72,f76])).
% 2.01/0.64  fof(f61,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_tarski(X1) != X0) )),
% 2.01/0.64    inference(cnf_transformation,[],[f35])).
% 2.01/0.64  fof(f286,plain,(
% 2.01/0.64    spl3_2 | ~spl3_5),
% 2.01/0.64    inference(avatar_contradiction_clause,[],[f285])).
% 2.01/0.64  fof(f285,plain,(
% 2.01/0.64    $false | (spl3_2 | ~spl3_5)),
% 2.01/0.64    inference(subsumption_resolution,[],[f284,f42])).
% 2.01/0.64  fof(f284,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,sK0) | (spl3_2 | ~spl3_5)),
% 2.01/0.64    inference(forward_demodulation,[],[f279,f83])).
% 2.01/0.64  fof(f279,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))) | (spl3_2 | ~spl3_5)),
% 2.01/0.64    inference(backward_demodulation,[],[f237,f249])).
% 2.01/0.64  fof(f263,plain,(
% 2.01/0.64    ~spl3_1 | spl3_2),
% 2.01/0.64    inference(avatar_contradiction_clause,[],[f262])).
% 2.01/0.64  fof(f262,plain,(
% 2.01/0.64    $false | (~spl3_1 | spl3_2)),
% 2.01/0.64    inference(subsumption_resolution,[],[f261,f42])).
% 2.01/0.64  fof(f261,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)) | (~spl3_1 | spl3_2)),
% 2.01/0.64    inference(forward_demodulation,[],[f252,f181])).
% 2.01/0.64  fof(f181,plain,(
% 2.01/0.64    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 2.01/0.64    inference(unit_resulting_resolution,[],[f98,f87])).
% 2.01/0.64  fof(f98,plain,(
% 2.01/0.64    ( ! [X2,X1] : (r1_tarski(k1_xboole_0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2))) )),
% 2.01/0.64    inference(equality_resolution,[],[f91])).
% 2.01/0.64  fof(f91,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X2)) | k1_xboole_0 != X0) )),
% 2.01/0.64    inference(definition_unfolding,[],[f60,f72])).
% 2.01/0.64  fof(f60,plain,(
% 2.01/0.64    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_tarski(X1,X2)) | k1_xboole_0 != X0) )),
% 2.01/0.64    inference(cnf_transformation,[],[f35])).
% 2.01/0.64  fof(f252,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k1_xboole_0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))) | (~spl3_1 | spl3_2)),
% 2.01/0.64    inference(backward_demodulation,[],[f237,f230])).
% 2.01/0.64  fof(f230,plain,(
% 2.01/0.64    k1_xboole_0 = sK0 | ~spl3_1),
% 2.01/0.64    inference(avatar_component_clause,[],[f229])).
% 2.01/0.64  fof(f250,plain,(
% 2.01/0.64    spl3_1 | spl3_3 | spl3_4 | spl3_5 | spl3_2),
% 2.01/0.64    inference(avatar_split_clause,[],[f102,f233,f247,f243,f239,f229])).
% 2.01/0.64  fof(f102,plain,(
% 2.01/0.64    k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0),
% 2.01/0.64    inference(backward_demodulation,[],[f81,f58])).
% 2.01/0.64  fof(f81,plain,(
% 2.01/0.64    sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2) | sK0 = k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2) | sK0 = k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 2.01/0.64    inference(definition_unfolding,[],[f36,f72,f76,f76,f75,f72])).
% 2.01/0.64  fof(f36,plain,(
% 2.01/0.64    sK0 = k2_tarski(sK1,sK2) | sK0 = k1_tarski(sK2) | sK0 = k1_tarski(sK1) | k1_xboole_0 = sK0 | k1_xboole_0 = k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.01/0.64    inference(cnf_transformation,[],[f31])).
% 2.01/0.64  fof(f236,plain,(
% 2.01/0.64    ~spl3_1 | ~spl3_2),
% 2.01/0.64    inference(avatar_split_clause,[],[f103,f233,f229])).
% 2.01/0.64  fof(f103,plain,(
% 2.01/0.64    k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(sK0,k5_xboole_0(k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))) | k1_xboole_0 != sK0),
% 2.01/0.64    inference(backward_demodulation,[],[f80,f58])).
% 2.01/0.64  fof(f80,plain,(
% 2.01/0.64    k1_xboole_0 != sK0 | k1_xboole_0 != k5_xboole_0(sK0,k5_xboole_0(k5_xboole_0(sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)),k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,k6_enumset1(sK1,sK1,sK1,sK1,sK1,sK1,sK1,sK2)))))),
% 2.01/0.64    inference(definition_unfolding,[],[f37,f75,f72])).
% 2.01/0.64  fof(f37,plain,(
% 2.01/0.64    k1_xboole_0 != sK0 | k1_xboole_0 != k4_xboole_0(sK0,k2_tarski(sK1,sK2))),
% 2.01/0.64    inference(cnf_transformation,[],[f31])).
% 2.01/0.64  % SZS output end Proof for theBenchmark
% 2.01/0.64  % (24893)------------------------------
% 2.01/0.64  % (24893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.01/0.64  % (24893)Termination reason: Refutation
% 2.01/0.64  
% 2.07/0.65  % (24893)Memory used [KB]: 11513
% 2.07/0.65  % (24893)Time elapsed: 0.220 s
% 2.07/0.65  % (24893)------------------------------
% 2.07/0.65  % (24893)------------------------------
% 2.07/0.65  % (24863)Success in time 0.28 s
%------------------------------------------------------------------------------
