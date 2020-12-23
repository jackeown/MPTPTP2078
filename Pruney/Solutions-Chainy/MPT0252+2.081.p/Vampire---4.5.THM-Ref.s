%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:39:02 EST 2020

% Result     : Theorem 1.45s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 383 expanded)
%              Number of leaves         :   17 ( 129 expanded)
%              Depth                    :   16
%              Number of atoms          :  115 ( 437 expanded)
%              Number of equality atoms :   40 ( 344 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (28061)Refutation not found, incomplete strategy% (28061)------------------------------
% (28061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (28061)Termination reason: Refutation not found, incomplete strategy

% (28061)Memory used [KB]: 1663
% (28061)Time elapsed: 0.141 s
% (28061)------------------------------
% (28061)------------------------------
fof(f284,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f98,f266,f274])).

fof(f274,plain,(
    ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f273])).

fof(f273,plain,
    ( $false
    | ~ spl3_2 ),
    inference(subsumption_resolution,[],[f270,f26])).

fof(f26,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,
    ( ~ r2_hidden(sK0,sK2)
    & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).

fof(f19,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

fof(f270,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f269,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f35,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f30,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f46,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f41,f42])).

fof(f42,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f40,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f30,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f269,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_2 ),
    inference(superposition,[],[f77,f97])).

fof(f97,plain,
    ( sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl3_2
  <=> sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f77,plain,(
    ! [X14,X15] : r1_tarski(X14,k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X14,X14,X14))) ),
    inference(superposition,[],[f55,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0) ),
    inference(definition_unfolding,[],[f38,f47,f47])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f28,f50])).

fof(f50,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f28,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f266,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f251,f93])).

fof(f93,plain,
    ( ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl3_1
  <=> r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f251,plain,(
    ! [X0,X1] : r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X0,X0,X0))) ),
    inference(superposition,[],[f235,f59])).

fof(f235,plain,(
    ! [X4,X5] : r1_tarski(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5))) ),
    inference(superposition,[],[f223,f118])).

fof(f118,plain,(
    ! [X8,X9] : k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9) = k6_enumset1(X8,X8,X8,X8,X8,X9,X8,X9) ),
    inference(superposition,[],[f52,f54])).

fof(f54,plain,(
    ! [X0] : k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f27,f50])).

fof(f27,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f52,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f43,f50,f45,f49])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f223,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X0,X1,X0))) ),
    inference(superposition,[],[f143,f59])).

fof(f143,plain,(
    ! [X10,X9] : r1_tarski(X9,k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X10,X9,X10))) ),
    inference(superposition,[],[f55,f118])).

fof(f98,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f89,f95,f91])).

fof(f89,plain,
    ( sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    inference(resolution,[],[f86,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f86,plain,(
    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    inference(forward_demodulation,[],[f53,f59])).

fof(f53,plain,(
    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2) ),
    inference(definition_unfolding,[],[f25,f50,f49])).

fof(f25,plain,(
    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:23:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (28046)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.51  % (28043)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.51  % (28044)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.51  % (28067)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.51  % (28067)Refutation not found, incomplete strategy% (28067)------------------------------
% 0.22/0.51  % (28067)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (28067)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (28067)Memory used [KB]: 10618
% 0.22/0.51  % (28067)Time elapsed: 0.105 s
% 0.22/0.51  % (28067)------------------------------
% 0.22/0.51  % (28067)------------------------------
% 0.22/0.52  % (28052)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (28042)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (28042)Refutation not found, incomplete strategy% (28042)------------------------------
% 0.22/0.52  % (28042)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (28042)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (28042)Memory used [KB]: 1663
% 0.22/0.52  % (28042)Time elapsed: 0.105 s
% 0.22/0.52  % (28042)------------------------------
% 0.22/0.52  % (28042)------------------------------
% 0.22/0.52  % (28070)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.52  % (28059)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.53  % (28059)Refutation not found, incomplete strategy% (28059)------------------------------
% 0.22/0.53  % (28059)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28059)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28059)Memory used [KB]: 10618
% 0.22/0.53  % (28059)Time elapsed: 0.116 s
% 0.22/0.53  % (28059)------------------------------
% 0.22/0.53  % (28059)------------------------------
% 0.22/0.53  % (28062)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (28050)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.53  % (28047)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (28052)Refutation not found, incomplete strategy% (28052)------------------------------
% 0.22/0.53  % (28052)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (28052)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (28052)Memory used [KB]: 10746
% 0.22/0.53  % (28052)Time elapsed: 0.114 s
% 0.22/0.53  % (28052)------------------------------
% 0.22/0.53  % (28052)------------------------------
% 0.22/0.53  % (28057)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.53  % (28069)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (28053)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (28065)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.53  % (28041)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.54  % (28053)Refutation not found, incomplete strategy% (28053)------------------------------
% 0.22/0.54  % (28053)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28053)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28053)Memory used [KB]: 6268
% 0.22/0.54  % (28053)Time elapsed: 0.123 s
% 0.22/0.54  % (28053)------------------------------
% 0.22/0.54  % (28053)------------------------------
% 0.22/0.54  % (28069)Refutation not found, incomplete strategy% (28069)------------------------------
% 0.22/0.54  % (28069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28069)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28069)Memory used [KB]: 6140
% 0.22/0.54  % (28069)Time elapsed: 0.108 s
% 0.22/0.54  % (28069)------------------------------
% 0.22/0.54  % (28069)------------------------------
% 0.22/0.54  % (28045)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (28055)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (28070)Refutation not found, incomplete strategy% (28070)------------------------------
% 0.22/0.54  % (28070)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (28070)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (28070)Memory used [KB]: 6140
% 0.22/0.54  % (28070)Time elapsed: 0.132 s
% 0.22/0.54  % (28070)------------------------------
% 0.22/0.54  % (28070)------------------------------
% 0.22/0.54  % (28066)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (28072)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (28048)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (28072)Refutation not found, incomplete strategy% (28072)------------------------------
% 0.22/0.55  % (28072)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28072)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28072)Memory used [KB]: 1663
% 0.22/0.55  % (28072)Time elapsed: 0.129 s
% 0.22/0.55  % (28072)------------------------------
% 0.22/0.55  % (28072)------------------------------
% 0.22/0.55  % (28071)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.55  % (28057)Refutation not found, incomplete strategy% (28057)------------------------------
% 0.22/0.55  % (28057)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28057)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28057)Memory used [KB]: 1663
% 0.22/0.55  % (28057)Time elapsed: 0.076 s
% 0.22/0.55  % (28057)------------------------------
% 0.22/0.55  % (28057)------------------------------
% 0.22/0.55  % (28064)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (28071)Refutation not found, incomplete strategy% (28071)------------------------------
% 0.22/0.55  % (28071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (28071)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (28071)Memory used [KB]: 10746
% 0.22/0.55  % (28071)Time elapsed: 0.139 s
% 0.22/0.55  % (28071)------------------------------
% 0.22/0.55  % (28071)------------------------------
% 1.45/0.55  % (28054)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.45/0.55  % (28063)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.45/0.55  % (28068)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.45/0.55  % (28058)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.45/0.55  % (28068)Refutation not found, incomplete strategy% (28068)------------------------------
% 1.45/0.55  % (28068)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (28068)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (28068)Memory used [KB]: 6140
% 1.45/0.55  % (28068)Time elapsed: 0.139 s
% 1.45/0.55  % (28068)------------------------------
% 1.45/0.55  % (28068)------------------------------
% 1.45/0.55  % (28060)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.45/0.55  % (28054)Refutation not found, incomplete strategy% (28054)------------------------------
% 1.45/0.55  % (28054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (28054)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (28054)Memory used [KB]: 10618
% 1.45/0.55  % (28054)Time elapsed: 0.141 s
% 1.45/0.55  % (28054)------------------------------
% 1.45/0.55  % (28054)------------------------------
% 1.45/0.55  % (28061)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.45/0.56  % (28047)Refutation found. Thanks to Tanya!
% 1.45/0.56  % SZS status Theorem for theBenchmark
% 1.45/0.56  % SZS output start Proof for theBenchmark
% 1.45/0.56  % (28061)Refutation not found, incomplete strategy% (28061)------------------------------
% 1.45/0.56  % (28061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (28061)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (28061)Memory used [KB]: 1663
% 1.45/0.56  % (28061)Time elapsed: 0.141 s
% 1.45/0.56  % (28061)------------------------------
% 1.45/0.56  % (28061)------------------------------
% 1.45/0.56  fof(f284,plain,(
% 1.45/0.56    $false),
% 1.45/0.56    inference(avatar_sat_refutation,[],[f98,f266,f274])).
% 1.45/0.56  fof(f274,plain,(
% 1.45/0.56    ~spl3_2),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f273])).
% 1.45/0.56  fof(f273,plain,(
% 1.45/0.56    $false | ~spl3_2),
% 1.45/0.56    inference(subsumption_resolution,[],[f270,f26])).
% 1.45/0.56  fof(f26,plain,(
% 1.45/0.56    ~r2_hidden(sK0,sK2)),
% 1.45/0.56    inference(cnf_transformation,[],[f20])).
% 1.45/0.56  fof(f20,plain,(
% 1.45/0.56    ~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 1.45/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f18,f19])).
% 1.45/0.56  fof(f19,plain,(
% 1.45/0.56    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2)) => (~r2_hidden(sK0,sK2) & r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2))),
% 1.45/0.56    introduced(choice_axiom,[])).
% 1.45/0.56  fof(f18,plain,(
% 1.45/0.56    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2))),
% 1.45/0.56    inference(ennf_transformation,[],[f16])).
% 1.45/0.56  fof(f16,negated_conjecture,(
% 1.45/0.56    ~! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.45/0.56    inference(negated_conjecture,[],[f15])).
% 1.45/0.56  fof(f15,conjecture,(
% 1.45/0.56    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(k2_tarski(X0,X1),X2),X2) => r2_hidden(X0,X2))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).
% 1.45/0.56  fof(f270,plain,(
% 1.45/0.56    r2_hidden(sK0,sK2) | ~spl3_2),
% 1.45/0.56    inference(resolution,[],[f269,f58])).
% 1.45/0.56  fof(f58,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f35,f49])).
% 1.45/0.56  fof(f49,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f30,f48])).
% 1.45/0.56  fof(f48,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f34,f47])).
% 1.45/0.56  fof(f47,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f39,f46])).
% 1.45/0.56  fof(f46,plain,(
% 1.45/0.56    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f40,f45])).
% 1.45/0.56  fof(f45,plain,(
% 1.45/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f41,f42])).
% 1.45/0.56  fof(f42,plain,(
% 1.45/0.56    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f12])).
% 1.45/0.56  fof(f12,axiom,(
% 1.45/0.56    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.45/0.56  fof(f41,plain,(
% 1.45/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f11])).
% 1.45/0.56  fof(f11,axiom,(
% 1.45/0.56    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.45/0.56  fof(f40,plain,(
% 1.45/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f10])).
% 1.45/0.56  fof(f10,axiom,(
% 1.45/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.45/0.56  fof(f39,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f9])).
% 1.45/0.56  fof(f9,axiom,(
% 1.45/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.45/0.56  fof(f34,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f8])).
% 1.45/0.56  fof(f8,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.45/0.56  fof(f30,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f7])).
% 1.45/0.56  fof(f7,axiom,(
% 1.45/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.45/0.56  fof(f35,plain,(
% 1.45/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f24])).
% 1.45/0.56  fof(f24,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.45/0.56    inference(flattening,[],[f23])).
% 1.45/0.56  fof(f23,plain,(
% 1.45/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.45/0.56    inference(nnf_transformation,[],[f14])).
% 1.45/0.56  fof(f14,axiom,(
% 1.45/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.45/0.56  fof(f269,plain,(
% 1.45/0.56    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_2),
% 1.45/0.56    inference(superposition,[],[f77,f97])).
% 1.45/0.56  fof(f97,plain,(
% 1.45/0.56    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~spl3_2),
% 1.45/0.56    inference(avatar_component_clause,[],[f95])).
% 1.45/0.56  fof(f95,plain,(
% 1.45/0.56    spl3_2 <=> sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.45/0.56  fof(f77,plain,(
% 1.45/0.56    ( ! [X14,X15] : (r1_tarski(X14,k3_tarski(k6_enumset1(X15,X15,X15,X15,X15,X14,X14,X14)))) )),
% 1.45/0.56    inference(superposition,[],[f55,f59])).
% 1.45/0.56  fof(f59,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X3,X3,X3,X3,X3,X2,X1,X0)) )),
% 1.45/0.56    inference(definition_unfolding,[],[f38,f47,f47])).
% 1.45/0.56  fof(f38,plain,(
% 1.45/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f4])).
% 1.45/0.56  fof(f4,axiom,(
% 1.45/0.56    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X3,X2,X1,X0)),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_enumset1)).
% 1.45/0.56  fof(f55,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.45/0.56    inference(definition_unfolding,[],[f28,f50])).
% 1.45/0.56  fof(f50,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.45/0.56    inference(definition_unfolding,[],[f29,f49])).
% 1.45/0.56  fof(f29,plain,(
% 1.45/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f13])).
% 1.45/0.56  fof(f13,axiom,(
% 1.45/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.45/0.56  fof(f28,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f3])).
% 1.45/0.56  fof(f3,axiom,(
% 1.45/0.56    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.45/0.56  fof(f266,plain,(
% 1.45/0.56    spl3_1),
% 1.45/0.56    inference(avatar_contradiction_clause,[],[f261])).
% 1.45/0.56  fof(f261,plain,(
% 1.45/0.56    $false | spl3_1),
% 1.45/0.56    inference(resolution,[],[f251,f93])).
% 1.45/0.56  fof(f93,plain,(
% 1.45/0.56    ~r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | spl3_1),
% 1.45/0.56    inference(avatar_component_clause,[],[f91])).
% 1.45/0.56  fof(f91,plain,(
% 1.45/0.56    spl3_1 <=> r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.45/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.45/0.56  fof(f251,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r1_tarski(X1,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X0,X0,X0)))) )),
% 1.45/0.56    inference(superposition,[],[f235,f59])).
% 1.45/0.56  fof(f235,plain,(
% 1.45/0.56    ( ! [X4,X5] : (r1_tarski(X5,k3_tarski(k6_enumset1(X4,X4,X4,X4,X4,X4,X4,X5)))) )),
% 1.45/0.56    inference(superposition,[],[f223,f118])).
% 1.45/0.56  fof(f118,plain,(
% 1.45/0.56    ( ! [X8,X9] : (k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X9) = k6_enumset1(X8,X8,X8,X8,X8,X9,X8,X9)) )),
% 1.45/0.56    inference(superposition,[],[f52,f54])).
% 1.45/0.56  fof(f54,plain,(
% 1.45/0.56    ( ! [X0] : (k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) = X0) )),
% 1.45/0.56    inference(definition_unfolding,[],[f27,f50])).
% 1.45/0.56  fof(f27,plain,(
% 1.45/0.56    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 1.45/0.56    inference(cnf_transformation,[],[f17])).
% 1.45/0.56  fof(f17,plain,(
% 1.45/0.56    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 1.45/0.56    inference(rectify,[],[f1])).
% 1.45/0.56  fof(f1,axiom,(
% 1.45/0.56    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 1.45/0.56  fof(f52,plain,(
% 1.45/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) )),
% 1.45/0.56    inference(definition_unfolding,[],[f43,f50,f45,f49])).
% 1.45/0.56  fof(f43,plain,(
% 1.45/0.56    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 1.45/0.56    inference(cnf_transformation,[],[f6])).
% 1.45/0.56  fof(f6,axiom,(
% 1.45/0.56    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 1.45/0.56  fof(f223,plain,(
% 1.45/0.56    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X0,X1,X0)))) )),
% 1.45/0.56    inference(superposition,[],[f143,f59])).
% 1.45/0.56  fof(f143,plain,(
% 1.45/0.56    ( ! [X10,X9] : (r1_tarski(X9,k3_tarski(k6_enumset1(X9,X9,X9,X9,X9,X10,X9,X10)))) )),
% 1.45/0.56    inference(superposition,[],[f55,f118])).
% 1.45/0.56  fof(f98,plain,(
% 1.45/0.56    ~spl3_1 | spl3_2),
% 1.45/0.56    inference(avatar_split_clause,[],[f89,f95,f91])).
% 1.45/0.56  fof(f89,plain,(
% 1.45/0.56    sK2 = k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))) | ~r1_tarski(sK2,k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.45/0.56    inference(resolution,[],[f86,f33])).
% 1.45/0.56  fof(f33,plain,(
% 1.45/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.45/0.56    inference(cnf_transformation,[],[f22])).
% 1.45/0.56  fof(f22,plain,(
% 1.45/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.56    inference(flattening,[],[f21])).
% 1.45/0.56  fof(f21,plain,(
% 1.45/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.45/0.56    inference(nnf_transformation,[],[f2])).
% 1.45/0.56  fof(f2,axiom,(
% 1.45/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.45/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.45/0.56  fof(f86,plain,(
% 1.45/0.56    r1_tarski(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 1.45/0.56    inference(forward_demodulation,[],[f53,f59])).
% 1.45/0.56  fof(f53,plain,(
% 1.45/0.56    r1_tarski(k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),sK2)),
% 1.45/0.56    inference(definition_unfolding,[],[f25,f50,f49])).
% 1.45/0.56  fof(f25,plain,(
% 1.45/0.56    r1_tarski(k2_xboole_0(k2_tarski(sK0,sK1),sK2),sK2)),
% 1.45/0.56    inference(cnf_transformation,[],[f20])).
% 1.45/0.56  % SZS output end Proof for theBenchmark
% 1.45/0.56  % (28047)------------------------------
% 1.45/0.56  % (28047)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (28047)Termination reason: Refutation
% 1.45/0.56  
% 1.45/0.56  % (28047)Memory used [KB]: 11001
% 1.45/0.56  % (28047)Time elapsed: 0.127 s
% 1.45/0.56  % (28047)------------------------------
% 1.45/0.56  % (28047)------------------------------
% 1.45/0.56  % (28032)Success in time 0.189 s
%------------------------------------------------------------------------------
