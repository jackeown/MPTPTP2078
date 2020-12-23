%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:37:39 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :  179 ( 939 expanded)
%              Number of leaves         :   38 ( 340 expanded)
%              Depth                    :   15
%              Number of atoms          :  394 (1279 expanded)
%              Number of equality atoms :  135 ( 866 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1858,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f175,f180,f335,f409,f1189,f1336,f1345,f1808,f1824,f1851,f1856])).

fof(f1856,plain,
    ( ~ spl4_5
    | ~ spl4_13 ),
    inference(avatar_contradiction_clause,[],[f1855])).

fof(f1855,plain,
    ( $false
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f1854,f348])).

fof(f348,plain,(
    ! [X0] : k1_xboole_0 != k1_enumset1(X0,X0,X0) ),
    inference(forward_demodulation,[],[f345,f336])).

fof(f336,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f292,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f292,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(superposition,[],[f165,f57])).

fof(f57,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f165,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(superposition,[],[f116,f106])).

fof(f106,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f59,f96])).

fof(f96,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f65,f64])).

fof(f64,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f65,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f59,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f116,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X2))) ),
    inference(definition_unfolding,[],[f79,f96])).

fof(f79,plain,(
    ! [X2,X0,X1] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).

fof(f345,plain,(
    ! [X0] : k1_enumset1(X0,X0,X0) != k3_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0)) ),
    inference(unit_resulting_resolution,[],[f138,f307])).

fof(f307,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) != k3_xboole_0(X0,k1_enumset1(X1,X1,X1))
      | r2_hidden(X1,X0) ) ),
    inference(backward_demodulation,[],[f127,f301])).

fof(f301,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X1,X1,X2) ),
    inference(superposition,[],[f118,f124])).

fof(f124,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_enumset1(X1,X1,X2))) ),
    inference(backward_demodulation,[],[f101,f102])).

fof(f102,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7))) ),
    inference(definition_unfolding,[],[f94,f96,f92])).

fof(f92,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_enumset1)).

fof(f94,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).

fof(f101,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k1_enumset1(X1,X1,X2))) ),
    inference(definition_unfolding,[],[f80,f96,f100,f64])).

fof(f100,plain,(
    ! [X0] : k1_tarski(X0) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) ),
    inference(definition_unfolding,[],[f60,f99])).

fof(f99,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3))) ),
    inference(definition_unfolding,[],[f91,f98])).

fof(f98,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X6))) ),
    inference(definition_unfolding,[],[f93,f96,f64,f92])).

fof(f93,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).

fof(f91,plain,(
    ! [X2,X0,X3,X1] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).

fof(f60,plain,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

fof(f118,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k1_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) ),
    inference(definition_unfolding,[],[f95,f96,f92])).

fof(f95,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).

fof(f127,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | r2_hidden(X1,X0) ) ),
    inference(forward_demodulation,[],[f110,f102])).

fof(f110,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k3_xboole_0(X0,k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f70,f100,f100])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1))
     => r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).

fof(f138,plain,(
    ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f136,f57])).

fof(f136,plain,(
    ! [X0,X1] : ~ r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0)) ),
    inference(unit_resulting_resolution,[],[f56,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f43])).

fof(f43,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f56,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f1854,plain,
    ( k1_xboole_0 = k1_enumset1(sK0,sK0,sK0)
    | ~ spl4_5
    | ~ spl4_13 ),
    inference(forward_demodulation,[],[f407,f1548])).

fof(f1548,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl4_13 ),
    inference(superposition,[],[f393,f1335])).

fof(f1335,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f1333])).

fof(f1333,plain,
    ( spl4_13
  <=> k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f393,plain,(
    ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X3),X3) ),
    inference(forward_demodulation,[],[f379,f57])).

fof(f379,plain,(
    ! [X4,X3] : k4_xboole_0(k3_xboole_0(X4,X3),X3) = k3_xboole_0(X4,k1_xboole_0) ),
    inference(superposition,[],[f81,f204])).

fof(f204,plain,(
    ! [X1] : k1_xboole_0 = k4_xboole_0(X1,X1) ),
    inference(superposition,[],[f105,f107])).

fof(f107,plain,(
    ! [X0] : k3_tarski(k1_enumset1(X0,X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f61,f96])).

fof(f61,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k3_tarski(k1_enumset1(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0))) ),
    inference(definition_unfolding,[],[f58,f97])).

fof(f97,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f66,f96])).

fof(f66,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f81,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f407,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f406])).

fof(f406,plain,
    ( spl4_5
  <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f1851,plain,
    ( spl4_3
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f1850])).

fof(f1850,plain,
    ( $false
    | spl4_3
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f1837,f334])).

fof(f334,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f332])).

fof(f332,plain,
    ( spl4_3
  <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f1837,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl4_12 ),
    inference(superposition,[],[f165,f1329])).

fof(f1329,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f1328])).

fof(f1328,plain,
    ( spl4_12
  <=> k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f1824,plain,
    ( spl4_5
    | spl4_15 ),
    inference(avatar_contradiction_clause,[],[f1823])).

fof(f1823,plain,
    ( $false
    | spl4_5
    | spl4_15 ),
    inference(subsumption_resolution,[],[f1822,f138])).

fof(f1822,plain,
    ( ! [X0] : r2_hidden(sK3(X0,X0,k1_xboole_0),k1_xboole_0)
    | spl4_5
    | spl4_15 ),
    inference(forward_demodulation,[],[f1821,f966])).

fof(f966,plain,
    ( k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f408,f145,f329])).

fof(f329,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k1_enumset1(X1,X1,X1))
      | k1_enumset1(X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f308,f301])).

fof(f308,plain,(
    ! [X0,X1] :
      ( k1_enumset1(X1,X1,X1) = X0
      | ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k1_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f131,f301])).

fof(f131,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))
      | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0 ) ),
    inference(forward_demodulation,[],[f130,f102])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(forward_demodulation,[],[f113,f102])).

fof(f113,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)))) ) ),
    inference(definition_unfolding,[],[f74,f100,f100])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k1_tarski(X1) = X0
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_tarski(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,k1_tarski(X1))
        | ( k1_tarski(X1) != X0
          & k1_xboole_0 != X0 ) )
      & ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0
        | ~ r1_tarski(X0,k1_tarski(X1)) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,k1_tarski(X1))
    <=> ( k1_tarski(X1) = X0
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

fof(f145,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(unit_resulting_resolution,[],[f134,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f134,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(superposition,[],[f108,f106])).

fof(f108,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1))) ),
    inference(definition_unfolding,[],[f62,f96])).

fof(f62,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f408,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f406])).

fof(f1821,plain,
    ( ! [X0] : r2_hidden(sK3(X0,X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))
    | spl4_15 ),
    inference(forward_demodulation,[],[f1810,f394])).

fof(f394,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k3_xboole_0(X12,X11)) = k4_xboole_0(X11,X12) ),
    inference(forward_demodulation,[],[f383,f106])).

fof(f383,plain,(
    ! [X12,X11] : k4_xboole_0(X11,k3_xboole_0(X12,X11)) = k3_tarski(k1_enumset1(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12),k1_xboole_0)) ),
    inference(superposition,[],[f117,f204])).

fof(f117,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f82,f96])).

fof(f82,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).

fof(f1810,plain,
    ( ! [X0] : r2_hidden(sK3(X0,X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))
    | spl4_15 ),
    inference(unit_resulting_resolution,[],[f1807,f238])).

fof(f238,plain,(
    ! [X2,X3] :
      ( r2_hidden(sK3(X2,X2,X3),X3)
      | k1_xboole_0 = X3 ) ),
    inference(forward_demodulation,[],[f236,f204])).

fof(f236,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X2) = X3
      | r2_hidden(sK3(X2,X2,X3),X3) ) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,(
    ! [X2,X3] :
      ( k4_xboole_0(X2,X2) = X3
      | r2_hidden(sK3(X2,X2,X3),X3)
      | r2_hidden(sK3(X2,X2,X3),X3)
      | k4_xboole_0(X2,X2) = X3 ) ),
    inference(resolution,[],[f89,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X0)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK3(X0,X1,X2),X1)
            | ~ r2_hidden(sK3(X0,X1,X2),X0)
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
              & r2_hidden(sK3(X0,X1,X2),X0) )
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).

fof(f52,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK3(X0,X1,X2),X1)
          | ~ r2_hidden(sK3(X0,X1,X2),X0)
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(sK3(X0,X1,X2),X0) )
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X1)
      | k4_xboole_0(X0,X1) = X2
      | r2_hidden(sK3(X0,X1,X2),X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f1807,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | spl4_15 ),
    inference(avatar_component_clause,[],[f1805])).

fof(f1805,plain,
    ( spl4_15
  <=> k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f1808,plain,
    ( ~ spl4_15
    | spl4_12 ),
    inference(avatar_split_clause,[],[f1371,f1328,f1805])).

fof(f1371,plain,
    ( k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))
    | spl4_12 ),
    inference(forward_demodulation,[],[f1370,f393])).

fof(f1370,plain,
    ( k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) != k4_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0))
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f1330,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

fof(f1330,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))
    | spl4_12 ),
    inference(avatar_component_clause,[],[f1328])).

fof(f1345,plain,
    ( spl4_1
    | spl4_5 ),
    inference(avatar_split_clause,[],[f410,f406,f168])).

fof(f168,plain,
    ( spl4_1
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f410,plain,
    ( r2_hidden(sK0,sK1)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f408,f309])).

fof(f309,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),X1) ) ),
    inference(backward_demodulation,[],[f132,f301])).

fof(f132,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) ) ),
    inference(forward_demodulation,[],[f114,f102])).

fof(f114,plain,(
    ! [X0,X1] :
      ( k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k4_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f78,f100,f100])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
        | r2_hidden(X0,X1) )
      & ( ~ r2_hidden(X0,X1)
        | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1)
    <=> ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

fof(f1336,plain,
    ( spl4_13
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f1190,f332,f1333])).

fof(f1190,plain,
    ( k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f333,f69])).

fof(f333,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f332])).

fof(f1189,plain,
    ( spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f1174,f172,f332])).

fof(f172,plain,
    ( spl4_2
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f1174,plain,
    ( r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f173,f301])).

fof(f173,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f172])).

fof(f409,plain,
    ( ~ spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f325,f168,f406])).

fof(f325,plain,
    ( k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f278,f301])).

fof(f278,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ spl4_1 ),
    inference(unit_resulting_resolution,[],[f169,f133])).

fof(f133,plain,(
    ! [X0,X1] :
      ( k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(forward_demodulation,[],[f115,f102])).

fof(f115,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k4_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1) ) ),
    inference(definition_unfolding,[],[f77,f100,f100])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f169,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f168])).

fof(f335,plain,
    ( ~ spl4_3
    | spl4_2 ),
    inference(avatar_split_clause,[],[f319,f172,f332])).

fof(f319,plain,
    ( ~ r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)
    | spl4_2 ),
    inference(backward_demodulation,[],[f174,f301])).

fof(f174,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f172])).

fof(f180,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f126,f172,f168])).

fof(f126,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f104,f102])).

fof(f104,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(definition_unfolding,[],[f54,f100])).

fof(f54,plain,
    ( r2_hidden(sK0,sK1)
    | r1_tarski(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ r2_hidden(sK0,sK1)
      | ~ r1_tarski(k1_tarski(sK0),sK1) )
    & ( r2_hidden(sK0,sK1)
      | r1_tarski(k1_tarski(sK0),sK1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f41])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( ~ r2_hidden(X0,X1)
          | ~ r1_tarski(k1_tarski(X0),X1) )
        & ( r2_hidden(X0,X1)
          | r1_tarski(k1_tarski(X0),X1) ) )
   => ( ( ~ r2_hidden(sK0,sK1)
        | ~ r1_tarski(k1_tarski(sK0),sK1) )
      & ( r2_hidden(sK0,sK1)
        | r1_tarski(k1_tarski(sK0),sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ~ r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) )
      & ( r2_hidden(X0,X1)
        | r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ? [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <~> r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,negated_conjecture,(
    ~ ! [X0,X1] :
        ( r1_tarski(k1_tarski(X0),X1)
      <=> r2_hidden(X0,X1) ) ),
    inference(negated_conjecture,[],[f30])).

fof(f30,conjecture,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).

fof(f175,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f125,f172,f168])).

fof(f125,plain,
    ( ~ r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)
    | ~ r2_hidden(sK0,sK1) ),
    inference(forward_demodulation,[],[f103,f102])).

fof(f103,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1) ),
    inference(definition_unfolding,[],[f55,f100])).

fof(f55,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ r1_tarski(k1_tarski(sK0),sK1) ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n024.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 09:29:51 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.19/0.50  % (24459)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.52  % (24475)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.19/0.52  % (24467)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.19/0.53  % (24476)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.19/0.53  % (24467)Refutation not found, incomplete strategy% (24467)------------------------------
% 0.19/0.53  % (24467)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.53  % (24467)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.53  
% 0.19/0.53  % (24467)Memory used [KB]: 1663
% 0.19/0.53  % (24467)Time elapsed: 0.130 s
% 0.19/0.53  % (24467)------------------------------
% 0.19/0.53  % (24467)------------------------------
% 0.19/0.53  % (24454)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.19/0.53  % (24468)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.19/0.53  % (24453)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.19/0.55  % (24460)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.19/0.55  % (24455)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.19/0.55  % (24479)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.55  % (24456)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.43/0.55  % (24482)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.43/0.55  % (24481)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.43/0.56  % (24482)Refutation not found, incomplete strategy% (24482)------------------------------
% 1.43/0.56  % (24482)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (24482)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (24482)Memory used [KB]: 1663
% 1.43/0.56  % (24482)Time elapsed: 0.002 s
% 1.43/0.56  % (24482)------------------------------
% 1.43/0.56  % (24482)------------------------------
% 1.43/0.56  % (24458)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.43/0.56  % (24457)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.56  % (24461)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.43/0.56  % (24462)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.56  % (24472)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.57  % (24471)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.43/0.57  % (24464)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.57  % (24474)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.57  % (24477)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.43/0.57  % (24473)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.43/0.57  % (24478)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.43/0.57  % (24480)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.57  % (24463)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.43/0.57  % (24466)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.43/0.57  % (24469)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.58  % (24465)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.58  % (24463)Refutation not found, incomplete strategy% (24463)------------------------------
% 1.43/0.58  % (24463)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (24463)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.58  
% 1.43/0.58  % (24463)Memory used [KB]: 10746
% 1.43/0.58  % (24463)Time elapsed: 0.179 s
% 1.43/0.58  % (24463)------------------------------
% 1.43/0.58  % (24463)------------------------------
% 1.43/0.58  % (24469)Refutation not found, incomplete strategy% (24469)------------------------------
% 1.43/0.58  % (24469)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (24469)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.58  
% 1.43/0.58  % (24469)Memory used [KB]: 10618
% 1.43/0.58  % (24469)Time elapsed: 0.177 s
% 1.43/0.58  % (24469)------------------------------
% 1.43/0.58  % (24469)------------------------------
% 1.43/0.58  % (24470)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.76/0.58  % (24481)Refutation not found, incomplete strategy% (24481)------------------------------
% 1.76/0.58  % (24481)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.58  % (24481)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.58  
% 1.76/0.58  % (24481)Memory used [KB]: 10746
% 1.76/0.58  % (24481)Time elapsed: 0.176 s
% 1.76/0.58  % (24481)------------------------------
% 1.76/0.58  % (24481)------------------------------
% 1.76/0.58  % (24470)Refutation not found, incomplete strategy% (24470)------------------------------
% 1.76/0.58  % (24470)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.58  % (24470)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.58  
% 1.76/0.58  % (24470)Memory used [KB]: 1791
% 1.76/0.58  % (24470)Time elapsed: 0.178 s
% 1.76/0.58  % (24470)------------------------------
% 1.76/0.58  % (24470)------------------------------
% 1.76/0.59  % (24464)Refutation not found, incomplete strategy% (24464)------------------------------
% 1.76/0.59  % (24464)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.76/0.59  % (24464)Termination reason: Refutation not found, incomplete strategy
% 1.76/0.59  
% 1.76/0.59  % (24464)Memory used [KB]: 6268
% 1.76/0.59  % (24464)Time elapsed: 0.187 s
% 1.76/0.59  % (24464)------------------------------
% 1.76/0.59  % (24464)------------------------------
% 2.50/0.71  % (24483)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.67/0.73  % (24473)Refutation found. Thanks to Tanya!
% 2.67/0.73  % SZS status Theorem for theBenchmark
% 2.77/0.73  % SZS output start Proof for theBenchmark
% 2.77/0.73  fof(f1858,plain,(
% 2.77/0.73    $false),
% 2.77/0.73    inference(avatar_sat_refutation,[],[f175,f180,f335,f409,f1189,f1336,f1345,f1808,f1824,f1851,f1856])).
% 2.77/0.73  fof(f1856,plain,(
% 2.77/0.73    ~spl4_5 | ~spl4_13),
% 2.77/0.73    inference(avatar_contradiction_clause,[],[f1855])).
% 2.77/0.73  fof(f1855,plain,(
% 2.77/0.73    $false | (~spl4_5 | ~spl4_13)),
% 2.77/0.73    inference(subsumption_resolution,[],[f1854,f348])).
% 2.77/0.73  fof(f348,plain,(
% 2.77/0.73    ( ! [X0] : (k1_xboole_0 != k1_enumset1(X0,X0,X0)) )),
% 2.77/0.73    inference(forward_demodulation,[],[f345,f336])).
% 2.77/0.73  fof(f336,plain,(
% 2.77/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(k1_xboole_0,X0)) )),
% 2.77/0.73    inference(unit_resulting_resolution,[],[f292,f69])).
% 2.77/0.73  fof(f69,plain,(
% 2.77/0.73    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.77/0.73    inference(cnf_transformation,[],[f36])).
% 2.77/0.73  fof(f36,plain,(
% 2.77/0.73    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.77/0.73    inference(ennf_transformation,[],[f8])).
% 2.77/0.73  fof(f8,axiom,(
% 2.77/0.73    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.77/0.73  fof(f292,plain,(
% 2.77/0.73    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 2.77/0.73    inference(superposition,[],[f165,f57])).
% 2.77/0.73  fof(f57,plain,(
% 2.77/0.73    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 2.77/0.73    inference(cnf_transformation,[],[f10])).
% 2.77/0.73  fof(f10,axiom,(
% 2.77/0.73    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 2.77/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 2.77/0.73  fof(f165,plain,(
% 2.77/0.73    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 2.77/0.73    inference(superposition,[],[f116,f106])).
% 2.77/0.73  fof(f106,plain,(
% 2.77/0.73    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,k1_xboole_0)) = X0) )),
% 2.77/0.73    inference(definition_unfolding,[],[f59,f96])).
% 2.77/0.73  fof(f96,plain,(
% 2.77/0.73    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k1_enumset1(X0,X0,X1))) )),
% 2.77/0.73    inference(definition_unfolding,[],[f65,f64])).
% 2.77/0.74  fof(f64,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f22])).
% 2.77/0.74  fof(f22,axiom,(
% 2.77/0.74    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 2.77/0.74  fof(f65,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f29])).
% 2.77/0.74  fof(f29,axiom,(
% 2.77/0.74    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 2.77/0.74  fof(f59,plain,(
% 2.77/0.74    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 2.77/0.74    inference(cnf_transformation,[],[f6])).
% 2.77/0.74  fof(f6,axiom,(
% 2.77/0.74    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 2.77/0.74  fof(f116,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k3_tarski(k1_enumset1(X0,X0,X2)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f79,f96])).
% 2.77/0.74  fof(f79,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f9])).
% 2.77/0.74  fof(f9,axiom,(
% 2.77/0.74    ! [X0,X1,X2] : r1_tarski(k3_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_xboole_1)).
% 2.77/0.74  fof(f345,plain,(
% 2.77/0.74    ( ! [X0] : (k1_enumset1(X0,X0,X0) != k3_xboole_0(k1_xboole_0,k1_enumset1(X0,X0,X0))) )),
% 2.77/0.74    inference(unit_resulting_resolution,[],[f138,f307])).
% 2.77/0.74  fof(f307,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) != k3_xboole_0(X0,k1_enumset1(X1,X1,X1)) | r2_hidden(X1,X0)) )),
% 2.77/0.74    inference(backward_demodulation,[],[f127,f301])).
% 2.77/0.74  fof(f301,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X1,X1,X2)) )),
% 2.77/0.74    inference(superposition,[],[f118,f124])).
% 2.77/0.74  fof(f124,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),k1_enumset1(X1,X1,X2)))) )),
% 2.77/0.74    inference(backward_demodulation,[],[f101,f102])).
% 2.77/0.74  fof(f102,plain,(
% 2.77/0.74    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k1_enumset1(k1_enumset1(X0,X1,X2),k1_enumset1(X0,X1,X2),k6_enumset1(X3,X3,X3,X3,X4,X5,X6,X7)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f94,f96,f92])).
% 2.77/0.74  fof(f92,plain,(
% 2.77/0.74    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f25])).
% 2.77/0.74  fof(f25,axiom,(
% 2.77/0.74    ! [X0,X1,X2,X3,X4] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_enumset1)).
% 2.77/0.74  fof(f94,plain,(
% 2.77/0.74    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f20])).
% 2.77/0.74  fof(f20,axiom,(
% 2.77/0.74    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k1_enumset1(X0,X1,X2),k3_enumset1(X3,X4,X5,X6,X7))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_enumset1)).
% 2.77/0.74  fof(f101,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k3_tarski(k1_enumset1(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),k1_enumset1(X1,X1,X2)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f80,f96,f100,f64])).
% 2.77/0.74  fof(f100,plain,(
% 2.77/0.74    ( ! [X0] : (k1_tarski(X0) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f60,f99])).
% 2.77/0.74  fof(f99,plain,(
% 2.77/0.74    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f91,f98])).
% 2.77/0.74  fof(f98,plain,(
% 2.77/0.74    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X1),k1_enumset1(X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X3,X4,X5,X6)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f93,f96,f64,f92])).
% 2.77/0.74  fof(f93,plain,(
% 2.77/0.74    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f19])).
% 2.77/0.74  fof(f19,axiom,(
% 2.77/0.74    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_tarski(X0,X1),k3_enumset1(X2,X3,X4,X5,X6))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_enumset1)).
% 2.77/0.74  fof(f91,plain,(
% 2.77/0.74    ( ! [X2,X0,X3,X1] : (k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f24])).
% 2.77/0.74  fof(f24,axiom,(
% 2.77/0.74    ! [X0,X1,X2,X3] : k5_enumset1(X0,X0,X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t85_enumset1)).
% 2.77/0.74  fof(f60,plain,(
% 2.77/0.74    ( ! [X0] : (k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f23])).
% 2.77/0.74  fof(f23,axiom,(
% 2.77/0.74    ! [X0] : k1_tarski(X0) = k2_enumset1(X0,X0,X0,X0)),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_enumset1)).
% 2.77/0.74  fof(f80,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f18])).
% 2.77/0.74  fof(f18,axiom,(
% 2.77/0.74    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k1_tarski(X0),k2_tarski(X1,X2))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).
% 2.77/0.74  fof(f118,plain,(
% 2.77/0.74    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k1_enumset1(k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f95,f96,f92])).
% 2.77/0.74  fof(f95,plain,(
% 2.77/0.74    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f21])).
% 2.77/0.74  fof(f21,axiom,(
% 2.77/0.74    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k3_enumset1(X0,X1,X2,X3,X4),k1_enumset1(X5,X6,X7))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_enumset1)).
% 2.77/0.74  fof(f127,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) != k3_xboole_0(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | r2_hidden(X1,X0)) )),
% 2.77/0.74    inference(forward_demodulation,[],[f110,f102])).
% 2.77/0.74  fof(f110,plain,(
% 2.77/0.74    ( ! [X0,X1] : (r2_hidden(X1,X0) | k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) != k3_xboole_0(X0,k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f70,f100,f100])).
% 2.77/0.74  fof(f70,plain,(
% 2.77/0.74    ( ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f37])).
% 2.77/0.74  fof(f37,plain,(
% 2.77/0.74    ! [X0,X1] : (r2_hidden(X1,X0) | k1_tarski(X1) != k3_xboole_0(X0,k1_tarski(X1)))),
% 2.77/0.74    inference(ennf_transformation,[],[f26])).
% 2.77/0.74  fof(f26,axiom,(
% 2.77/0.74    ! [X0,X1] : (k1_tarski(X1) = k3_xboole_0(X0,k1_tarski(X1)) => r2_hidden(X1,X0))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l29_zfmisc_1)).
% 2.77/0.74  fof(f138,plain,(
% 2.77/0.74    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) )),
% 2.77/0.74    inference(forward_demodulation,[],[f136,f57])).
% 2.77/0.74  fof(f136,plain,(
% 2.77/0.74    ( ! [X0,X1] : (~r2_hidden(X0,k3_xboole_0(X1,k1_xboole_0))) )),
% 2.77/0.74    inference(unit_resulting_resolution,[],[f56,f68])).
% 2.77/0.74  fof(f68,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f44])).
% 2.77/0.74  fof(f44,plain,(
% 2.77/0.74    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.77/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f35,f43])).
% 2.77/0.74  fof(f43,plain,(
% 2.77/0.74    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK2(X0,X1),k3_xboole_0(X0,X1)))),
% 2.77/0.74    introduced(choice_axiom,[])).
% 2.77/0.74  fof(f35,plain,(
% 2.77/0.74    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 2.77/0.74    inference(ennf_transformation,[],[f33])).
% 2.77/0.74  fof(f33,plain,(
% 2.77/0.74    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.77/0.74    inference(rectify,[],[f4])).
% 2.77/0.74  fof(f4,axiom,(
% 2.77/0.74    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 2.77/0.74  fof(f56,plain,(
% 2.77/0.74    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f14])).
% 2.77/0.74  fof(f14,axiom,(
% 2.77/0.74    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).
% 2.77/0.74  fof(f1854,plain,(
% 2.77/0.74    k1_xboole_0 = k1_enumset1(sK0,sK0,sK0) | (~spl4_5 | ~spl4_13)),
% 2.77/0.74    inference(forward_demodulation,[],[f407,f1548])).
% 2.77/0.74  fof(f1548,plain,(
% 2.77/0.74    k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl4_13),
% 2.77/0.74    inference(superposition,[],[f393,f1335])).
% 2.77/0.74  fof(f1335,plain,(
% 2.77/0.74    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl4_13),
% 2.77/0.74    inference(avatar_component_clause,[],[f1333])).
% 2.77/0.74  fof(f1333,plain,(
% 2.77/0.74    spl4_13 <=> k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 2.77/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 2.77/0.74  fof(f393,plain,(
% 2.77/0.74    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X4,X3),X3)) )),
% 2.77/0.74    inference(forward_demodulation,[],[f379,f57])).
% 2.77/0.74  fof(f379,plain,(
% 2.77/0.74    ( ! [X4,X3] : (k4_xboole_0(k3_xboole_0(X4,X3),X3) = k3_xboole_0(X4,k1_xboole_0)) )),
% 2.77/0.74    inference(superposition,[],[f81,f204])).
% 2.77/0.74  fof(f204,plain,(
% 2.77/0.74    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(X1,X1)) )),
% 2.77/0.74    inference(superposition,[],[f105,f107])).
% 2.77/0.74  fof(f107,plain,(
% 2.77/0.74    ( ! [X0] : (k3_tarski(k1_enumset1(X0,X0,X0)) = X0) )),
% 2.77/0.74    inference(definition_unfolding,[],[f61,f96])).
% 2.77/0.74  fof(f61,plain,(
% 2.77/0.74    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 2.77/0.74    inference(cnf_transformation,[],[f32])).
% 2.77/0.74  fof(f32,plain,(
% 2.77/0.74    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 2.77/0.74    inference(rectify,[],[f3])).
% 2.77/0.74  fof(f3,axiom,(
% 2.77/0.74    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 2.77/0.74  fof(f105,plain,(
% 2.77/0.74    ( ! [X0] : (k1_xboole_0 = k3_tarski(k1_enumset1(k4_xboole_0(X0,X0),k4_xboole_0(X0,X0),k4_xboole_0(X0,X0)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f58,f97])).
% 2.77/0.74  fof(f97,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f66,f96])).
% 2.77/0.74  fof(f66,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f2])).
% 2.77/0.74  fof(f2,axiom,(
% 2.77/0.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.77/0.74  fof(f58,plain,(
% 2.77/0.74    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f17])).
% 2.77/0.74  fof(f17,axiom,(
% 2.77/0.74    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 2.77/0.74  fof(f81,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f12])).
% 2.77/0.74  fof(f12,axiom,(
% 2.77/0.74    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_xboole_1)).
% 2.77/0.74  fof(f407,plain,(
% 2.77/0.74    k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl4_5),
% 2.77/0.74    inference(avatar_component_clause,[],[f406])).
% 2.77/0.74  fof(f406,plain,(
% 2.77/0.74    spl4_5 <=> k1_enumset1(sK0,sK0,sK0) = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),
% 2.77/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 2.77/0.74  fof(f1851,plain,(
% 2.77/0.74    spl4_3 | ~spl4_12),
% 2.77/0.74    inference(avatar_contradiction_clause,[],[f1850])).
% 2.77/0.74  fof(f1850,plain,(
% 2.77/0.74    $false | (spl4_3 | ~spl4_12)),
% 2.77/0.74    inference(subsumption_resolution,[],[f1837,f334])).
% 2.77/0.74  fof(f334,plain,(
% 2.77/0.74    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | spl4_3),
% 2.77/0.74    inference(avatar_component_clause,[],[f332])).
% 2.77/0.74  fof(f332,plain,(
% 2.77/0.74    spl4_3 <=> r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1)),
% 2.77/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 2.77/0.74  fof(f1837,plain,(
% 2.77/0.74    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl4_12),
% 2.77/0.74    inference(superposition,[],[f165,f1329])).
% 2.77/0.74  fof(f1329,plain,(
% 2.77/0.74    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) | ~spl4_12),
% 2.77/0.74    inference(avatar_component_clause,[],[f1328])).
% 2.77/0.74  fof(f1328,plain,(
% 2.77/0.74    spl4_12 <=> k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))),
% 2.77/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 2.77/0.74  fof(f1824,plain,(
% 2.77/0.74    spl4_5 | spl4_15),
% 2.77/0.74    inference(avatar_contradiction_clause,[],[f1823])).
% 2.77/0.74  fof(f1823,plain,(
% 2.77/0.74    $false | (spl4_5 | spl4_15)),
% 2.77/0.74    inference(subsumption_resolution,[],[f1822,f138])).
% 2.77/0.74  fof(f1822,plain,(
% 2.77/0.74    ( ! [X0] : (r2_hidden(sK3(X0,X0,k1_xboole_0),k1_xboole_0)) ) | (spl4_5 | spl4_15)),
% 2.77/0.74    inference(forward_demodulation,[],[f1821,f966])).
% 2.77/0.74  fof(f966,plain,(
% 2.77/0.74    k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | spl4_5),
% 2.77/0.74    inference(unit_resulting_resolution,[],[f408,f145,f329])).
% 2.77/0.74  fof(f329,plain,(
% 2.77/0.74    ( ! [X0,X1] : (~r1_tarski(X0,k1_enumset1(X1,X1,X1)) | k1_enumset1(X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 2.77/0.74    inference(forward_demodulation,[],[f308,f301])).
% 2.77/0.74  fof(f308,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k1_enumset1(X1,X1,X1) = X0 | ~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k1_xboole_0 = X0) )),
% 2.77/0.74    inference(backward_demodulation,[],[f131,f301])).
% 2.77/0.74  fof(f131,plain,(
% 2.77/0.74    ( ! [X0,X1] : (~r1_tarski(X0,k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1)) | k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0) )),
% 2.77/0.74    inference(forward_demodulation,[],[f130,f102])).
% 2.77/0.74  fof(f130,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 2.77/0.74    inference(forward_demodulation,[],[f113,f102])).
% 2.77/0.74  fof(f113,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k3_tarski(k1_enumset1(k1_enumset1(X1,X1,X1),k1_enumset1(X1,X1,X1),k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X1))))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f74,f100,f100])).
% 2.77/0.74  fof(f74,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f47])).
% 2.77/0.74  fof(f47,plain,(
% 2.77/0.74    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & (k1_tarski(X1) = X0 | k1_xboole_0 = X0 | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.77/0.74    inference(flattening,[],[f46])).
% 2.77/0.74  fof(f46,plain,(
% 2.77/0.74    ! [X0,X1] : ((r1_tarski(X0,k1_tarski(X1)) | (k1_tarski(X1) != X0 & k1_xboole_0 != X0)) & ((k1_tarski(X1) = X0 | k1_xboole_0 = X0) | ~r1_tarski(X0,k1_tarski(X1))))),
% 2.77/0.74    inference(nnf_transformation,[],[f28])).
% 2.77/0.74  fof(f28,axiom,(
% 2.77/0.74    ! [X0,X1] : (r1_tarski(X0,k1_tarski(X1)) <=> (k1_tarski(X1) = X0 | k1_xboole_0 = X0))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).
% 2.77/0.74  fof(f145,plain,(
% 2.77/0.74    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.77/0.74    inference(unit_resulting_resolution,[],[f134,f83])).
% 2.77/0.74  fof(f83,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f39])).
% 2.77/0.74  fof(f39,plain,(
% 2.77/0.74    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.77/0.74    inference(ennf_transformation,[],[f5])).
% 2.77/0.74  fof(f5,axiom,(
% 2.77/0.74    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.77/0.74  fof(f134,plain,(
% 2.77/0.74    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 2.77/0.74    inference(superposition,[],[f108,f106])).
% 2.77/0.74  fof(f108,plain,(
% 2.77/0.74    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k1_enumset1(X0,X0,X1)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f62,f96])).
% 2.77/0.74  fof(f62,plain,(
% 2.77/0.74    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f15])).
% 2.77/0.74  fof(f15,axiom,(
% 2.77/0.74    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 2.77/0.74  fof(f408,plain,(
% 2.77/0.74    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | spl4_5),
% 2.77/0.74    inference(avatar_component_clause,[],[f406])).
% 2.77/0.74  fof(f1821,plain,(
% 2.77/0.74    ( ! [X0] : (r2_hidden(sK3(X0,X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1)),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1))) ) | spl4_15),
% 2.77/0.74    inference(forward_demodulation,[],[f1810,f394])).
% 2.77/0.74  fof(f394,plain,(
% 2.77/0.74    ( ! [X12,X11] : (k4_xboole_0(X11,k3_xboole_0(X12,X11)) = k4_xboole_0(X11,X12)) )),
% 2.77/0.74    inference(forward_demodulation,[],[f383,f106])).
% 2.77/0.74  fof(f383,plain,(
% 2.77/0.74    ( ! [X12,X11] : (k4_xboole_0(X11,k3_xboole_0(X12,X11)) = k3_tarski(k1_enumset1(k4_xboole_0(X11,X12),k4_xboole_0(X11,X12),k1_xboole_0))) )),
% 2.77/0.74    inference(superposition,[],[f117,f204])).
% 2.77/0.74  fof(f117,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_tarski(k1_enumset1(k4_xboole_0(X0,X1),k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)))) )),
% 2.77/0.74    inference(definition_unfolding,[],[f82,f96])).
% 2.77/0.74  fof(f82,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))) )),
% 2.77/0.74    inference(cnf_transformation,[],[f13])).
% 2.77/0.74  fof(f13,axiom,(
% 2.77/0.74    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_xboole_1)).
% 2.77/0.74  fof(f1810,plain,(
% 2.77/0.74    ( ! [X0] : (r2_hidden(sK3(X0,X0,k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))))) ) | spl4_15),
% 2.77/0.74    inference(unit_resulting_resolution,[],[f1807,f238])).
% 2.77/0.74  fof(f238,plain,(
% 2.77/0.74    ( ! [X2,X3] : (r2_hidden(sK3(X2,X2,X3),X3) | k1_xboole_0 = X3) )),
% 2.77/0.74    inference(forward_demodulation,[],[f236,f204])).
% 2.77/0.74  fof(f236,plain,(
% 2.77/0.74    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = X3 | r2_hidden(sK3(X2,X2,X3),X3)) )),
% 2.77/0.74    inference(duplicate_literal_removal,[],[f234])).
% 2.77/0.74  fof(f234,plain,(
% 2.77/0.74    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = X3 | r2_hidden(sK3(X2,X2,X3),X3) | r2_hidden(sK3(X2,X2,X3),X3) | k4_xboole_0(X2,X2) = X3) )),
% 2.77/0.74    inference(resolution,[],[f89,f88])).
% 2.77/0.74  fof(f88,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) )),
% 2.77/0.74    inference(cnf_transformation,[],[f53])).
% 2.77/0.74  fof(f53,plain,(
% 2.77/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f51,f52])).
% 2.77/0.74  fof(f52,plain,(
% 2.77/0.74    ! [X2,X1,X0] : (? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2))) => ((r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(sK3(X0,X1,X2),X0) | ~r2_hidden(sK3(X0,X1,X2),X2)) & ((~r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),X0)) | r2_hidden(sK3(X0,X1,X2),X2))))),
% 2.77/0.74    introduced(choice_axiom,[])).
% 2.77/0.74  fof(f51,plain,(
% 2.77/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | r2_hidden(X4,X1) | ~r2_hidden(X4,X0)) & ((~r2_hidden(X4,X1) & r2_hidden(X4,X0)) | ~r2_hidden(X4,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/0.74    inference(rectify,[],[f50])).
% 2.77/0.74  fof(f50,plain,(
% 2.77/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : ((r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/0.74    inference(flattening,[],[f49])).
% 2.77/0.74  fof(f49,plain,(
% 2.77/0.74    ! [X0,X1,X2] : ((k4_xboole_0(X0,X1) = X2 | ? [X3] : (((r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r2_hidden(X3,X2)) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (r2_hidden(X3,X1) | ~r2_hidden(X3,X0))) & ((~r2_hidden(X3,X1) & r2_hidden(X3,X0)) | ~r2_hidden(X3,X2))) | k4_xboole_0(X0,X1) != X2))),
% 2.77/0.74    inference(nnf_transformation,[],[f1])).
% 2.77/0.74  fof(f1,axiom,(
% 2.77/0.74    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.77/0.74  fof(f89,plain,(
% 2.77/0.74    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X1) | k4_xboole_0(X0,X1) = X2 | r2_hidden(sK3(X0,X1,X2),X2)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f53])).
% 2.77/0.74  fof(f1807,plain,(
% 2.77/0.74    k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | spl4_15),
% 2.77/0.74    inference(avatar_component_clause,[],[f1805])).
% 2.77/0.74  fof(f1805,plain,(
% 2.77/0.74    spl4_15 <=> k1_xboole_0 = k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)))),
% 2.77/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 2.77/0.74  fof(f1808,plain,(
% 2.77/0.74    ~spl4_15 | spl4_12),
% 2.77/0.74    inference(avatar_split_clause,[],[f1371,f1328,f1805])).
% 2.77/0.74  fof(f1371,plain,(
% 2.77/0.74    k1_xboole_0 != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) | spl4_12),
% 2.77/0.74    inference(forward_demodulation,[],[f1370,f393])).
% 2.77/0.74  fof(f1370,plain,(
% 2.77/0.74    k4_xboole_0(k1_enumset1(sK0,sK0,sK0),k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0))) != k4_xboole_0(k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)),k1_enumset1(sK0,sK0,sK0)) | spl4_12),
% 2.77/0.74    inference(unit_resulting_resolution,[],[f1330,f71])).
% 2.77/0.74  fof(f71,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0) | X0 = X1) )),
% 2.77/0.74    inference(cnf_transformation,[],[f38])).
% 2.77/0.74  fof(f38,plain,(
% 2.77/0.74    ! [X0,X1] : (X0 = X1 | k4_xboole_0(X0,X1) != k4_xboole_0(X1,X0))),
% 2.77/0.74    inference(ennf_transformation,[],[f11])).
% 2.77/0.74  fof(f11,axiom,(
% 2.77/0.74    ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X1,X0) => X0 = X1)),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).
% 2.77/0.74  fof(f1330,plain,(
% 2.77/0.74    k1_enumset1(sK0,sK0,sK0) != k3_xboole_0(sK1,k1_enumset1(sK0,sK0,sK0)) | spl4_12),
% 2.77/0.74    inference(avatar_component_clause,[],[f1328])).
% 2.77/0.74  fof(f1345,plain,(
% 2.77/0.74    spl4_1 | spl4_5),
% 2.77/0.74    inference(avatar_split_clause,[],[f410,f406,f168])).
% 2.77/0.74  fof(f168,plain,(
% 2.77/0.74    spl4_1 <=> r2_hidden(sK0,sK1)),
% 2.77/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 2.77/0.74  fof(f410,plain,(
% 2.77/0.74    r2_hidden(sK0,sK1) | spl4_5),
% 2.77/0.74    inference(unit_resulting_resolution,[],[f408,f309])).
% 2.77/0.74  fof(f309,plain,(
% 2.77/0.74    ( ! [X0,X1] : (r2_hidden(X0,X1) | k1_enumset1(X0,X0,X0) = k4_xboole_0(k1_enumset1(X0,X0,X0),X1)) )),
% 2.77/0.74    inference(backward_demodulation,[],[f132,f301])).
% 2.77/0.74  fof(f132,plain,(
% 2.77/0.74    ( ! [X0,X1] : (r2_hidden(X0,X1) | k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) = k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1)) )),
% 2.77/0.74    inference(forward_demodulation,[],[f114,f102])).
% 2.77/0.74  fof(f114,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) = k4_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1) | r2_hidden(X0,X1)) )),
% 2.77/0.74    inference(definition_unfolding,[],[f78,f100,f100])).
% 2.77/0.74  fof(f78,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f48])).
% 2.77/0.74  fof(f48,plain,(
% 2.77/0.74    ! [X0,X1] : ((k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) & (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)))),
% 2.77/0.74    inference(nnf_transformation,[],[f27])).
% 2.77/0.74  fof(f27,axiom,(
% 2.77/0.74    ! [X0,X1] : (k1_tarski(X0) = k4_xboole_0(k1_tarski(X0),X1) <=> ~r2_hidden(X0,X1))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).
% 2.77/0.74  fof(f1336,plain,(
% 2.77/0.74    spl4_13 | ~spl4_3),
% 2.77/0.74    inference(avatar_split_clause,[],[f1190,f332,f1333])).
% 2.77/0.74  fof(f1190,plain,(
% 2.77/0.74    k1_enumset1(sK0,sK0,sK0) = k3_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl4_3),
% 2.77/0.74    inference(unit_resulting_resolution,[],[f333,f69])).
% 2.77/0.74  fof(f333,plain,(
% 2.77/0.74    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl4_3),
% 2.77/0.74    inference(avatar_component_clause,[],[f332])).
% 2.77/0.74  fof(f1189,plain,(
% 2.77/0.74    spl4_3 | ~spl4_2),
% 2.77/0.74    inference(avatar_split_clause,[],[f1174,f172,f332])).
% 2.77/0.74  fof(f172,plain,(
% 2.77/0.74    spl4_2 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1)),
% 2.77/0.74    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 2.77/0.74  fof(f1174,plain,(
% 2.77/0.74    r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl4_2),
% 2.77/0.74    inference(forward_demodulation,[],[f173,f301])).
% 2.77/0.74  fof(f173,plain,(
% 2.77/0.74    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_2),
% 2.77/0.74    inference(avatar_component_clause,[],[f172])).
% 2.77/0.74  fof(f409,plain,(
% 2.77/0.74    ~spl4_5 | ~spl4_1),
% 2.77/0.74    inference(avatar_split_clause,[],[f325,f168,f406])).
% 2.77/0.74  fof(f325,plain,(
% 2.77/0.74    k1_enumset1(sK0,sK0,sK0) != k4_xboole_0(k1_enumset1(sK0,sK0,sK0),sK1) | ~spl4_1),
% 2.77/0.74    inference(backward_demodulation,[],[f278,f301])).
% 2.77/0.74  fof(f278,plain,(
% 2.77/0.74    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0) != k4_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~spl4_1),
% 2.77/0.74    inference(unit_resulting_resolution,[],[f169,f133])).
% 2.77/0.74  fof(f133,plain,(
% 2.77/0.74    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) != k4_xboole_0(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0),X1) | ~r2_hidden(X0,X1)) )),
% 2.77/0.74    inference(forward_demodulation,[],[f115,f102])).
% 2.77/0.74  fof(f115,plain,(
% 2.77/0.74    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))) != k4_xboole_0(k3_tarski(k1_enumset1(k1_enumset1(X0,X0,X0),k1_enumset1(X0,X0,X0),k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0))),X1)) )),
% 2.77/0.74    inference(definition_unfolding,[],[f77,f100,f100])).
% 2.77/0.74  fof(f77,plain,(
% 2.77/0.74    ( ! [X0,X1] : (~r2_hidden(X0,X1) | k1_tarski(X0) != k4_xboole_0(k1_tarski(X0),X1)) )),
% 2.77/0.74    inference(cnf_transformation,[],[f48])).
% 2.77/0.74  fof(f169,plain,(
% 2.77/0.74    r2_hidden(sK0,sK1) | ~spl4_1),
% 2.77/0.74    inference(avatar_component_clause,[],[f168])).
% 2.77/0.74  fof(f335,plain,(
% 2.77/0.74    ~spl4_3 | spl4_2),
% 2.77/0.74    inference(avatar_split_clause,[],[f319,f172,f332])).
% 2.77/0.74  fof(f319,plain,(
% 2.77/0.74    ~r1_tarski(k1_enumset1(sK0,sK0,sK0),sK1) | spl4_2),
% 2.77/0.74    inference(backward_demodulation,[],[f174,f301])).
% 2.77/0.74  fof(f174,plain,(
% 2.77/0.74    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | spl4_2),
% 2.77/0.74    inference(avatar_component_clause,[],[f172])).
% 2.77/0.74  fof(f180,plain,(
% 2.77/0.74    spl4_1 | spl4_2),
% 2.77/0.74    inference(avatar_split_clause,[],[f126,f172,f168])).
% 2.77/0.74  fof(f126,plain,(
% 2.77/0.74    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | r2_hidden(sK0,sK1)),
% 2.77/0.74    inference(forward_demodulation,[],[f104,f102])).
% 2.77/0.74  fof(f104,plain,(
% 2.77/0.74    r2_hidden(sK0,sK1) | r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.77/0.74    inference(definition_unfolding,[],[f54,f100])).
% 2.77/0.74  fof(f54,plain,(
% 2.77/0.74    r2_hidden(sK0,sK1) | r1_tarski(k1_tarski(sK0),sK1)),
% 2.77/0.74    inference(cnf_transformation,[],[f42])).
% 2.77/0.74  fof(f42,plain,(
% 2.77/0.74    (~r2_hidden(sK0,sK1) | ~r1_tarski(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | r1_tarski(k1_tarski(sK0),sK1))),
% 2.77/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f40,f41])).
% 2.77/0.74  fof(f41,plain,(
% 2.77/0.74    ? [X0,X1] : ((~r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1))) => ((~r2_hidden(sK0,sK1) | ~r1_tarski(k1_tarski(sK0),sK1)) & (r2_hidden(sK0,sK1) | r1_tarski(k1_tarski(sK0),sK1)))),
% 2.77/0.74    introduced(choice_axiom,[])).
% 2.77/0.74  fof(f40,plain,(
% 2.77/0.74    ? [X0,X1] : ((~r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)) & (r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)))),
% 2.77/0.74    inference(nnf_transformation,[],[f34])).
% 2.77/0.74  fof(f34,plain,(
% 2.77/0.74    ? [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <~> r2_hidden(X0,X1))),
% 2.77/0.74    inference(ennf_transformation,[],[f31])).
% 2.77/0.74  fof(f31,negated_conjecture,(
% 2.77/0.74    ~! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.77/0.74    inference(negated_conjecture,[],[f30])).
% 2.77/0.74  fof(f30,conjecture,(
% 2.77/0.74    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 2.77/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_zfmisc_1)).
% 2.77/0.74  fof(f175,plain,(
% 2.77/0.74    ~spl4_1 | ~spl4_2),
% 2.77/0.74    inference(avatar_split_clause,[],[f125,f172,f168])).
% 2.77/0.74  fof(f125,plain,(
% 2.77/0.74    ~r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0),sK1) | ~r2_hidden(sK0,sK1)),
% 2.77/0.74    inference(forward_demodulation,[],[f103,f102])).
% 2.77/0.74  fof(f103,plain,(
% 2.77/0.74    ~r2_hidden(sK0,sK1) | ~r1_tarski(k3_tarski(k1_enumset1(k1_enumset1(sK0,sK0,sK0),k1_enumset1(sK0,sK0,sK0),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK0))),sK1)),
% 2.77/0.74    inference(definition_unfolding,[],[f55,f100])).
% 2.77/0.74  fof(f55,plain,(
% 2.77/0.74    ~r2_hidden(sK0,sK1) | ~r1_tarski(k1_tarski(sK0),sK1)),
% 2.77/0.74    inference(cnf_transformation,[],[f42])).
% 2.77/0.74  % SZS output end Proof for theBenchmark
% 2.77/0.74  % (24473)------------------------------
% 2.77/0.74  % (24473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.77/0.74  % (24473)Termination reason: Refutation
% 2.77/0.74  
% 2.77/0.74  % (24473)Memory used [KB]: 12025
% 2.77/0.74  % (24473)Time elapsed: 0.326 s
% 2.77/0.74  % (24473)------------------------------
% 2.77/0.74  % (24473)------------------------------
% 2.77/0.74  % (24452)Success in time 0.384 s
%------------------------------------------------------------------------------
