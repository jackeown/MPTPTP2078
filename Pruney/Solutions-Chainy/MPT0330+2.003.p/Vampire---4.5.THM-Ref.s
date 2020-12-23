%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:42:59 EST 2020

% Result     : Theorem 4.95s
% Output     : Refutation 4.95s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 352 expanded)
%              Number of leaves         :   18 ( 113 expanded)
%              Depth                    :   16
%              Number of atoms          :  133 ( 479 expanded)
%              Number of equality atoms :   32 ( 262 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2676,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1248,f1712,f2675])).

fof(f2675,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f2674])).

fof(f2674,plain,
    ( $false
    | spl6_2 ),
    inference(subsumption_resolution,[],[f2672,f27])).

fof(f27,plain,(
    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
    & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3,X4,X5] :
        ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
        & r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
   => ( ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))
      & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
      & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0,X1,X2,X3,X4,X5] :
      ( ~ r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5)))
      & r1_tarski(X1,k2_zfmisc_1(X4,X5))
      & r1_tarski(X0,k2_zfmisc_1(X2,X3)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] :
        ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
          & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
       => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( r1_tarski(X1,k2_zfmisc_1(X4,X5))
        & r1_tarski(X0,k2_zfmisc_1(X2,X3)) )
     => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

fof(f2672,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))
    | spl6_2 ),
    inference(resolution,[],[f2663,f1061])).

fof(f1061,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_zfmisc_1(X3,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0))))
      | ~ r1_tarski(X2,k2_zfmisc_1(X3,X0)) ) ),
    inference(superposition,[],[f1030,f52])).

fof(f52,plain,(
    ! [X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f31,f48,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f32,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f35,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f41,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f42,f43])).

fof(f43,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f42,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f41,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f32,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f31,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1030,plain,(
    ! [X6,X8,X7,X5] :
      ( r1_tarski(X8,k2_zfmisc_1(X5,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))))
      | ~ r1_tarski(X8,k2_zfmisc_1(X5,X6)) ) ),
    inference(superposition,[],[f56,f96])).

fof(f96,plain,(
    ! [X21,X22,X20] : k2_zfmisc_1(X20,X21) = k3_xboole_0(k2_zfmisc_1(X20,X21),k2_zfmisc_1(X20,k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22)))) ),
    inference(resolution,[],[f67,f51])).

fof(f51,plain,(
    ! [X0,X1] : r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f29,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f33,f48])).

fof(f33,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f29,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_zfmisc_1(X2,X0) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ) ),
    inference(resolution,[],[f37,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) )
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => ( r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
        & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_xboole_0(X1,X0))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f38,f30])).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k3_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
      | ~ r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
     => r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

fof(f2663,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5))))
    | spl6_2 ),
    inference(resolution,[],[f1247,f656])).

fof(f656,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X2,k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X3))
      | ~ r1_tarski(X2,k2_zfmisc_1(X0,X3)) ) ),
    inference(superposition,[],[f636,f52])).

fof(f636,plain,(
    ! [X6,X8,X7,X5] :
      ( r1_tarski(X8,k2_zfmisc_1(k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X7)),X6))
      | ~ r1_tarski(X8,k2_zfmisc_1(X5,X6)) ) ),
    inference(superposition,[],[f56,f75])).

fof(f75,plain,(
    ! [X14,X15,X16] : k2_zfmisc_1(X14,X15) = k3_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X16)),X15)) ),
    inference(resolution,[],[f66,f51])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    inference(resolution,[],[f36,f34])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1247,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5))))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f1245])).

fof(f1245,plain,
    ( spl6_2
  <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f1712,plain,(
    spl6_1 ),
    inference(avatar_contradiction_clause,[],[f1711])).

fof(f1711,plain,
    ( $false
    | spl6_1 ),
    inference(subsumption_resolution,[],[f1710,f26])).

fof(f26,plain,(
    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) ),
    inference(cnf_transformation,[],[f25])).

fof(f1710,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))
    | spl6_1 ),
    inference(resolution,[],[f1706,f1030])).

fof(f1706,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5))))
    | spl6_1 ),
    inference(resolution,[],[f1243,f636])).

fof(f1243,plain,
    ( ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5))))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f1241])).

fof(f1241,plain,
    ( spl6_1
  <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f1248,plain,
    ( ~ spl6_1
    | ~ spl6_2 ),
    inference(avatar_split_clause,[],[f385,f1245,f1241])).

fof(f385,plain,
    ( ~ r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5))))
    | ~ r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) ),
    inference(resolution,[],[f50,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X2,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X2,X1)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

fof(f50,plain,(
    ~ r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) ),
    inference(definition_unfolding,[],[f28,f49,f49,f49])).

fof(f28,plain,(
    ~ r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n015.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:49:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.48  % (8567)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (8577)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.48  % (8566)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (8568)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (8569)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (8575)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.49  % (8573)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (8572)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (8565)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (8574)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (8564)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.50  % (8562)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (8576)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (8573)Refutation not found, incomplete strategy% (8573)------------------------------
% 0.21/0.50  % (8573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8573)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8573)Memory used [KB]: 10618
% 0.21/0.50  % (8573)Time elapsed: 0.077 s
% 0.21/0.50  % (8573)------------------------------
% 0.21/0.50  % (8573)------------------------------
% 0.21/0.51  % (8570)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.52  % (8578)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.27/0.54  % (8563)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.27/0.55  % (8579)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.51/0.56  % (8571)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 4.95/1.00  % (8571)Refutation found. Thanks to Tanya!
% 4.95/1.00  % SZS status Theorem for theBenchmark
% 4.95/1.00  % SZS output start Proof for theBenchmark
% 4.95/1.00  fof(f2676,plain,(
% 4.95/1.00    $false),
% 4.95/1.00    inference(avatar_sat_refutation,[],[f1248,f1712,f2675])).
% 4.95/1.00  fof(f2675,plain,(
% 4.95/1.00    spl6_2),
% 4.95/1.00    inference(avatar_contradiction_clause,[],[f2674])).
% 4.95/1.00  fof(f2674,plain,(
% 4.95/1.00    $false | spl6_2),
% 4.95/1.00    inference(subsumption_resolution,[],[f2672,f27])).
% 4.95/1.00  fof(f27,plain,(
% 4.95/1.00    r1_tarski(sK1,k2_zfmisc_1(sK4,sK5))),
% 4.95/1.00    inference(cnf_transformation,[],[f25])).
% 4.95/1.00  fof(f25,plain,(
% 4.95/1.00    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 4.95/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f18,f24])).
% 4.95/1.00  fof(f24,plain,(
% 4.95/1.00    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => (~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5))) & r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) & r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)))),
% 4.95/1.00    introduced(choice_axiom,[])).
% 4.95/1.00  fof(f18,plain,(
% 4.95/1.00    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3)))),
% 4.95/1.00    inference(flattening,[],[f17])).
% 4.95/1.00  fof(f17,plain,(
% 4.95/1.00    ? [X0,X1,X2,X3,X4,X5] : (~r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))) & (r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))))),
% 4.95/1.00    inference(ennf_transformation,[],[f16])).
% 4.95/1.00  fof(f16,negated_conjecture,(
% 4.95/1.00    ~! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 4.95/1.00    inference(negated_conjecture,[],[f15])).
% 4.95/1.00  fof(f15,conjecture,(
% 4.95/1.00    ! [X0,X1,X2,X3,X4,X5] : ((r1_tarski(X1,k2_zfmisc_1(X4,X5)) & r1_tarski(X0,k2_zfmisc_1(X2,X3))) => r1_tarski(k2_xboole_0(X0,X1),k2_zfmisc_1(k2_xboole_0(X2,X4),k2_xboole_0(X3,X5))))),
% 4.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).
% 4.95/1.00  fof(f2672,plain,(
% 4.95/1.00    ~r1_tarski(sK1,k2_zfmisc_1(sK4,sK5)) | spl6_2),
% 4.95/1.00    inference(resolution,[],[f2663,f1061])).
% 4.95/1.00  fof(f1061,plain,(
% 4.95/1.00    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_zfmisc_1(X3,k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)))) | ~r1_tarski(X2,k2_zfmisc_1(X3,X0))) )),
% 4.95/1.00    inference(superposition,[],[f1030,f52])).
% 4.95/1.00  fof(f52,plain,(
% 4.95/1.00    ( ! [X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) = k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)) )),
% 4.95/1.00    inference(definition_unfolding,[],[f31,f48,f48])).
% 4.95/1.00  fof(f48,plain,(
% 4.95/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 4.95/1.00    inference(definition_unfolding,[],[f32,f47])).
% 4.95/1.00  fof(f47,plain,(
% 4.95/1.00    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 4.95/1.00    inference(definition_unfolding,[],[f35,f46])).
% 4.95/1.00  fof(f46,plain,(
% 4.95/1.00    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 4.95/1.00    inference(definition_unfolding,[],[f40,f45])).
% 4.95/1.00  fof(f45,plain,(
% 4.95/1.00    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 4.95/1.00    inference(definition_unfolding,[],[f41,f44])).
% 4.95/1.00  fof(f44,plain,(
% 4.95/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 4.95/1.00    inference(definition_unfolding,[],[f42,f43])).
% 4.95/1.00  fof(f43,plain,(
% 4.95/1.00    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 4.95/1.00    inference(cnf_transformation,[],[f12])).
% 4.95/1.00  fof(f12,axiom,(
% 4.95/1.00    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 4.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 4.95/1.00  fof(f42,plain,(
% 4.95/1.00    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 4.95/1.00    inference(cnf_transformation,[],[f11])).
% 4.95/1.00  fof(f11,axiom,(
% 4.95/1.00    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 4.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 4.95/1.00  fof(f41,plain,(
% 4.95/1.00    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 4.95/1.00    inference(cnf_transformation,[],[f10])).
% 4.95/1.00  fof(f10,axiom,(
% 4.95/1.00    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 4.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 4.95/1.00  fof(f40,plain,(
% 4.95/1.00    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 4.95/1.00    inference(cnf_transformation,[],[f9])).
% 4.95/1.00  fof(f9,axiom,(
% 4.95/1.00    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 4.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 4.95/1.00  fof(f35,plain,(
% 4.95/1.00    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 4.95/1.00    inference(cnf_transformation,[],[f8])).
% 4.95/1.00  fof(f8,axiom,(
% 4.95/1.00    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 4.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 4.95/1.00  fof(f32,plain,(
% 4.95/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 4.95/1.00    inference(cnf_transformation,[],[f7])).
% 4.95/1.00  fof(f7,axiom,(
% 4.95/1.00    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 4.95/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 4.95/1.00  fof(f31,plain,(
% 4.95/1.00    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 4.95/1.00    inference(cnf_transformation,[],[f6])).
% 4.95/1.01  fof(f6,axiom,(
% 4.95/1.01    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 4.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 4.95/1.01  fof(f1030,plain,(
% 4.95/1.01    ( ! [X6,X8,X7,X5] : (r1_tarski(X8,k2_zfmisc_1(X5,k3_tarski(k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) | ~r1_tarski(X8,k2_zfmisc_1(X5,X6))) )),
% 4.95/1.01    inference(superposition,[],[f56,f96])).
% 4.95/1.01  fof(f96,plain,(
% 4.95/1.01    ( ! [X21,X22,X20] : (k2_zfmisc_1(X20,X21) = k3_xboole_0(k2_zfmisc_1(X20,X21),k2_zfmisc_1(X20,k3_tarski(k6_enumset1(X21,X21,X21,X21,X21,X21,X21,X22))))) )),
% 4.95/1.01    inference(resolution,[],[f67,f51])).
% 4.95/1.01  fof(f51,plain,(
% 4.95/1.01    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 4.95/1.01    inference(definition_unfolding,[],[f29,f49])).
% 4.95/1.01  fof(f49,plain,(
% 4.95/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 4.95/1.01    inference(definition_unfolding,[],[f33,f48])).
% 4.95/1.01  fof(f33,plain,(
% 4.95/1.01    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 4.95/1.01    inference(cnf_transformation,[],[f13])).
% 4.95/1.01  fof(f13,axiom,(
% 4.95/1.01    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 4.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 4.95/1.01  fof(f29,plain,(
% 4.95/1.01    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 4.95/1.01    inference(cnf_transformation,[],[f4])).
% 4.95/1.01  fof(f4,axiom,(
% 4.95/1.01    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 4.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).
% 4.95/1.01  fof(f67,plain,(
% 4.95/1.01    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_zfmisc_1(X2,X0) = k3_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 4.95/1.01    inference(resolution,[],[f37,f34])).
% 4.95/1.01  fof(f34,plain,(
% 4.95/1.01    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 4.95/1.01    inference(cnf_transformation,[],[f19])).
% 4.95/1.01  fof(f19,plain,(
% 4.95/1.01    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 4.95/1.01    inference(ennf_transformation,[],[f3])).
% 4.95/1.01  fof(f3,axiom,(
% 4.95/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 4.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 4.95/1.01  fof(f37,plain,(
% 4.95/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) | ~r1_tarski(X0,X1)) )),
% 4.95/1.01    inference(cnf_transformation,[],[f20])).
% 4.95/1.01  fof(f20,plain,(
% 4.95/1.01    ! [X0,X1,X2] : ((r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) | ~r1_tarski(X0,X1))),
% 4.95/1.01    inference(ennf_transformation,[],[f14])).
% 4.95/1.01  fof(f14,axiom,(
% 4.95/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) => (r1_tarski(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))))),
% 4.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).
% 4.95/1.01  fof(f56,plain,(
% 4.95/1.01    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_xboole_0(X1,X0)) | r1_tarski(X2,X0)) )),
% 4.95/1.01    inference(superposition,[],[f38,f30])).
% 4.95/1.01  fof(f30,plain,(
% 4.95/1.01    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 4.95/1.01    inference(cnf_transformation,[],[f1])).
% 4.95/1.01  fof(f1,axiom,(
% 4.95/1.01    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 4.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 4.95/1.01  fof(f38,plain,(
% 4.95/1.01    ( ! [X2,X0,X1] : (~r1_tarski(X0,k3_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 4.95/1.01    inference(cnf_transformation,[],[f21])).
% 4.95/1.01  fof(f21,plain,(
% 4.95/1.01    ! [X0,X1,X2] : (r1_tarski(X0,X1) | ~r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 4.95/1.01    inference(ennf_transformation,[],[f2])).
% 4.95/1.01  fof(f2,axiom,(
% 4.95/1.01    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) => r1_tarski(X0,X1))),
% 4.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).
% 4.95/1.01  fof(f2663,plain,(
% 4.95/1.01    ~r1_tarski(sK1,k2_zfmisc_1(sK4,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) | spl6_2),
% 4.95/1.01    inference(resolution,[],[f1247,f656])).
% 4.95/1.01  fof(f656,plain,(
% 4.95/1.01    ( ! [X2,X0,X3,X1] : (r1_tarski(X2,k2_zfmisc_1(k3_tarski(k6_enumset1(X1,X1,X1,X1,X1,X1,X1,X0)),X3)) | ~r1_tarski(X2,k2_zfmisc_1(X0,X3))) )),
% 4.95/1.01    inference(superposition,[],[f636,f52])).
% 4.95/1.01  fof(f636,plain,(
% 4.95/1.01    ( ! [X6,X8,X7,X5] : (r1_tarski(X8,k2_zfmisc_1(k3_tarski(k6_enumset1(X5,X5,X5,X5,X5,X5,X5,X7)),X6)) | ~r1_tarski(X8,k2_zfmisc_1(X5,X6))) )),
% 4.95/1.01    inference(superposition,[],[f56,f75])).
% 4.95/1.01  fof(f75,plain,(
% 4.95/1.01    ( ! [X14,X15,X16] : (k2_zfmisc_1(X14,X15) = k3_xboole_0(k2_zfmisc_1(X14,X15),k2_zfmisc_1(k3_tarski(k6_enumset1(X14,X14,X14,X14,X14,X14,X14,X16)),X15))) )),
% 4.95/1.01    inference(resolution,[],[f66,f51])).
% 4.95/1.01  fof(f66,plain,(
% 4.95/1.01    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 4.95/1.01    inference(resolution,[],[f36,f34])).
% 4.95/1.01  fof(f36,plain,(
% 4.95/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 4.95/1.01    inference(cnf_transformation,[],[f20])).
% 4.95/1.01  fof(f1247,plain,(
% 4.95/1.01    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) | spl6_2),
% 4.95/1.01    inference(avatar_component_clause,[],[f1245])).
% 4.95/1.01  fof(f1245,plain,(
% 4.95/1.01    spl6_2 <=> r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5))))),
% 4.95/1.01    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 4.95/1.01  fof(f1712,plain,(
% 4.95/1.01    spl6_1),
% 4.95/1.01    inference(avatar_contradiction_clause,[],[f1711])).
% 4.95/1.01  fof(f1711,plain,(
% 4.95/1.01    $false | spl6_1),
% 4.95/1.01    inference(subsumption_resolution,[],[f1710,f26])).
% 4.95/1.01  fof(f26,plain,(
% 4.95/1.01    r1_tarski(sK0,k2_zfmisc_1(sK2,sK3))),
% 4.95/1.01    inference(cnf_transformation,[],[f25])).
% 4.95/1.01  fof(f1710,plain,(
% 4.95/1.01    ~r1_tarski(sK0,k2_zfmisc_1(sK2,sK3)) | spl6_1),
% 4.95/1.01    inference(resolution,[],[f1706,f1030])).
% 4.95/1.01  fof(f1706,plain,(
% 4.95/1.01    ~r1_tarski(sK0,k2_zfmisc_1(sK2,k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) | spl6_1),
% 4.95/1.01    inference(resolution,[],[f1243,f636])).
% 4.95/1.01  fof(f1243,plain,(
% 4.95/1.01    ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) | spl6_1),
% 4.95/1.01    inference(avatar_component_clause,[],[f1241])).
% 4.95/1.01  fof(f1241,plain,(
% 4.95/1.01    spl6_1 <=> r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5))))),
% 4.95/1.01    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 4.95/1.01  fof(f1248,plain,(
% 4.95/1.01    ~spl6_1 | ~spl6_2),
% 4.95/1.01    inference(avatar_split_clause,[],[f385,f1245,f1241])).
% 4.95/1.01  fof(f385,plain,(
% 4.95/1.01    ~r1_tarski(sK1,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5)))) | ~r1_tarski(sK0,k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5))))),
% 4.95/1.01    inference(resolution,[],[f50,f53])).
% 4.95/1.01  fof(f53,plain,(
% 4.95/1.01    ( ! [X2,X0,X1] : (r1_tarski(k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X2)),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.95/1.01    inference(definition_unfolding,[],[f39,f49])).
% 4.95/1.01  fof(f39,plain,(
% 4.95/1.01    ( ! [X2,X0,X1] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)) )),
% 4.95/1.01    inference(cnf_transformation,[],[f23])).
% 4.95/1.01  fof(f23,plain,(
% 4.95/1.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | ~r1_tarski(X2,X1) | ~r1_tarski(X0,X1))),
% 4.95/1.01    inference(flattening,[],[f22])).
% 4.95/1.01  fof(f22,plain,(
% 4.95/1.01    ! [X0,X1,X2] : (r1_tarski(k2_xboole_0(X0,X2),X1) | (~r1_tarski(X2,X1) | ~r1_tarski(X0,X1)))),
% 4.95/1.01    inference(ennf_transformation,[],[f5])).
% 4.95/1.01  fof(f5,axiom,(
% 4.95/1.01    ! [X0,X1,X2] : ((r1_tarski(X2,X1) & r1_tarski(X0,X1)) => r1_tarski(k2_xboole_0(X0,X2),X1))),
% 4.95/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).
% 4.95/1.01  fof(f50,plain,(
% 4.95/1.01    ~r1_tarski(k3_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k2_zfmisc_1(k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK4)),k3_tarski(k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK5))))),
% 4.95/1.01    inference(definition_unfolding,[],[f28,f49,f49,f49])).
% 4.95/1.01  fof(f28,plain,(
% 4.95/1.01    ~r1_tarski(k2_xboole_0(sK0,sK1),k2_zfmisc_1(k2_xboole_0(sK2,sK4),k2_xboole_0(sK3,sK5)))),
% 4.95/1.01    inference(cnf_transformation,[],[f25])).
% 4.95/1.01  % SZS output end Proof for theBenchmark
% 4.95/1.01  % (8571)------------------------------
% 4.95/1.01  % (8571)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.95/1.01  % (8571)Termination reason: Refutation
% 4.95/1.01  
% 4.95/1.01  % (8571)Memory used [KB]: 18166
% 4.95/1.01  % (8571)Time elapsed: 0.548 s
% 4.95/1.01  % (8571)------------------------------
% 4.95/1.01  % (8571)------------------------------
% 4.95/1.01  % (8561)Success in time 0.644 s
%------------------------------------------------------------------------------
