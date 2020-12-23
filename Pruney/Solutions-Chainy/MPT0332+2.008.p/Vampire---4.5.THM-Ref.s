%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:09 EST 2020

% Result     : Theorem 1.42s
% Output     : Refutation 1.42s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 624 expanded)
%              Number of leaves         :   29 ( 221 expanded)
%              Depth                    :   18
%              Number of atoms          :  180 ( 738 expanded)
%              Number of equality atoms :   88 ( 598 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    9 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1343,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f73,f294,f311,f434,f440,f994,f1219,f1337,f1338])).

fof(f1338,plain,
    ( k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | sK2 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1337,plain,
    ( spl3_50
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f1331,f1216,f1333])).

fof(f1333,plain,
    ( spl3_50
  <=> k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f1216,plain,
    ( spl3_46
  <=> r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f1331,plain,
    ( k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl3_46 ),
    inference(resolution,[],[f1218,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f34,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f35,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f40,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f35,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f34,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f1218,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f1216])).

fof(f1219,plain,
    ( spl3_46
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f1214,f421,f1216])).

fof(f421,plain,
    ( spl3_21
  <=> k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f1214,plain,
    ( r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f1213,f100])).

fof(f100,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f98,f74])).

fof(f74,plain,(
    ! [X0] : k5_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f32,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f32,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f98,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f41,f96])).

fof(f96,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(forward_demodulation,[],[f95,f30])).

fof(f95,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0) ),
    inference(forward_demodulation,[],[f52,f53])).

fof(f53,plain,(
    ! [X0] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0 ),
    inference(definition_unfolding,[],[f29,f48])).

fof(f29,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f52,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0))) ),
    inference(definition_unfolding,[],[f28,f49])).

fof(f49,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f38,f48])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f28,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f41,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f1213,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f1180,f32])).

fof(f1180,plain,
    ( r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2))
    | ~ spl3_21 ),
    inference(superposition,[],[f229,f423])).

fof(f423,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f421])).

fof(f229,plain,(
    ! [X2,X1] : r1_tarski(k5_xboole_0(X2,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))),k5_xboole_0(X1,X2)) ),
    inference(superposition,[],[f210,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0)) ),
    inference(definition_unfolding,[],[f31,f48,f48])).

fof(f31,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f210,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))),k5_xboole_0(X0,X1)) ),
    inference(backward_demodulation,[],[f105,f100])).

fof(f105,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))),k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f55,f41])).

fof(f55,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,X1)) ),
    inference(definition_unfolding,[],[f33,f50])).

fof(f50,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f36,f49])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).

fof(f994,plain,
    ( spl3_39
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f993,f291,f793])).

fof(f793,plain,
    ( spl3_39
  <=> sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f291,plain,
    ( spl3_9
  <=> sK2 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f993,plain,
    ( sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f955,f30])).

fof(f955,plain,
    ( k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k1_xboole_0)
    | ~ spl3_9 ),
    inference(superposition,[],[f790,f293])).

fof(f293,plain,
    ( sK2 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f291])).

fof(f790,plain,(
    ! [X28,X27] : k5_xboole_0(X28,X27) = k5_xboole_0(k5_xboole_0(X27,X28),k1_xboole_0) ),
    inference(forward_demodulation,[],[f761,f74])).

fof(f761,plain,(
    ! [X28,X27] : k5_xboole_0(k5_xboole_0(X27,X28),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X28,X27)) ),
    inference(superposition,[],[f651,f651])).

fof(f651,plain,(
    ! [X39,X38] : k5_xboole_0(X39,X38) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X38,X39)) ),
    inference(superposition,[],[f88,f74])).

fof(f88,plain,(
    ! [X6,X7,X5] : k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6)) ),
    inference(superposition,[],[f41,f32])).

fof(f440,plain,
    ( spl3_21
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f413,f291,f421])).

fof(f413,plain,
    ( k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl3_9 ),
    inference(superposition,[],[f251,f293])).

fof(f251,plain,(
    ! [X8,X7] : k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7 ),
    inference(superposition,[],[f213,f213])).

fof(f213,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f100,f32])).

fof(f434,plain,
    ( spl3_23
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f411,f291,f431])).

fof(f431,plain,
    ( spl3_23
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f411,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2)
    | ~ spl3_9 ),
    inference(superposition,[],[f213,f293])).

fof(f311,plain,
    ( ~ spl3_12
    | spl3_1 ),
    inference(avatar_split_clause,[],[f306,f60,f308])).

fof(f308,plain,
    ( spl3_12
  <=> sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f60,plain,
    ( spl3_1
  <=> sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f306,plain,
    ( sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f305,f54])).

fof(f305,plain,
    ( sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))
    | spl3_1 ),
    inference(forward_demodulation,[],[f62,f41])).

fof(f62,plain,
    ( sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f60])).

fof(f294,plain,
    ( spl3_9
    | spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f278,f70,f65,f291])).

fof(f65,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f70,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f278,plain,
    ( sK2 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))
    | spl3_2
    | spl3_3 ),
    inference(unit_resulting_resolution,[],[f67,f72,f211])).

fof(f211,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X0,X0,X0,X0,X0,X1)))) = X2 ) ),
    inference(backward_demodulation,[],[f179,f100])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X0,X0,X0,X0,X0,X1)))))) = X2 ) ),
    inference(forward_demodulation,[],[f58,f41])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k4_enumset1(X0,X0,X0,X0,X0,X1)),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X0,X0,X0,X0,X0,X1))))) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f42,f50,f47])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X2,k2_tarski(X0,X1)) = X2
      | r2_hidden(X1,X2)
      | r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(X2,k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).

fof(f72,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f67,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f65])).

fof(f73,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f25,f70])).

fof(f25,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    & ~ r2_hidden(sK1,sK2)
    & ~ r2_hidden(sK0,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).

fof(f23,plain,
    ( ? [X0,X1,X2] :
        ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) )
   => ( sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
      & ~ r2_hidden(sK1,sK2)
      & ~ r2_hidden(sK0,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
      & ~ r2_hidden(X1,X2)
      & ~ r2_hidden(X0,X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
          & ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ~ ( k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2
        & ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).

fof(f68,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f26,f65])).

fof(f26,plain,(
    ~ r2_hidden(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f63,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f51,f60])).

fof(f51,plain,(
    sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))) ),
    inference(definition_unfolding,[],[f27,f50,f48,f47,f47])).

fof(f27,plain,(
    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:59:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.41  % (28794)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.45  % (28784)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (28788)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (28800)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (28792)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (28798)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (28795)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (28793)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (28796)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (28789)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (28786)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (28791)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (28799)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.49  % (28787)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (28801)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (28790)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.51  % (28797)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.29/0.52  % (28785)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 1.42/0.56  % (28790)Refutation found. Thanks to Tanya!
% 1.42/0.56  % SZS status Theorem for theBenchmark
% 1.42/0.56  % SZS output start Proof for theBenchmark
% 1.42/0.56  fof(f1343,plain,(
% 1.42/0.56    $false),
% 1.42/0.56    inference(avatar_sat_refutation,[],[f63,f68,f73,f294,f311,f434,f440,f994,f1219,f1337,f1338])).
% 1.42/0.56  fof(f1338,plain,(
% 1.42/0.56    k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) != k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) != k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) | sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))))),
% 1.42/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.42/0.56  fof(f1337,plain,(
% 1.42/0.56    spl3_50 | ~spl3_46),
% 1.42/0.56    inference(avatar_split_clause,[],[f1331,f1216,f1333])).
% 1.42/0.56  fof(f1333,plain,(
% 1.42/0.56    spl3_50 <=> k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 1.42/0.56  fof(f1216,plain,(
% 1.42/0.56    spl3_46 <=> r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.42/0.56  fof(f1331,plain,(
% 1.42/0.56    k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) = k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl3_46),
% 1.42/0.56    inference(resolution,[],[f1218,f57])).
% 1.42/0.56  fof(f57,plain,(
% 1.42/0.56    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = X1) )),
% 1.42/0.56    inference(definition_unfolding,[],[f39,f48])).
% 1.42/0.56  fof(f48,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f34,f47])).
% 1.42/0.56  fof(f47,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 1.42/0.56    inference(definition_unfolding,[],[f35,f46])).
% 1.42/0.56  fof(f46,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 1.42/0.56    inference(definition_unfolding,[],[f40,f45])).
% 1.42/0.56  fof(f45,plain,(
% 1.42/0.56    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 1.42/0.56    inference(definition_unfolding,[],[f43,f44])).
% 1.42/0.56  fof(f44,plain,(
% 1.42/0.56    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f15])).
% 1.42/0.56  fof(f15,axiom,(
% 1.42/0.56    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 1.42/0.56  fof(f43,plain,(
% 1.42/0.56    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f14])).
% 1.42/0.56  fof(f14,axiom,(
% 1.42/0.56    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 1.42/0.56  fof(f40,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f13])).
% 1.42/0.56  fof(f13,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 1.42/0.56  fof(f35,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f12])).
% 1.42/0.56  fof(f12,axiom,(
% 1.42/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 1.42/0.56  fof(f34,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f16])).
% 1.42/0.56  fof(f16,axiom,(
% 1.42/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.42/0.56  fof(f39,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f21])).
% 1.42/0.56  fof(f21,plain,(
% 1.42/0.56    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 1.42/0.56    inference(ennf_transformation,[],[f4])).
% 1.42/0.56  fof(f4,axiom,(
% 1.42/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).
% 1.42/0.56  fof(f1218,plain,(
% 1.42/0.56    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) | ~spl3_46),
% 1.42/0.56    inference(avatar_component_clause,[],[f1216])).
% 1.42/0.56  fof(f1219,plain,(
% 1.42/0.56    spl3_46 | ~spl3_21),
% 1.42/0.56    inference(avatar_split_clause,[],[f1214,f421,f1216])).
% 1.42/0.56  fof(f421,plain,(
% 1.42/0.56    spl3_21 <=> k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.42/0.56  fof(f1214,plain,(
% 1.42/0.56    r1_tarski(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) | ~spl3_21),
% 1.42/0.56    inference(forward_demodulation,[],[f1213,f100])).
% 1.42/0.56  fof(f100,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 1.42/0.56    inference(forward_demodulation,[],[f98,f74])).
% 1.42/0.56  fof(f74,plain,(
% 1.42/0.56    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.42/0.56    inference(superposition,[],[f32,f30])).
% 1.42/0.56  fof(f30,plain,(
% 1.42/0.56    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.56    inference(cnf_transformation,[],[f8])).
% 1.42/0.56  fof(f8,axiom,(
% 1.42/0.56    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 1.42/0.56  fof(f32,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f2])).
% 1.42/0.56  fof(f2,axiom,(
% 1.42/0.56    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.42/0.56  fof(f98,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 1.42/0.56    inference(superposition,[],[f41,f96])).
% 1.42/0.56  fof(f96,plain,(
% 1.42/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 1.42/0.56    inference(forward_demodulation,[],[f95,f30])).
% 1.42/0.56  fof(f95,plain,(
% 1.42/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),X0)) )),
% 1.42/0.56    inference(forward_demodulation,[],[f52,f53])).
% 1.42/0.56  fof(f53,plain,(
% 1.42/0.56    ( ! [X0] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)) = X0) )),
% 1.42/0.56    inference(definition_unfolding,[],[f29,f48])).
% 1.42/0.56  fof(f29,plain,(
% 1.42/0.56    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.42/0.56    inference(cnf_transformation,[],[f5])).
% 1.42/0.56  fof(f5,axiom,(
% 1.42/0.56    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).
% 1.42/0.56  fof(f52,plain,(
% 1.42/0.56    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k5_xboole_0(X0,k1_xboole_0),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,k1_xboole_0)))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f28,f49])).
% 1.42/0.56  fof(f49,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f38,f48])).
% 1.42/0.56  fof(f38,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f10])).
% 1.42/0.56  fof(f10,axiom,(
% 1.42/0.56    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.42/0.56  fof(f28,plain,(
% 1.42/0.56    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f6])).
% 1.42/0.56  fof(f6,axiom,(
% 1.42/0.56    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 1.42/0.56  fof(f41,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f9])).
% 1.42/0.56  fof(f9,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.42/0.56  fof(f1213,plain,(
% 1.42/0.56    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) | ~spl3_21),
% 1.42/0.56    inference(forward_demodulation,[],[f1180,f32])).
% 1.42/0.56  fof(f1180,plain,(
% 1.42/0.56    r1_tarski(k5_xboole_0(sK2,k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)) | ~spl3_21),
% 1.42/0.56    inference(superposition,[],[f229,f423])).
% 1.42/0.56  fof(f423,plain,(
% 1.42/0.56    k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_21),
% 1.42/0.56    inference(avatar_component_clause,[],[f421])).
% 1.42/0.56  fof(f229,plain,(
% 1.42/0.56    ( ! [X2,X1] : (r1_tarski(k5_xboole_0(X2,k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,X1))),k5_xboole_0(X1,X2))) )),
% 1.42/0.56    inference(superposition,[],[f210,f54])).
% 1.42/0.56  fof(f54,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) = k3_tarski(k4_enumset1(X1,X1,X1,X1,X1,X0))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f31,f48,f48])).
% 1.42/0.56  fof(f31,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f1])).
% 1.42/0.56  fof(f1,axiom,(
% 1.42/0.56    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.42/0.56  fof(f210,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))),k5_xboole_0(X0,X1))) )),
% 1.42/0.56    inference(backward_demodulation,[],[f105,f100])).
% 1.42/0.56  fof(f105,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))),k5_xboole_0(X0,X1))) )),
% 1.42/0.56    inference(forward_demodulation,[],[f55,f41])).
% 1.42/0.56  fof(f55,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X0,X1))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f33,f50])).
% 1.42/0.56  fof(f50,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) )),
% 1.42/0.56    inference(definition_unfolding,[],[f36,f49])).
% 1.42/0.56  fof(f36,plain,(
% 1.42/0.56    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f3])).
% 1.42/0.56  fof(f3,axiom,(
% 1.42/0.56    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.42/0.56  fof(f33,plain,(
% 1.42/0.56    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 1.42/0.56    inference(cnf_transformation,[],[f11])).
% 1.42/0.56  fof(f11,axiom,(
% 1.42/0.56    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t96_xboole_1)).
% 1.42/0.56  fof(f994,plain,(
% 1.42/0.56    spl3_39 | ~spl3_9),
% 1.42/0.56    inference(avatar_split_clause,[],[f993,f291,f793])).
% 1.42/0.56  fof(f793,plain,(
% 1.42/0.56    spl3_39 <=> sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.42/0.56  fof(f291,plain,(
% 1.42/0.56    spl3_9 <=> sK2 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.42/0.56  fof(f993,plain,(
% 1.42/0.56    sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_9),
% 1.42/0.56    inference(forward_demodulation,[],[f955,f30])).
% 1.42/0.56  fof(f955,plain,(
% 1.42/0.56    k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) = k5_xboole_0(sK2,k1_xboole_0) | ~spl3_9),
% 1.42/0.56    inference(superposition,[],[f790,f293])).
% 1.42/0.56  fof(f293,plain,(
% 1.42/0.56    sK2 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl3_9),
% 1.42/0.56    inference(avatar_component_clause,[],[f291])).
% 1.42/0.56  fof(f790,plain,(
% 1.42/0.56    ( ! [X28,X27] : (k5_xboole_0(X28,X27) = k5_xboole_0(k5_xboole_0(X27,X28),k1_xboole_0)) )),
% 1.42/0.56    inference(forward_demodulation,[],[f761,f74])).
% 1.42/0.56  fof(f761,plain,(
% 1.42/0.56    ( ! [X28,X27] : (k5_xboole_0(k5_xboole_0(X27,X28),k1_xboole_0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X28,X27))) )),
% 1.42/0.56    inference(superposition,[],[f651,f651])).
% 1.42/0.56  fof(f651,plain,(
% 1.42/0.56    ( ! [X39,X38] : (k5_xboole_0(X39,X38) = k5_xboole_0(k1_xboole_0,k5_xboole_0(X38,X39))) )),
% 1.42/0.56    inference(superposition,[],[f88,f74])).
% 1.42/0.56  fof(f88,plain,(
% 1.42/0.56    ( ! [X6,X7,X5] : (k5_xboole_0(X5,k5_xboole_0(X6,X7)) = k5_xboole_0(X7,k5_xboole_0(X5,X6))) )),
% 1.42/0.56    inference(superposition,[],[f41,f32])).
% 1.42/0.56  fof(f440,plain,(
% 1.42/0.56    spl3_21 | ~spl3_9),
% 1.42/0.56    inference(avatar_split_clause,[],[f413,f291,f421])).
% 1.42/0.56  fof(f413,plain,(
% 1.42/0.56    k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))) = k5_xboole_0(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl3_9),
% 1.42/0.56    inference(superposition,[],[f251,f293])).
% 1.42/0.56  fof(f251,plain,(
% 1.42/0.56    ( ! [X8,X7] : (k5_xboole_0(k5_xboole_0(X8,X7),X8) = X7) )),
% 1.42/0.56    inference(superposition,[],[f213,f213])).
% 1.42/0.56  fof(f213,plain,(
% 1.42/0.56    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 1.42/0.56    inference(superposition,[],[f100,f32])).
% 1.42/0.56  fof(f434,plain,(
% 1.42/0.56    spl3_23 | ~spl3_9),
% 1.42/0.56    inference(avatar_split_clause,[],[f411,f291,f431])).
% 1.42/0.56  fof(f431,plain,(
% 1.42/0.56    spl3_23 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2)),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.42/0.56  fof(f411,plain,(
% 1.42/0.56    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),sK2) | ~spl3_9),
% 1.42/0.56    inference(superposition,[],[f213,f293])).
% 1.42/0.56  fof(f311,plain,(
% 1.42/0.56    ~spl3_12 | spl3_1),
% 1.42/0.56    inference(avatar_split_clause,[],[f306,f60,f308])).
% 1.42/0.56  fof(f308,plain,(
% 1.42/0.56    spl3_12 <=> sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.42/0.56  fof(f60,plain,(
% 1.42/0.56    spl3_1 <=> sK2 = k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.42/0.56  fof(f306,plain,(
% 1.42/0.56    sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))))) | spl3_1),
% 1.42/0.56    inference(forward_demodulation,[],[f305,f54])).
% 1.42/0.56  fof(f305,plain,(
% 1.42/0.56    sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))) | spl3_1),
% 1.42/0.56    inference(forward_demodulation,[],[f62,f41])).
% 1.42/0.56  fof(f62,plain,(
% 1.42/0.56    sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))) | spl3_1),
% 1.42/0.56    inference(avatar_component_clause,[],[f60])).
% 1.42/0.56  fof(f294,plain,(
% 1.42/0.56    spl3_9 | spl3_2 | spl3_3),
% 1.42/0.56    inference(avatar_split_clause,[],[f278,f70,f65,f291])).
% 1.42/0.56  fof(f65,plain,(
% 1.42/0.56    spl3_2 <=> r2_hidden(sK1,sK2)),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.42/0.56  fof(f70,plain,(
% 1.42/0.56    spl3_3 <=> r2_hidden(sK0,sK2)),
% 1.42/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.42/0.56  fof(f278,plain,(
% 1.42/0.56    sK2 = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))) | (spl3_2 | spl3_3)),
% 1.42/0.56    inference(unit_resulting_resolution,[],[f67,f72,f211])).
% 1.42/0.56  fof(f211,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | r2_hidden(X0,X2) | k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X0,X0,X0,X0,X0,X1)))) = X2) )),
% 1.42/0.56    inference(backward_demodulation,[],[f179,f100])).
% 1.42/0.56  fof(f179,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | r2_hidden(X0,X2) | k5_xboole_0(X2,k5_xboole_0(X2,k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X0,X0,X0,X0,X0,X1)))))) = X2) )),
% 1.42/0.56    inference(forward_demodulation,[],[f58,f41])).
% 1.42/0.56  fof(f58,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (k5_xboole_0(X2,k5_xboole_0(k5_xboole_0(X2,k4_enumset1(X0,X0,X0,X0,X0,X1)),k3_tarski(k4_enumset1(X2,X2,X2,X2,X2,k4_enumset1(X0,X0,X0,X0,X0,X1))))) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.42/0.56    inference(definition_unfolding,[],[f42,f50,f47])).
% 1.42/0.56  fof(f42,plain,(
% 1.42/0.56    ( ! [X2,X0,X1] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2)) )),
% 1.42/0.56    inference(cnf_transformation,[],[f22])).
% 1.42/0.56  fof(f22,plain,(
% 1.42/0.56    ! [X0,X1,X2] : (k4_xboole_0(X2,k2_tarski(X0,X1)) = X2 | r2_hidden(X1,X2) | r2_hidden(X0,X2))),
% 1.42/0.56    inference(ennf_transformation,[],[f17])).
% 1.42/0.56  fof(f17,axiom,(
% 1.42/0.56    ! [X0,X1,X2] : ~(k4_xboole_0(X2,k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_zfmisc_1)).
% 1.42/0.56  fof(f72,plain,(
% 1.42/0.56    ~r2_hidden(sK0,sK2) | spl3_3),
% 1.42/0.56    inference(avatar_component_clause,[],[f70])).
% 1.42/0.56  fof(f67,plain,(
% 1.42/0.56    ~r2_hidden(sK1,sK2) | spl3_2),
% 1.42/0.56    inference(avatar_component_clause,[],[f65])).
% 1.42/0.56  fof(f73,plain,(
% 1.42/0.56    ~spl3_3),
% 1.42/0.56    inference(avatar_split_clause,[],[f25,f70])).
% 1.42/0.56  fof(f25,plain,(
% 1.42/0.56    ~r2_hidden(sK0,sK2)),
% 1.42/0.56    inference(cnf_transformation,[],[f24])).
% 1.42/0.56  fof(f24,plain,(
% 1.42/0.56    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)),
% 1.42/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f20,f23])).
% 1.42/0.56  fof(f23,plain,(
% 1.42/0.56    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) => (sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) & ~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2))),
% 1.42/0.56    introduced(choice_axiom,[])).
% 1.42/0.56  fof(f20,plain,(
% 1.42/0.56    ? [X0,X1,X2] : (k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.42/0.56    inference(ennf_transformation,[],[f19])).
% 1.42/0.56  fof(f19,negated_conjecture,(
% 1.42/0.56    ~! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.42/0.56    inference(negated_conjecture,[],[f18])).
% 1.42/0.56  fof(f18,conjecture,(
% 1.42/0.56    ! [X0,X1,X2] : ~(k4_xboole_0(k2_xboole_0(X2,k2_tarski(X0,X1)),k2_tarski(X0,X1)) != X2 & ~r2_hidden(X1,X2) & ~r2_hidden(X0,X2))),
% 1.42/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_zfmisc_1)).
% 1.42/0.56  fof(f68,plain,(
% 1.42/0.56    ~spl3_2),
% 1.42/0.56    inference(avatar_split_clause,[],[f26,f65])).
% 1.42/0.56  fof(f26,plain,(
% 1.42/0.56    ~r2_hidden(sK1,sK2)),
% 1.42/0.56    inference(cnf_transformation,[],[f24])).
% 1.42/0.56  fof(f63,plain,(
% 1.42/0.56    ~spl3_1),
% 1.42/0.56    inference(avatar_split_clause,[],[f51,f60])).
% 1.42/0.56  fof(f51,plain,(
% 1.42/0.56    sK2 != k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k5_xboole_0(k5_xboole_0(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k4_enumset1(k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))),
% 1.42/0.56    inference(definition_unfolding,[],[f27,f50,f48,f47,f47])).
% 1.42/0.56  fof(f27,plain,(
% 1.42/0.56    sK2 != k4_xboole_0(k2_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))),
% 1.42/0.56    inference(cnf_transformation,[],[f24])).
% 1.42/0.56  % SZS output end Proof for theBenchmark
% 1.42/0.56  % (28790)------------------------------
% 1.42/0.56  % (28790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.42/0.56  % (28790)Termination reason: Refutation
% 1.42/0.56  
% 1.42/0.56  % (28790)Memory used [KB]: 7291
% 1.42/0.56  % (28790)Time elapsed: 0.100 s
% 1.42/0.56  % (28790)------------------------------
% 1.42/0.56  % (28790)------------------------------
% 1.42/0.57  % (28783)Success in time 0.209 s
%------------------------------------------------------------------------------
