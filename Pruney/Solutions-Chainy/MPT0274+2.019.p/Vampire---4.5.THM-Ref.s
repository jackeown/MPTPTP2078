%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:22 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 511 expanded)
%              Number of leaves         :   17 ( 173 expanded)
%              Depth                    :   17
%              Number of atoms          :  209 ( 718 expanded)
%              Number of equality atoms :   74 ( 496 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f83,f86,f111,f134,f154])).

fof(f154,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(trivial_inequality_removal,[],[f152])).

fof(f152,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_1
    | ~ spl3_2 ),
    inference(superposition,[],[f142,f75])).

fof(f75,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl3_2
  <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f142,plain,
    ( ! [X1] : k4_enumset1(X1,X1,X1,X1,X1,sK1) != k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(X1,X1,X1,X1,X1,sK1))))))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f139,f48])).

fof(f48,plain,(
    ! [X0,X1] : k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f26,f41,f41])).

fof(f41,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f28,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f33,f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f37,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f33,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f26,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f139,plain,
    ( ! [X1] : k4_enumset1(X1,X1,X1,X1,X1,sK1) != k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,sK1),k4_enumset1(X1,X1,X1,X1,X1,sK1),k4_enumset1(X1,X1,X1,X1,X1,sK1),k4_enumset1(X1,X1,X1,X1,X1,sK1),k4_enumset1(X1,X1,X1,X1,X1,sK1),sK2)))))
    | ~ spl3_1 ),
    inference(resolution,[],[f136,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) != X0 ) ),
    inference(forward_demodulation,[],[f49,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) != X0 ) ),
    inference(definition_unfolding,[],[f32,f44])).

fof(f44,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) ),
    inference(definition_unfolding,[],[f29,f43])).

fof(f43,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f30,f42])).

fof(f42,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f41])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f30,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f136,plain,
    ( ! [X1] : ~ r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),sK2)
    | ~ spl3_1 ),
    inference(resolution,[],[f70,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X0),X2) ) ),
    inference(superposition,[],[f52,f48])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f36,f41])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f70,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl3_1
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f134,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(trivial_inequality_removal,[],[f132])).

fof(f132,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f116,f75])).

fof(f116,plain,
    ( ! [X0] : k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0))))))
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f114,f48])).

fof(f114,plain,
    ( ! [X0] : k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),sK2)))))
    | ~ spl3_3 ),
    inference(resolution,[],[f81,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k5_xboole_0(X2,k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))))) ) ),
    inference(resolution,[],[f61,f52])).

fof(f81,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f111,plain,
    ( spl3_1
    | spl3_2
    | spl3_3 ),
    inference(avatar_contradiction_clause,[],[f110])).

fof(f110,plain,
    ( $false
    | spl3_1
    | spl3_2
    | spl3_3 ),
    inference(trivial_inequality_removal,[],[f108])).

fof(f108,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)
    | spl3_1
    | spl3_2
    | spl3_3 ),
    inference(superposition,[],[f74,f103])).

fof(f103,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))
    | spl3_1
    | spl3_3 ),
    inference(resolution,[],[f96,f82])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f96,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK2)
        | k4_enumset1(X8,X8,X8,X8,X8,sK1) = k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,sK1),k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(X8,X8,X8,X8,X8,sK1)))))) )
    | spl3_1 ),
    inference(forward_demodulation,[],[f89,f48])).

fof(f89,plain,
    ( ! [X8] :
        ( r2_hidden(X8,sK2)
        | k4_enumset1(X8,X8,X8,X8,X8,sK1) = k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,sK1),k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(X8,X8,X8,X8,X8,sK1),k4_enumset1(X8,X8,X8,X8,X8,sK1),k4_enumset1(X8,X8,X8,X8,X8,sK1),k4_enumset1(X8,X8,X8,X8,X8,sK1),k4_enumset1(X8,X8,X8,X8,X8,sK1),sK2))))) )
    | spl3_1 ),
    inference(resolution,[],[f64,f71])).

fof(f71,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,X2)
      | r2_hidden(X0,X2)
      | k4_enumset1(X0,X0,X0,X0,X0,X1) = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k5_xboole_0(X2,k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2))))) ) ),
    inference(resolution,[],[f62,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f35,f41])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(k2_tarski(X0,X2),X1)
      | r2_hidden(X2,X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ r1_xboole_0(k2_tarski(X0,X2),X1)
        & ~ r2_hidden(X2,X1)
        & ~ r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) = X0 ) ),
    inference(forward_demodulation,[],[f50,f34])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f31,f44])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f74,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f86,plain,
    ( spl3_3
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f85,f73,f69,f80])).

fof(f85,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f84,f48])).

fof(f84,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)))))
    | r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f45,f34])).

fof(f45,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f25,f41,f44,f41])).

fof(f25,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).

fof(f20,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f83,plain,
    ( ~ spl3_3
    | spl3_2 ),
    inference(avatar_split_clause,[],[f78,f73,f80])).

fof(f78,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f77,f48])).

fof(f77,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)))))
    | ~ r2_hidden(sK0,sK2) ),
    inference(forward_demodulation,[],[f47,f34])).

fof(f47,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f23,f41,f44,f41])).

fof(f23,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,
    ( ~ spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f67,f73,f69])).

fof(f67,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f66,f48])).

fof(f66,plain,
    ( k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)))))
    | ~ r2_hidden(sK1,sK2) ),
    inference(forward_demodulation,[],[f46,f34])).

fof(f46,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)))) ),
    inference(definition_unfolding,[],[f24,f41,f44,f41])).

fof(f24,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 17:12:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.46  % (1332)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.46  % (1327)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (1341)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (1337)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (1342)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (1331)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (1327)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (1340)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (1339)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (1335)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.47  % (1329)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (1337)Refutation not found, incomplete strategy% (1337)------------------------------
% 0.20/0.48  % (1337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (1333)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.48  % (1338)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (1337)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (1337)Memory used [KB]: 10618
% 0.20/0.48  % (1337)Time elapsed: 0.064 s
% 0.20/0.48  % (1337)------------------------------
% 0.20/0.48  % (1337)------------------------------
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f155,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f76,f83,f86,f111,f134,f154])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    ~spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f153])).
% 0.20/0.49  fof(f153,plain,(
% 0.20/0.49    $false | (~spl3_1 | ~spl3_2)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f152])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) | (~spl3_1 | ~spl3_2)),
% 0.20/0.49    inference(superposition,[],[f142,f75])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))) | ~spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f73])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    spl3_2 <=> k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.49  fof(f142,plain,(
% 0.20/0.49    ( ! [X1] : (k4_enumset1(X1,X1,X1,X1,X1,sK1) != k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(X1,X1,X1,X1,X1,sK1))))))) ) | ~spl3_1),
% 0.20/0.49    inference(forward_demodulation,[],[f139,f48])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_enumset1(X0,X0,X0,X0,X0,X1) = k4_enumset1(X1,X1,X1,X1,X1,X0)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f26,f41,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f28,f40])).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f33,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f37,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,axiom,(
% 0.20/0.49    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.49  fof(f139,plain,(
% 0.20/0.49    ( ! [X1] : (k4_enumset1(X1,X1,X1,X1,X1,sK1) != k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),k5_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(X1,X1,X1,X1,X1,sK1),k4_enumset1(X1,X1,X1,X1,X1,sK1),k4_enumset1(X1,X1,X1,X1,X1,sK1),k4_enumset1(X1,X1,X1,X1,X1,sK1),k4_enumset1(X1,X1,X1,X1,X1,sK1),sK2)))))) ) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f136,f61])).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) != X0) )),
% 0.20/0.49    inference(forward_demodulation,[],[f49,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) != X0) )),
% 0.20/0.49    inference(definition_unfolding,[],[f32,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f29,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f30,f42])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.20/0.49    inference(definition_unfolding,[],[f27,f41])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,axiom,(
% 0.20/0.49    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.49    inference(nnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ( ! [X1] : (~r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,sK1),sK2)) ) | ~spl3_1),
% 0.20/0.49    inference(resolution,[],[f70,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k4_enumset1(X1,X1,X1,X1,X1,X0),X2)) )),
% 0.20/0.49    inference(superposition,[],[f52,f48])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f36,f41])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    r2_hidden(sK1,sK2) | ~spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f69])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    spl3_1 <=> r2_hidden(sK1,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ~spl3_2 | ~spl3_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f133])).
% 0.20/0.49  fof(f133,plain,(
% 0.20/0.49    $false | (~spl3_2 | ~spl3_3)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f132])).
% 0.20/0.49  fof(f132,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) | (~spl3_2 | ~spl3_3)),
% 0.20/0.49    inference(superposition,[],[f116,f75])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X0] : (k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0))))))) ) | ~spl3_3),
% 0.20/0.49    inference(forward_demodulation,[],[f114,f48])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0] : (k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,X0),sK2)))))) ) | ~spl3_3),
% 0.20/0.49    inference(resolution,[],[f81,f63])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X0,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) != k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k5_xboole_0(X2,k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2)))))) )),
% 0.20/0.49    inference(resolution,[],[f61,f52])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    r2_hidden(sK0,sK2) | ~spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f80])).
% 0.20/0.49  fof(f80,plain,(
% 0.20/0.49    spl3_3 <=> r2_hidden(sK0,sK2)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl3_1 | spl3_2 | spl3_3),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f110])).
% 0.20/0.49  fof(f110,plain,(
% 0.20/0.49    $false | (spl3_1 | spl3_2 | spl3_3)),
% 0.20/0.49    inference(trivial_inequality_removal,[],[f108])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) | (spl3_1 | spl3_2 | spl3_3)),
% 0.20/0.49    inference(superposition,[],[f74,f103])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))) | (spl3_1 | spl3_3)),
% 0.20/0.49    inference(resolution,[],[f96,f82])).
% 0.20/0.49  fof(f82,plain,(
% 0.20/0.49    ~r2_hidden(sK0,sK2) | spl3_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f80])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    ( ! [X8] : (r2_hidden(X8,sK2) | k4_enumset1(X8,X8,X8,X8,X8,sK1) = k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,sK1),k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(X8,X8,X8,X8,X8,sK1))))))) ) | spl3_1),
% 0.20/0.49    inference(forward_demodulation,[],[f89,f48])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X8] : (r2_hidden(X8,sK2) | k4_enumset1(X8,X8,X8,X8,X8,sK1) = k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,sK1),k5_xboole_0(k4_enumset1(X8,X8,X8,X8,X8,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(X8,X8,X8,X8,X8,sK1),k4_enumset1(X8,X8,X8,X8,X8,sK1),k4_enumset1(X8,X8,X8,X8,X8,sK1),k4_enumset1(X8,X8,X8,X8,X8,sK1),k4_enumset1(X8,X8,X8,X8,X8,sK1),sK2)))))) ) | spl3_1),
% 0.20/0.49    inference(resolution,[],[f64,f71])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK2) | spl3_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f69])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r2_hidden(X1,X2) | r2_hidden(X0,X2) | k4_enumset1(X0,X0,X0,X0,X0,X1) = k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k5_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X1),k5_xboole_0(X2,k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),k4_enumset1(X0,X0,X0,X0,X0,X1),X2)))))) )),
% 0.20/0.49    inference(resolution,[],[f62,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(k4_enumset1(X0,X0,X0,X0,X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f35,f41])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_xboole_0(k2_tarski(X0,X2),X1) | r2_hidden(X2,X1) | r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ~(~r1_xboole_0(k2_tarski(X0,X2),X1) & ~r2_hidden(X2,X1) & ~r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k5_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))))) = X0) )),
% 0.20/0.49    inference(forward_demodulation,[],[f50,f34])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)))) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(definition_unfolding,[],[f31,f44])).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f22])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))) | spl3_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f73])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    spl3_3 | spl3_1 | ~spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f85,f73,f69,f80])).
% 0.20/0.49  fof(f85,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f84,f48])).
% 0.20/0.49  fof(f84,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2))))) | r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f45,f34])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) != k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2))))),
% 0.20/0.49    inference(definition_unfolding,[],[f25,f41,f44,f41])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 0.20/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 0.20/0.49    introduced(choice_axiom,[])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 0.20/0.49    inference(nnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,negated_conjecture,(
% 0.20/0.49    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.20/0.49    inference(negated_conjecture,[],[f13])).
% 0.20/0.49  fof(f13,conjecture,(
% 0.20/0.49    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    ~spl3_3 | spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f78,f73,f80])).
% 0.20/0.49  fof(f78,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))) | ~r2_hidden(sK0,sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f77,f48])).
% 0.20/0.49  fof(f77,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2))))) | ~r2_hidden(sK0,sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f47,f34])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ~r2_hidden(sK0,sK2) | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2))))),
% 0.20/0.49    inference(definition_unfolding,[],[f23,f41,f44,f41])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ~spl3_1 | spl3_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f67,f73,f69])).
% 0.20/0.49  fof(f67,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(sK2,sK2,sK2,sK2,sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)))))) | ~r2_hidden(sK1,sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f66,f48])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2))))) | ~r2_hidden(sK1,sK2)),
% 0.20/0.49    inference(forward_demodulation,[],[f46,f34])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK2) | k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k5_xboole_0(k5_xboole_0(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2))))),
% 0.20/0.49    inference(definition_unfolding,[],[f24,f41,f44,f41])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (1327)------------------------------
% 0.20/0.49  % (1327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (1327)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (1327)Memory used [KB]: 6268
% 0.20/0.49  % (1327)Time elapsed: 0.066 s
% 0.20/0.49  % (1327)------------------------------
% 0.20/0.49  % (1327)------------------------------
% 0.20/0.49  % (1326)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.49  % (1320)Success in time 0.139 s
%------------------------------------------------------------------------------
