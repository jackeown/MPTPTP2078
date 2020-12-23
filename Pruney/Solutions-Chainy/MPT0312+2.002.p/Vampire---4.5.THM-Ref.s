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
% DateTime   : Thu Dec  3 12:42:06 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 243 expanded)
%              Number of leaves         :   22 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  137 ( 341 expanded)
%              Number of equality atoms :   70 ( 227 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f111,f112,f157,f190])).

fof(f190,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f189])).

fof(f189,plain,
    ( $false
    | spl4_7 ),
    inference(trivial_inequality_removal,[],[f173])).

fof(f173,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2)
    | spl4_7 ),
    inference(backward_demodulation,[],[f156,f159])).

fof(f159,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2 ),
    inference(superposition,[],[f94,f34])).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f94,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1 ),
    inference(forward_demodulation,[],[f80,f72])).

fof(f72,plain,(
    ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1 ),
    inference(superposition,[],[f34,f30])).

fof(f30,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

fof(f80,plain,(
    ! [X0,X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f40,f29])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f40,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f156,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl4_7
  <=> k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f157,plain,
    ( ~ spl4_7
    | spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f152,f107,f102,f58,f154])).

fof(f58,plain,
    ( spl4_1
  <=> k2_zfmisc_1(sK0,sK2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k5_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f102,plain,
    ( spl4_4
  <=> sK1 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f107,plain,
    ( spl4_5
  <=> sK3 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f152,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f151,f30])).

fof(f151,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f150,f29])).

fof(f150,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f149,f104])).

fof(f104,plain,
    ( sK1 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f149,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))
    | spl4_1
    | ~ spl4_5 ),
    inference(forward_demodulation,[],[f148,f109])).

fof(f109,plain,
    ( sK3 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f107])).

fof(f148,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)))))
    | spl4_1 ),
    inference(forward_demodulation,[],[f130,f54])).

fof(f54,plain,(
    ! [X0,X1] : k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0) ),
    inference(definition_unfolding,[],[f33,f48,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f36,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f39,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f41,f45])).

fof(f45,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f43,f44])).

fof(f44,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f43,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f33,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f130,plain,
    ( k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK2)))))
    | spl4_1 ),
    inference(superposition,[],[f60,f122])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))))) ),
    inference(forward_demodulation,[],[f121,f40])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] : k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3))))) ),
    inference(forward_demodulation,[],[f56,f40])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) ),
    inference(definition_unfolding,[],[f42,f50,f50,f50])).

fof(f50,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f37,f49])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f35,f48])).

fof(f35,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

fof(f60,plain,
    ( k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k5_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f112,plain,
    ( spl4_4
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f100,f68,f102])).

fof(f68,plain,
    ( spl4_3
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f100,plain,
    ( sK1 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))
    | ~ spl4_3 ),
    inference(resolution,[],[f55,f70])).

fof(f70,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1 ) ),
    inference(definition_unfolding,[],[f38,f49])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f111,plain,
    ( spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f99,f63,f107])).

fof(f63,plain,
    ( spl4_2
  <=> r1_tarski(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f99,plain,
    ( sK3 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))
    | ~ spl4_2 ),
    inference(resolution,[],[f55,f65])).

fof(f65,plain,
    ( r1_tarski(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f71,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f26,f68])).

fof(f26,plain,(
    r1_tarski(sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
    & r1_tarski(sK2,sK3)
    & r1_tarski(sK0,sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f24])).

fof(f24,plain,
    ( ? [X0,X1,X2,X3] :
        ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
        & r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
   => ( k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))
      & r1_tarski(sK2,sK3)
      & r1_tarski(sK0,sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2))
      & r1_tarski(X2,X3)
      & r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_tarski(X2,X3)
          & r1_tarski(X0,X1) )
       => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

fof(f66,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f27,f63])).

fof(f27,plain,(
    r1_tarski(sK2,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f61,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f51,f58])).

fof(f51,plain,(
    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k5_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) ),
    inference(definition_unfolding,[],[f28,f50])).

fof(f28,plain,(
    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:10:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.23/0.45  % (28157)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.23/0.47  % (28143)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.23/0.47  % (28141)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.23/0.48  % (28148)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.23/0.48  % (28155)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.23/0.49  % (28151)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.23/0.49  % (28145)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.23/0.49  % (28146)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.23/0.49  % (28142)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.23/0.49  % (28144)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.23/0.50  % (28150)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.23/0.50  % (28152)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.23/0.51  % (28153)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.23/0.51  % (28147)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.23/0.51  % (28154)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.23/0.51  % (28156)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.23/0.52  % (28149)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.23/0.52  % (28147)Refutation found. Thanks to Tanya!
% 0.23/0.52  % SZS status Theorem for theBenchmark
% 0.23/0.52  % SZS output start Proof for theBenchmark
% 0.23/0.52  fof(f192,plain,(
% 0.23/0.52    $false),
% 0.23/0.52    inference(avatar_sat_refutation,[],[f61,f66,f71,f111,f112,f157,f190])).
% 0.23/0.52  fof(f190,plain,(
% 0.23/0.52    spl4_7),
% 0.23/0.52    inference(avatar_contradiction_clause,[],[f189])).
% 0.23/0.52  fof(f189,plain,(
% 0.23/0.52    $false | spl4_7),
% 0.23/0.52    inference(trivial_inequality_removal,[],[f173])).
% 0.23/0.52  fof(f173,plain,(
% 0.23/0.52    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,sK2) | spl4_7),
% 0.23/0.52    inference(backward_demodulation,[],[f156,f159])).
% 0.23/0.52  fof(f159,plain,(
% 0.23/0.52    ( ! [X2,X1] : (k5_xboole_0(X1,k5_xboole_0(X2,X1)) = X2) )),
% 0.23/0.52    inference(superposition,[],[f94,f34])).
% 0.23/0.52  fof(f34,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f1])).
% 0.23/0.52  fof(f1,axiom,(
% 0.23/0.52    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 0.23/0.52  fof(f94,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) )),
% 0.23/0.52    inference(forward_demodulation,[],[f80,f72])).
% 0.23/0.52  fof(f72,plain,(
% 0.23/0.52    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) )),
% 0.23/0.52    inference(superposition,[],[f34,f30])).
% 0.23/0.52  fof(f30,plain,(
% 0.23/0.52    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.23/0.52    inference(cnf_transformation,[],[f5])).
% 0.23/0.52  fof(f5,axiom,(
% 0.23/0.52    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 0.23/0.52  fof(f80,plain,(
% 0.23/0.52    ( ! [X0,X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 0.23/0.52    inference(superposition,[],[f40,f29])).
% 0.23/0.52  fof(f29,plain,(
% 0.23/0.52    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.23/0.52    inference(cnf_transformation,[],[f7])).
% 0.23/0.52  fof(f7,axiom,(
% 0.23/0.52    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.23/0.52  fof(f40,plain,(
% 0.23/0.52    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.23/0.52    inference(cnf_transformation,[],[f6])).
% 0.23/0.52  fof(f6,axiom,(
% 0.23/0.52    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.23/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.23/0.52  fof(f156,plain,(
% 0.23/0.52    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | spl4_7),
% 0.23/0.52    inference(avatar_component_clause,[],[f154])).
% 0.23/0.52  fof(f154,plain,(
% 0.23/0.52    spl4_7 <=> k2_zfmisc_1(sK0,sK2) = k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3)))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.23/0.52  fof(f157,plain,(
% 0.23/0.52    ~spl4_7 | spl4_1 | ~spl4_4 | ~spl4_5),
% 0.23/0.52    inference(avatar_split_clause,[],[f152,f107,f102,f58,f154])).
% 0.23/0.52  fof(f58,plain,(
% 0.23/0.52    spl4_1 <=> k2_zfmisc_1(sK0,sK2) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k5_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.23/0.52  fof(f102,plain,(
% 0.23/0.52    spl4_4 <=> sK1 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.23/0.52  fof(f107,plain,(
% 0.23/0.52    spl4_5 <=> sK3 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))),
% 0.23/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.23/0.52  fof(f152,plain,(
% 0.23/0.52    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(sK0,k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_4 | ~spl4_5)),
% 0.23/0.52    inference(forward_demodulation,[],[f151,f30])).
% 0.23/0.52  fof(f151,plain,(
% 0.23/0.52    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k1_xboole_0),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_4 | ~spl4_5)),
% 0.23/0.52    inference(forward_demodulation,[],[f150,f29])).
% 0.23/0.52  fof(f150,plain,(
% 0.23/0.52    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,sK1)),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_4 | ~spl4_5)),
% 0.23/0.52    inference(forward_demodulation,[],[f149,f104])).
% 0.23/0.52  fof(f104,plain,(
% 0.23/0.52    sK1 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_4),
% 0.23/0.52    inference(avatar_component_clause,[],[f102])).
% 0.23/0.52  fof(f149,plain,(
% 0.23/0.52    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,sK3))) | (spl4_1 | ~spl4_5)),
% 0.23/0.52    inference(forward_demodulation,[],[f148,f109])).
% 0.23/0.52  fof(f109,plain,(
% 0.23/0.52    sK3 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl4_5),
% 0.23/0.52    inference(avatar_component_clause,[],[f107])).
% 0.23/0.53  fof(f148,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3))))) | spl4_1),
% 0.23/0.53    inference(forward_demodulation,[],[f130,f54])).
% 0.23/0.53  fof(f54,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k5_enumset1(X0,X0,X0,X0,X0,X0,X1) = k5_enumset1(X1,X1,X1,X1,X1,X1,X0)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f33,f48,f48])).
% 0.23/0.53  fof(f48,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f36,f47])).
% 0.23/0.53  fof(f47,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_enumset1(X0,X0,X0,X0,X0,X1,X2)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f39,f46])).
% 0.23/0.53  fof(f46,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k5_enumset1(X0,X0,X0,X0,X1,X2,X3)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f41,f45])).
% 0.23/0.53  fof(f45,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k5_enumset1(X0,X0,X0,X1,X2,X3,X4)) )),
% 0.23/0.53    inference(definition_unfolding,[],[f43,f44])).
% 0.23/0.53  fof(f44,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f14])).
% 0.23/0.53  fof(f14,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 0.23/0.53  fof(f43,plain,(
% 0.23/0.53    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f13])).
% 0.23/0.53  fof(f13,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 0.23/0.53  fof(f41,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f12])).
% 0.23/0.53  fof(f12,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 0.23/0.53  fof(f39,plain,(
% 0.23/0.53    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f11])).
% 0.23/0.53  fof(f11,axiom,(
% 0.23/0.53    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 0.23/0.53  fof(f36,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f10])).
% 0.23/0.53  fof(f10,axiom,(
% 0.23/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.23/0.53  fof(f33,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f9])).
% 0.23/0.53  fof(f9,axiom,(
% 0.23/0.53    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.23/0.53  fof(f130,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k2_zfmisc_1(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)))),k5_xboole_0(sK3,k5_xboole_0(sK2,k3_tarski(k5_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK2))))) | spl4_1),
% 0.23/0.53    inference(superposition,[],[f60,f122])).
% 0.23/0.53  fof(f122,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))))) )),
% 0.23/0.53    inference(forward_demodulation,[],[f121,f40])).
% 0.23/0.53  fof(f121,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)))) = k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(X2,k5_xboole_0(X3,k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))))) )),
% 0.23/0.53    inference(forward_demodulation,[],[f56,f40])).
% 0.23/0.53  fof(f56,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))),k5_xboole_0(k5_xboole_0(X2,X3),k3_tarski(k5_enumset1(X2,X2,X2,X2,X2,X2,X3)))) = k5_xboole_0(k5_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3)),k3_tarski(k5_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))))) )),
% 0.23/0.53    inference(definition_unfolding,[],[f42,f50,f50,f50])).
% 0.23/0.53  fof(f50,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)))) )),
% 0.23/0.53    inference(definition_unfolding,[],[f37,f49])).
% 0.23/0.53  fof(f49,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1))) )),
% 0.23/0.53    inference(definition_unfolding,[],[f35,f48])).
% 0.23/0.53  fof(f35,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f15])).
% 0.23/0.53  fof(f15,axiom,(
% 0.23/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.23/0.53  fof(f37,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f8])).
% 0.23/0.53  fof(f8,axiom,(
% 0.23/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.23/0.53  fof(f42,plain,(
% 0.23/0.53    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))) )),
% 0.23/0.53    inference(cnf_transformation,[],[f16])).
% 0.23/0.53  fof(f16,axiom,(
% 0.23/0.53    ! [X0,X1,X2,X3] : k2_zfmisc_1(k3_xboole_0(X0,X1),k3_xboole_0(X2,X3)) = k3_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X3))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).
% 0.23/0.53  fof(f60,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k5_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)))) | spl4_1),
% 0.23/0.53    inference(avatar_component_clause,[],[f58])).
% 0.23/0.53  fof(f112,plain,(
% 0.23/0.53    spl4_4 | ~spl4_3),
% 0.23/0.53    inference(avatar_split_clause,[],[f100,f68,f102])).
% 0.23/0.53  fof(f68,plain,(
% 0.23/0.53    spl4_3 <=> r1_tarski(sK0,sK1)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.23/0.53  fof(f100,plain,(
% 0.23/0.53    sK1 = k3_tarski(k5_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK1)) | ~spl4_3),
% 0.23/0.53    inference(resolution,[],[f55,f70])).
% 0.23/0.53  fof(f70,plain,(
% 0.23/0.53    r1_tarski(sK0,sK1) | ~spl4_3),
% 0.23/0.53    inference(avatar_component_clause,[],[f68])).
% 0.23/0.53  fof(f55,plain,(
% 0.23/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_tarski(k5_enumset1(X0,X0,X0,X0,X0,X0,X1)) = X1) )),
% 0.23/0.53    inference(definition_unfolding,[],[f38,f49])).
% 0.23/0.53  fof(f38,plain,(
% 0.23/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 0.23/0.53    inference(cnf_transformation,[],[f23])).
% 0.23/0.53  fof(f23,plain,(
% 0.23/0.53    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 0.23/0.53    inference(ennf_transformation,[],[f4])).
% 0.23/0.53  fof(f4,axiom,(
% 0.23/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 0.23/0.53  fof(f111,plain,(
% 0.23/0.53    spl4_5 | ~spl4_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f99,f63,f107])).
% 0.23/0.53  fof(f63,plain,(
% 0.23/0.53    spl4_2 <=> r1_tarski(sK2,sK3)),
% 0.23/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.23/0.53  fof(f99,plain,(
% 0.23/0.53    sK3 = k3_tarski(k5_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK3)) | ~spl4_2),
% 0.23/0.53    inference(resolution,[],[f55,f65])).
% 0.23/0.53  fof(f65,plain,(
% 0.23/0.53    r1_tarski(sK2,sK3) | ~spl4_2),
% 0.23/0.53    inference(avatar_component_clause,[],[f63])).
% 0.23/0.53  fof(f71,plain,(
% 0.23/0.53    spl4_3),
% 0.23/0.53    inference(avatar_split_clause,[],[f26,f68])).
% 0.23/0.53  fof(f26,plain,(
% 0.23/0.53    r1_tarski(sK0,sK1)),
% 0.23/0.53    inference(cnf_transformation,[],[f25])).
% 0.23/0.53  fof(f25,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1)),
% 0.23/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f22,f24])).
% 0.23/0.53  fof(f24,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1)) => (k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)) & r1_tarski(sK2,sK3) & r1_tarski(sK0,sK1))),
% 0.23/0.53    introduced(choice_axiom,[])).
% 0.23/0.53  fof(f22,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & r1_tarski(X2,X3) & r1_tarski(X0,X1))),
% 0.23/0.53    inference(flattening,[],[f21])).
% 0.23/0.53  fof(f21,plain,(
% 0.23/0.53    ? [X0,X1,X2,X3] : (k2_zfmisc_1(X0,X2) != k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)) & (r1_tarski(X2,X3) & r1_tarski(X0,X1)))),
% 0.23/0.53    inference(ennf_transformation,[],[f18])).
% 0.23/0.53  fof(f18,negated_conjecture,(
% 0.23/0.53    ~! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.23/0.53    inference(negated_conjecture,[],[f17])).
% 0.23/0.53  fof(f17,conjecture,(
% 0.23/0.53    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => k2_zfmisc_1(X0,X2) = k3_xboole_0(k2_zfmisc_1(X0,X3),k2_zfmisc_1(X1,X2)))),
% 0.23/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).
% 0.23/0.53  fof(f66,plain,(
% 0.23/0.53    spl4_2),
% 0.23/0.53    inference(avatar_split_clause,[],[f27,f63])).
% 0.23/0.53  fof(f27,plain,(
% 0.23/0.53    r1_tarski(sK2,sK3)),
% 0.23/0.53    inference(cnf_transformation,[],[f25])).
% 0.23/0.53  fof(f61,plain,(
% 0.23/0.53    ~spl4_1),
% 0.23/0.53    inference(avatar_split_clause,[],[f51,f58])).
% 0.23/0.53  fof(f51,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k5_xboole_0(k5_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2)),k3_tarski(k5_enumset1(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))))),
% 0.23/0.53    inference(definition_unfolding,[],[f28,f50])).
% 0.23/0.53  fof(f28,plain,(
% 0.23/0.53    k2_zfmisc_1(sK0,sK2) != k3_xboole_0(k2_zfmisc_1(sK0,sK3),k2_zfmisc_1(sK1,sK2))),
% 0.23/0.53    inference(cnf_transformation,[],[f25])).
% 0.23/0.53  % SZS output end Proof for theBenchmark
% 0.23/0.53  % (28147)------------------------------
% 0.23/0.53  % (28147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.53  % (28147)Termination reason: Refutation
% 0.23/0.53  
% 0.23/0.53  % (28147)Memory used [KB]: 6268
% 0.23/0.53  % (28147)Time elapsed: 0.082 s
% 0.23/0.53  % (28147)------------------------------
% 0.23/0.53  % (28147)------------------------------
% 0.23/0.53  % (28158)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.23/0.53  % (28139)Success in time 0.164 s
%------------------------------------------------------------------------------
