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
% DateTime   : Thu Dec  3 12:42:27 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 255 expanded)
%              Number of leaves         :   12 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :   63 ( 274 expanded)
%              Number of equality atoms :   54 ( 264 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f50,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f49])).

fof(f49,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f48])).

fof(f48,plain,
    ( $false
    | spl3_1 ),
    inference(trivial_inequality_removal,[],[f47])).

fof(f47,plain,
    ( k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | spl3_1 ),
    inference(forward_demodulation,[],[f46,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5))) ),
    inference(definition_unfolding,[],[f24,f31])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f25,f29,f30])).

fof(f30,plain,(
    ! [X0] : k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f16,f28])).

fof(f28,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f18,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f19,f26])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f22,f23])).

fof(f23,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f19,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f18,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f29,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f17,f28])).

fof(f17,plain,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f46,plain,
    ( k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),sK2)
    | spl3_1 ),
    inference(superposition,[],[f44,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k4_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) ),
    inference(definition_unfolding,[],[f20,f29,f29])).

fof(f20,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f44,plain,
    ( k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl3_1
  <=> k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f45,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f38,f42])).

fof(f38,plain,(
    k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(trivial_inequality_removal,[],[f37])).

fof(f37,plain,
    ( k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1))
    | k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(forward_demodulation,[],[f36,f32])).

fof(f36,plain,
    ( k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))
    | k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(backward_demodulation,[],[f33,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k3_tarski(k4_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) ),
    inference(definition_unfolding,[],[f21,f29,f29])).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f33,plain,
    ( k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) != k3_tarski(k4_enumset1(k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))))
    | k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2))) ),
    inference(definition_unfolding,[],[f15,f28,f29,f30,f30,f28,f29,f30,f30])).

fof(f15,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
    | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) )
   => ( k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1)))
      | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
        & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.45  % (11870)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (11864)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (11865)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.51  % (11874)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.52  % (11866)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.52  % (11871)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.52  % (11875)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (11867)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.52  % (11875)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f45,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl3_1),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    $false | spl3_1),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) | spl3_1),
% 0.21/0.52    inference(forward_demodulation,[],[f46,f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k3_tarski(k4_enumset1(k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X0,X0,X1,X2,X3,X4),k4_enumset1(X5,X5,X5,X5,X5,X5)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f24,f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k4_enumset1(k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X0,X1,X2,X3,X4,X5),k4_enumset1(X6,X6,X6,X6,X6,X6)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f25,f29,f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X0] : (k1_tarski(X0) = k4_enumset1(X0,X0,X0,X0,X0,X0)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f16,f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_tarski(X0,X1) = k4_enumset1(X0,X0,X0,X0,X0,X1)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f18,f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k4_enumset1(X0,X0,X0,X0,X1,X2)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f19,f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k4_enumset1(X0,X0,X0,X1,X2,X3)) )),
% 0.21/0.52    inference(definition_unfolding,[],[f22,f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f17,f28])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k3_tarski(k2_tarski(X0,X1)) = k2_xboole_0(X0,X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_enumset1)).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k2_zfmisc_1(k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1))),sK2) | spl3_1),
% 0.21/0.52    inference(superposition,[],[f44,f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1)),X2) = k3_tarski(k4_enumset1(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f20,f29,f29])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)) & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2))) | spl3_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f42])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    spl3_1 <=> k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) = k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ~spl3_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f38,f42])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) | k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.21/0.52    inference(forward_demodulation,[],[f36,f32])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) != k2_zfmisc_1(sK2,k3_tarski(k4_enumset1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))) | k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.21/0.52    inference(backward_demodulation,[],[f33,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k3_tarski(k4_enumset1(X0,X0,X0,X0,X0,X1))) = k3_tarski(k4_enumset1(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1)))) )),
% 0.21/0.52    inference(definition_unfolding,[],[f21,f29,f29])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1)) != k3_tarski(k4_enumset1(k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0)),k2_zfmisc_1(sK2,k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1)))) | k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK1),sK2) != k3_tarski(k4_enumset1(k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK0,sK0,sK0,sK0,sK0,sK0),sK2),k2_zfmisc_1(k4_enumset1(sK1,sK1,sK1,sK1,sK1,sK1),sK2)))),
% 0.21/0.52    inference(definition_unfolding,[],[f15,f28,f29,f30,f30,f28,f29,f30,f30])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2))),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f13])).
% 0.21/0.52  fof(f13,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2))) => (k2_zfmisc_1(sK2,k2_tarski(sK0,sK1)) != k2_xboole_0(k2_zfmisc_1(sK2,k1_tarski(sK0)),k2_zfmisc_1(sK2,k1_tarski(sK1))) | k2_zfmisc_1(k2_tarski(sK0,sK1),sK2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(sK0),sK2),k2_zfmisc_1(k1_tarski(sK1),sK2)))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f12,plain,(
% 0.21/0.52    ? [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) != k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) | k2_zfmisc_1(k2_tarski(X0,X1),X2) != k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1,X2] : (k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1))) & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_zfmisc_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (11875)------------------------------
% 0.21/0.52  % (11875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11875)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (11875)Memory used [KB]: 10618
% 0.21/0.52  % (11875)Time elapsed: 0.089 s
% 0.21/0.52  % (11875)------------------------------
% 0.21/0.52  % (11875)------------------------------
% 0.21/0.52  % (11856)Success in time 0.167 s
%------------------------------------------------------------------------------
