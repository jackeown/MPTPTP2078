%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0886+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:48:49 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   39 (  81 expanded)
%              Number of leaves         :   11 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  98 expanded)
%              Number of equality atoms :   36 (  78 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f70,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f30,f65,f69])).

fof(f69,plain,(
    spl6_2 ),
    inference(avatar_contradiction_clause,[],[f68])).

fof(f68,plain,
    ( $false
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f67])).

fof(f67,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5))
    | spl6_2 ),
    inference(forward_demodulation,[],[f66,f25])).

fof(f25,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(k4_tarski(X0,X2),k4_tarski(X0,X3)),k2_tarski(k4_tarski(X1,X2),k4_tarski(X1,X3))) ),
    inference(definition_unfolding,[],[f20,f19])).

% (30740)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
fof(f19,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_mcart_1)).

fof(f66,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_zfmisc_1(k2_xboole_0(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))),k2_tarski(sK4,sK5))
    | spl6_2 ),
    inference(superposition,[],[f64,f16])).

fof(f16,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_xboole_0(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,X0),k2_zfmisc_1(X2,X1))
      & k2_zfmisc_1(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(X0,X2),k2_zfmisc_1(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

fof(f64,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(sK4,sK5)),k2_zfmisc_1(k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k2_tarski(sK4,sK5)))
    | spl6_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl6_2
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) = k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(sK4,sK5)),k2_zfmisc_1(k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k2_tarski(sK4,sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f65,plain,
    ( ~ spl6_2
    | spl6_1 ),
    inference(avatar_split_clause,[],[f60,f27,f62])).

fof(f27,plain,
    ( spl6_1
  <=> k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) = k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK5),k4_tarski(k4_tarski(sK1,sK3),sK5)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f60,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3)),k2_tarski(sK4,sK5)),k2_zfmisc_1(k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k2_tarski(sK4,sK5)))
    | spl6_1 ),
    inference(forward_demodulation,[],[f59,f25])).

fof(f59,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK2),sK5)),k2_tarski(k4_tarski(k4_tarski(sK0,sK3),sK4),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_zfmisc_1(k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k2_tarski(sK4,sK5)))
    | spl6_1 ),
    inference(forward_demodulation,[],[f58,f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_xboole_0(k2_tarski(X0,X2),k2_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f18,f19,f19])).

fof(f18,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).

fof(f58,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_zfmisc_1(k2_tarski(k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)),k2_tarski(sK4,sK5)))
    | spl6_1 ),
    inference(forward_demodulation,[],[f57,f25])).

fof(f57,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK5)),k2_tarski(k4_tarski(k4_tarski(sK1,sK3),sK4),k4_tarski(k4_tarski(sK1,sK3),sK5))))
    | spl6_1 ),
    inference(forward_demodulation,[],[f29,f24])).

fof(f29,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK5),k4_tarski(k4_tarski(sK1,sK3),sK5))))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f27])).

fof(f30,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f23,f27])).

fof(f23,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)),k2_tarski(sK4,sK5)) != k2_xboole_0(k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK0,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK0,sK2),sK5),k4_tarski(k4_tarski(sK0,sK3),sK5))),k2_xboole_0(k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK4),k4_tarski(k4_tarski(sK1,sK3),sK4)),k2_tarski(k4_tarski(k4_tarski(sK1,sK2),sK5),k4_tarski(k4_tarski(sK1,sK3),sK5)))) ),
    inference(definition_unfolding,[],[f13,f14,f22,f15,f15,f15,f15,f15,f15,f15,f15])).

fof(f15,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f22,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)),k2_xboole_0(k2_tarski(X4,X5),k2_tarski(X6,X7))) ),
    inference(definition_unfolding,[],[f21,f19,f19])).

fof(f21,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k2_enumset1(X4,X5,X6,X7)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_enumset1)).

fof(f14,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f13,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK0,sK2,sK5),k3_mcart_1(sK0,sK3,sK5),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK3,sK4),k3_mcart_1(sK1,sK2,sK5),k3_mcart_1(sK1,sK3,sK5)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK0,sK2,sK5),k3_mcart_1(sK0,sK3,sK5),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK3,sK4),k3_mcart_1(sK1,sK2,sK5),k3_mcart_1(sK1,sK3,sK5)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f10,f11])).

fof(f11,plain,
    ( ? [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) != k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3),k2_tarski(sK4,sK5)) != k6_enumset1(k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK0,sK3,sK4),k3_mcart_1(sK0,sK2,sK5),k3_mcart_1(sK0,sK3,sK5),k3_mcart_1(sK1,sK2,sK4),k3_mcart_1(sK1,sK3,sK4),k3_mcart_1(sK1,sK2,sK5),k3_mcart_1(sK1,sK3,sK5)) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) != k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3,X4,X5] : k3_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3),k2_tarski(X4,X5)) = k6_enumset1(k3_mcart_1(X0,X2,X4),k3_mcart_1(X0,X3,X4),k3_mcart_1(X0,X2,X5),k3_mcart_1(X0,X3,X5),k3_mcart_1(X1,X2,X4),k3_mcart_1(X1,X3,X4),k3_mcart_1(X1,X2,X5),k3_mcart_1(X1,X3,X5)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_mcart_1)).

%------------------------------------------------------------------------------
