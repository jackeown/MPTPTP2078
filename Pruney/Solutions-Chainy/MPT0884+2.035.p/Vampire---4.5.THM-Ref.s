%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:59:00 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   57 ( 235 expanded)
%              Number of leaves         :   18 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :   76 ( 260 expanded)
%              Number of equality atoms :   52 ( 230 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f91,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f46,f50,f58,f72,f90])).

fof(f90,plain,
    ( ~ spl5_2
    | ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f38,f75])).

fof(f75,plain,
    ( ! [X12,X10,X8,X11,X9] : k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X10),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9)),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12)) = k6_enumset1(k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X10,X9),X11),k4_tarski(k4_tarski(X8,X9),X12),k4_tarski(k4_tarski(X10,X9),X12))
    | ~ spl5_2
    | ~ spl5_5 ),
    inference(superposition,[],[f71,f49])).

fof(f49,plain,
    ( ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl5_2
  <=> ! [X1,X0,X2] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f71,plain,
    ( ! [X10,X8,X11,X9] : k6_enumset1(k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X11,X9),k4_tarski(X8,X10),k4_tarski(X11,X10)) = k2_zfmisc_1(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X11),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_5
  <=> ! [X9,X11,X8,X10] : k6_enumset1(k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X11,X9),k4_tarski(X8,X10),k4_tarski(X11,X10)) = k2_zfmisc_1(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X11),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f38,plain,(
    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4)) ),
    inference(definition_unfolding,[],[f18,f21,f36,f37,f36,f34,f22,f22,f22,f22])).

fof(f22,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

fof(f34,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f27,f33])).

fof(f33,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f29,f32])).

fof(f32,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f30,f31])).

fof(f31,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

fof(f30,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

fof(f29,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

fof(f27,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

fof(f37,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f19,f36])).

fof(f19,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f36,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f20,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f23,f34])).

fof(f23,plain,(
    ! [X2,X0,X1] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

fof(f20,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

fof(f18,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))
   => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).

fof(f72,plain,
    ( spl5_5
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f65,f56,f44,f70])).

fof(f44,plain,
    ( spl5_1
  <=> ! [X1,X3,X0,X2] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f56,plain,
    ( spl5_4
  <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f65,plain,
    ( ! [X10,X8,X11,X9] : k6_enumset1(k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X11,X9),k4_tarski(X8,X10),k4_tarski(X11,X10)) = k2_zfmisc_1(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X11),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10))
    | ~ spl5_1
    | ~ spl5_4 ),
    inference(superposition,[],[f57,f45])).

fof(f45,plain,
    ( ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f57,plain,
    ( ! [X2,X0,X3,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f58,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f42,f56])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(definition_unfolding,[],[f28,f36,f36,f34])).

fof(f28,plain,(
    ! [X2,X0,X3,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).

fof(f50,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f39,f48])).

fof(f39,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(definition_unfolding,[],[f25,f36,f37,f36])).

fof(f25,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))
      & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

% (7819)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
fof(f46,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f41,f44])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3) ),
    inference(definition_unfolding,[],[f26,f34,f34])).

fof(f26,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f1])).

% (7814)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:22:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (7810)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (7809)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (7811)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (7806)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (7813)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (7807)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (7813)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (7820)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (7818)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (7822)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (7817)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (7817)Refutation not found, incomplete strategy% (7817)------------------------------
% 0.20/0.48  % (7817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7817)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (7817)Memory used [KB]: 10618
% 0.20/0.48  % (7817)Time elapsed: 0.074 s
% 0.20/0.48  % (7817)------------------------------
% 0.20/0.48  % (7817)------------------------------
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(avatar_sat_refutation,[],[f46,f50,f58,f72,f90])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~spl5_2 | ~spl5_5),
% 0.20/0.48    inference(avatar_contradiction_clause,[],[f89])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    $false | (~spl5_2 | ~spl5_5)),
% 0.20/0.48    inference(subsumption_resolution,[],[f38,f75])).
% 0.20/0.48  fof(f75,plain,(
% 0.20/0.48    ( ! [X12,X10,X8,X11,X9] : (k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X10),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X9)),k6_enumset1(X11,X11,X11,X11,X11,X11,X11,X12)) = k6_enumset1(k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X8,X9),X11),k4_tarski(k4_tarski(X10,X9),X11),k4_tarski(k4_tarski(X8,X9),X12),k4_tarski(k4_tarski(X10,X9),X12))) ) | (~spl5_2 | ~spl5_5)),
% 0.20/0.48    inference(superposition,[],[f71,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) ) | ~spl5_2),
% 0.20/0.48    inference(avatar_component_clause,[],[f48])).
% 0.20/0.48  fof(f48,plain,(
% 0.20/0.48    spl5_2 <=> ! [X1,X0,X2] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.20/0.48  fof(f71,plain,(
% 0.20/0.48    ( ! [X10,X8,X11,X9] : (k6_enumset1(k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X11,X9),k4_tarski(X8,X10),k4_tarski(X11,X10)) = k2_zfmisc_1(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X11),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10))) ) | ~spl5_5),
% 0.20/0.48    inference(avatar_component_clause,[],[f70])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl5_5 <=> ! [X9,X11,X8,X10] : k6_enumset1(k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X11,X9),k4_tarski(X8,X10),k4_tarski(X11,X10)) = k2_zfmisc_1(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X11),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    k2_zfmisc_1(k2_zfmisc_1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,sK2)),k6_enumset1(sK3,sK3,sK3,sK3,sK3,sK3,sK3,sK4)) != k6_enumset1(k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK3),k4_tarski(k4_tarski(sK1,sK2),sK3),k4_tarski(k4_tarski(sK0,sK2),sK4),k4_tarski(k4_tarski(sK1,sK2),sK4))),
% 0.20/0.48    inference(definition_unfolding,[],[f18,f21,f36,f37,f36,f34,f22,f22,f22,f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f27,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f29,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f30,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5,X6] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k5_enumset1(X0,X1,X2,X3,X4,X5,X6)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f7])).
% 0.20/0.48  fof(f7,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4,X5] : k5_enumset1(X0,X0,X1,X2,X3,X4,X5) = k4_enumset1(X0,X1,X2,X3,X4,X5)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k3_enumset1(X0,X0,X1,X2,X3)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f19,f36])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f20,f35])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f23,f34])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k2_enumset1(X0,X0,X1,X2) = k1_enumset1(X0,X1,X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.20/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f15,f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4)) => k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3),k3_mcart_1(sK0,sK2,sK4),k3_mcart_1(sK1,sK2,sK4))),
% 0.20/0.48    introduced(choice_axiom,[])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 0.20/0.48    inference(ennf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,negated_conjecture,(
% 0.20/0.48    ~! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 0.20/0.48    inference(negated_conjecture,[],[f13])).
% 0.20/0.48  fof(f13,conjecture,(
% 0.20/0.48    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3),k3_mcart_1(X0,X2,X4),k3_mcart_1(X1,X2,X4))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_mcart_1)).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    spl5_5 | ~spl5_1 | ~spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f65,f56,f44,f70])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    spl5_1 <=> ! [X1,X3,X0,X2] : k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3)),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.20/0.48  fof(f56,plain,(
% 0.20/0.48    spl5_4 <=> ! [X1,X3,X0,X2] : k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.20/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.20/0.48  fof(f65,plain,(
% 0.20/0.48    ( ! [X10,X8,X11,X9] : (k6_enumset1(k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X8,X9),k4_tarski(X11,X9),k4_tarski(X8,X10),k4_tarski(X11,X10)) = k2_zfmisc_1(k6_enumset1(X8,X8,X8,X8,X8,X8,X8,X11),k6_enumset1(X9,X9,X9,X9,X9,X9,X9,X10))) ) | (~spl5_1 | ~spl5_4)),
% 0.20/0.48    inference(superposition,[],[f57,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3)) ) | ~spl5_1),
% 0.20/0.48    inference(avatar_component_clause,[],[f44])).
% 0.20/0.48  fof(f57,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) ) | ~spl5_4),
% 0.20/0.48    inference(avatar_component_clause,[],[f56])).
% 0.20/0.48  fof(f58,plain,(
% 0.20/0.48    spl5_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f56])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X3)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f28,f36,f36,f34])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f9])).
% 0.20/0.48  fof(f9,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_zfmisc_1)).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    spl5_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f48])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),k6_enumset1(X2,X2,X2,X2,X2,X2,X2,X2)) = k6_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.48    inference(definition_unfolding,[],[f25,f36,f37,f36])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : (k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) = k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) & k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) = k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).
% 0.20/0.48  % (7819)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    spl5_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f44])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X2,X1,X3)) )),
% 0.20/0.48    inference(definition_unfolding,[],[f26,f34,f34])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  % (7814)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_enumset1)).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (7813)------------------------------
% 0.20/0.48  % (7813)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (7813)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (7813)Memory used [KB]: 6268
% 0.20/0.48  % (7813)Time elapsed: 0.069 s
% 0.20/0.48  % (7813)------------------------------
% 0.20/0.48  % (7813)------------------------------
% 0.20/0.49  % (7805)Success in time 0.13 s
%------------------------------------------------------------------------------
