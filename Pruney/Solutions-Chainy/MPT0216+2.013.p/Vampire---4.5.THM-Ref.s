%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:35:15 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 125 expanded)
%              Number of leaves         :   14 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   92 ( 196 expanded)
%              Number of equality atoms :   58 ( 145 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f96,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f38,f57,f62,f88,f93])).

fof(f93,plain,
    ( spl3_4
    | ~ spl3_6 ),
    inference(avatar_contradiction_clause,[],[f89])).

fof(f89,plain,
    ( $false
    | spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f56,f86,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( k2_tarski(X0,X0) != k2_tarski(X1,X2)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f22,f16])).

fof(f16,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] :
      ( X0 = X1
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( X0 = X1
      | k1_tarski(X0) != k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

fof(f86,plain,
    ( k2_tarski(sK0,sK0) = k2_tarski(sK2,sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl3_6
  <=> k2_tarski(sK0,sK0) = k2_tarski(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f56,plain,
    ( sK0 != sK2
    | spl3_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl3_4
  <=> sK0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f88,plain,
    ( spl3_6
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f80,f59,f84])).

fof(f59,plain,
    ( spl3_5
  <=> k2_tarski(sK0,sK0) = k2_tarski(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f80,plain,
    ( k2_tarski(sK0,sK0) = k2_tarski(sK2,sK0)
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f74,f61])).

fof(f61,plain,
    ( k2_tarski(sK0,sK0) = k2_tarski(sK0,sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f74,plain,
    ( k2_tarski(sK0,sK2) = k2_tarski(sK2,sK0)
    | ~ spl3_5 ),
    inference(superposition,[],[f25,f66])).

fof(f66,plain,
    ( ! [X1] : k2_tarski(sK0,X1) = k5_xboole_0(k2_tarski(X1,sK2),k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(X1,sK2))))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f64,f25])).

fof(f64,plain,
    ( ! [X1] : k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(sK0,sK0)))) = k5_xboole_0(k2_tarski(X1,sK2),k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(X1,sK2))))
    | ~ spl3_5 ),
    inference(superposition,[],[f27,f61])).

fof(f27,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) = k5_xboole_0(k2_tarski(X2,X1),k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X2,X1)))) ),
    inference(definition_unfolding,[],[f20,f24,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) ),
    inference(definition_unfolding,[],[f21,f23,f16])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f19,f18])).

fof(f18,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f20,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0)))) ),
    inference(definition_unfolding,[],[f17,f24])).

fof(f17,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f62,plain,
    ( spl3_5
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f46,f35,f59])).

fof(f35,plain,
    ( spl3_2
  <=> k2_tarski(sK1,sK2) = k2_tarski(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f46,plain,
    ( k2_tarski(sK0,sK0) = k2_tarski(sK0,sK2)
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f37,f44])).

fof(f44,plain,
    ( sK0 = sK1
    | ~ spl3_2 ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,
    ( ! [X0] :
        ( k2_tarski(X0,X0) != k2_tarski(sK0,sK0)
        | sK1 = X0 )
    | ~ spl3_2 ),
    inference(superposition,[],[f28,f37])).

fof(f37,plain,
    ( k2_tarski(sK1,sK2) = k2_tarski(sK0,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f57,plain,
    ( ~ spl3_4
    | spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f47,f35,f30,f54])).

fof(f30,plain,
    ( spl3_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f47,plain,
    ( sK0 != sK2
    | spl3_1
    | ~ spl3_2 ),
    inference(backward_demodulation,[],[f32,f44])).

fof(f32,plain,
    ( sK1 != sK2
    | spl3_1 ),
    inference(avatar_component_clause,[],[f30])).

fof(f38,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f26,f35])).

fof(f26,plain,(
    k2_tarski(sK1,sK2) = k2_tarski(sK0,sK0) ),
    inference(definition_unfolding,[],[f14,f16])).

fof(f14,plain,(
    k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,
    ( sK1 != sK2
    & k1_tarski(sK0) = k2_tarski(sK1,sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).

fof(f12,plain,
    ( ? [X0,X1,X2] :
        ( X1 != X2
        & k1_tarski(X0) = k2_tarski(X1,X2) )
   => ( sK1 != sK2
      & k1_tarski(sK0) = k2_tarski(sK1,sK2) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( X1 != X2
      & k1_tarski(X0) = k2_tarski(X1,X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k1_tarski(X0) = k2_tarski(X1,X2)
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2] :
      ( k1_tarski(X0) = k2_tarski(X1,X2)
     => X1 = X2 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

fof(f33,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f15,f30])).

% (17258)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f15,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f13])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n020.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:40:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (17250)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (17243)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (17251)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.51  % (17251)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f33,f38,f57,f62,f88,f93])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl3_4 | ~spl3_6),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f89])).
% 0.21/0.51  fof(f89,plain,(
% 0.21/0.51    $false | (spl3_4 | ~spl3_6)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f56,f86,f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k2_tarski(X0,X0) != k2_tarski(X1,X2) | X0 = X1) )),
% 0.21/0.51    inference(definition_unfolding,[],[f22,f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (X0 = X1 | k1_tarski(X0) != k2_tarski(X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (X0 = X1 | k1_tarski(X0) != k2_tarski(X1,X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X0 = X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    k2_tarski(sK0,sK0) = k2_tarski(sK2,sK0) | ~spl3_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f84])).
% 0.21/0.51  fof(f84,plain,(
% 0.21/0.51    spl3_6 <=> k2_tarski(sK0,sK0) = k2_tarski(sK2,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f56,plain,(
% 0.21/0.51    sK0 != sK2 | spl3_4),
% 0.21/0.51    inference(avatar_component_clause,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    spl3_4 <=> sK0 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl3_6 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f80,f59,f84])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    spl3_5 <=> k2_tarski(sK0,sK0) = k2_tarski(sK0,sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    k2_tarski(sK0,sK0) = k2_tarski(sK2,sK0) | ~spl3_5),
% 0.21/0.51    inference(forward_demodulation,[],[f74,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    k2_tarski(sK0,sK0) = k2_tarski(sK0,sK2) | ~spl3_5),
% 0.21/0.51    inference(avatar_component_clause,[],[f59])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    k2_tarski(sK0,sK2) = k2_tarski(sK2,sK0) | ~spl3_5),
% 0.21/0.51    inference(superposition,[],[f25,f66])).
% 0.21/0.51  fof(f66,plain,(
% 0.21/0.51    ( ! [X1] : (k2_tarski(sK0,X1) = k5_xboole_0(k2_tarski(X1,sK2),k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(X1,sK2))))) ) | ~spl3_5),
% 0.21/0.51    inference(forward_demodulation,[],[f64,f25])).
% 0.21/0.51  fof(f64,plain,(
% 0.21/0.51    ( ! [X1] : (k5_xboole_0(k2_tarski(sK0,sK0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(sK0,sK0)))) = k5_xboole_0(k2_tarski(X1,sK2),k5_xboole_0(k2_tarski(sK0,sK0),k3_xboole_0(k2_tarski(sK0,sK0),k2_tarski(X1,sK2))))) ) | ~spl3_5),
% 0.21/0.51    inference(superposition,[],[f27,f61])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1)))) = k5_xboole_0(k2_tarski(X2,X1),k5_xboole_0(k2_tarski(X0,X0),k3_xboole_0(k2_tarski(X0,X0),k2_tarski(X2,X1))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f20,f24,f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k5_xboole_0(k2_tarski(X0,X1),k5_xboole_0(k2_tarski(X2,X2),k3_xboole_0(k2_tarski(X2,X2),k2_tarski(X0,X1))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f21,f23,f16])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f19,f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f3])).
% 0.21/0.51  fof(f3,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k5_xboole_0(k2_tarski(X0,X0),k5_xboole_0(k2_tarski(X1,X1),k3_xboole_0(k2_tarski(X1,X1),k2_tarski(X0,X0))))) )),
% 0.21/0.51    inference(definition_unfolding,[],[f17,f24])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.51  fof(f62,plain,(
% 0.21/0.51    spl3_5 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f35,f59])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    spl3_2 <=> k2_tarski(sK1,sK2) = k2_tarski(sK0,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    k2_tarski(sK0,sK0) = k2_tarski(sK0,sK2) | ~spl3_2),
% 0.21/0.51    inference(backward_demodulation,[],[f37,f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    sK0 = sK1 | ~spl3_2),
% 0.21/0.51    inference(equality_resolution,[],[f39])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ( ! [X0] : (k2_tarski(X0,X0) != k2_tarski(sK0,sK0) | sK1 = X0) ) | ~spl3_2),
% 0.21/0.51    inference(superposition,[],[f28,f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    k2_tarski(sK1,sK2) = k2_tarski(sK0,sK0) | ~spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f35])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ~spl3_4 | spl3_1 | ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f35,f30,f54])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    spl3_1 <=> sK1 = sK2),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    sK0 != sK2 | (spl3_1 | ~spl3_2)),
% 0.21/0.51    inference(backward_demodulation,[],[f32,f44])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    sK1 != sK2 | spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f30])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f26,f35])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    k2_tarski(sK1,sK2) = k2_tarski(sK0,sK0)),
% 0.21/0.51    inference(definition_unfolding,[],[f14,f16])).
% 0.21/0.51  fof(f14,plain,(
% 0.21/0.51    k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,plain,(
% 0.21/0.51    sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f10,f12])).
% 0.21/0.51  fof(f12,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2)) => (sK1 != sK2 & k1_tarski(sK0) = k2_tarski(sK1,sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f10,plain,(
% 0.21/0.51    ? [X0,X1,X2] : (X1 != X2 & k1_tarski(X0) = k2_tarski(X1,X2))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,negated_conjecture,(
% 0.21/0.51    ~! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.51    inference(negated_conjecture,[],[f8])).
% 0.21/0.51  fof(f8,conjecture,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_tarski(X0) = k2_tarski(X1,X2) => X1 = X2)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f15,f30])).
% 0.21/0.51  % (17258)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.51  fof(f15,plain,(
% 0.21/0.51    sK1 != sK2),
% 0.21/0.51    inference(cnf_transformation,[],[f13])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (17251)------------------------------
% 0.21/0.51  % (17251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (17251)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (17251)Memory used [KB]: 10746
% 0.21/0.51  % (17251)Time elapsed: 0.095 s
% 0.21/0.51  % (17251)------------------------------
% 0.21/0.51  % (17251)------------------------------
% 0.21/0.51  % (17240)Success in time 0.151 s
%------------------------------------------------------------------------------
