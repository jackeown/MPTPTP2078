%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   58 (  73 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :  123 ( 155 expanded)
%              Number of equality atoms :   57 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f54,f58,f72,f82,f104,f119])).

fof(f119,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(avatar_contradiction_clause,[],[f118])).

fof(f118,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(subsumption_resolution,[],[f37,f117])).

fof(f117,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_9
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f116,f74])).

fof(f74,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f73,f57])).

fof(f57,plain,
    ( ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f73,plain,
    ( ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))
    | ~ spl2_3
    | ~ spl2_9 ),
    inference(superposition,[],[f71,f45])).

fof(f45,plain,
    ( ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f44,plain,
    ( spl2_3
  <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f71,plain,
    ( ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f116,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f115,f41])).

fof(f41,plain,
    ( ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f40,plain,
    ( spl2_2
  <=> ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f115,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k3_xboole_0(k1_setfam_1(k1_tarski(X0)),X1)
    | ~ spl2_2
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f111,f41])).

fof(f111,plain,
    ( ! [X0,X1] : k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k3_xboole_0(k1_setfam_1(k1_tarski(X0)),k1_setfam_1(k1_tarski(X1)))
    | ~ spl2_11
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f81,f81,f103])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl2_15
  <=> ! [X1,X0] :
        ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f81,plain,
    ( ! [X0] : k1_tarski(X0) != k1_xboole_0
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl2_11
  <=> ! [X0] : k1_tarski(X0) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f37,plain,
    ( k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_1
  <=> k3_xboole_0(sK0,sK1) = k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f104,plain,(
    spl2_15 ),
    inference(avatar_split_clause,[],[f27,f102])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ~ ( k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1))
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).

fof(f82,plain,
    ( spl2_11
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f63,f52,f48,f80])).

fof(f48,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f52,plain,
    ( spl2_5
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f63,plain,
    ( ! [X0] : k1_tarski(X0) != k1_xboole_0
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f49,f53])).

fof(f53,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f49,plain,
    ( ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f72,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).

fof(f58,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f25,f56])).

fof(f25,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f54,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f52])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f50,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f23,f48])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

fof(f46,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f22,f44])).

fof(f22,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f42,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f21,f40])).

fof(f21,plain,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

fof(f38,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f20,f35])).

fof(f20,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).

fof(f18,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))
   => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:25:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (32019)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.45  % (32019)Refutation found. Thanks to Tanya!
% 0.21/0.45  % SZS status Theorem for theBenchmark
% 0.21/0.45  % SZS output start Proof for theBenchmark
% 0.21/0.45  fof(f122,plain,(
% 0.21/0.45    $false),
% 0.21/0.45    inference(avatar_sat_refutation,[],[f38,f42,f46,f50,f54,f58,f72,f82,f104,f119])).
% 0.21/0.45  fof(f119,plain,(
% 0.21/0.45    spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_9 | ~spl2_11 | ~spl2_15),
% 0.21/0.45    inference(avatar_contradiction_clause,[],[f118])).
% 0.21/0.45  fof(f118,plain,(
% 0.21/0.45    $false | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_9 | ~spl2_11 | ~spl2_15)),
% 0.21/0.45    inference(subsumption_resolution,[],[f37,f117])).
% 0.21/0.45  fof(f117,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) ) | (~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_9 | ~spl2_11 | ~spl2_15)),
% 0.21/0.45    inference(forward_demodulation,[],[f116,f74])).
% 0.21/0.45  fof(f74,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | (~spl2_3 | ~spl2_6 | ~spl2_9)),
% 0.21/0.45    inference(forward_demodulation,[],[f73,f57])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) ) | ~spl2_6),
% 0.21/0.45    inference(avatar_component_clause,[],[f56])).
% 0.21/0.45  fof(f56,plain,(
% 0.21/0.45    spl2_6 <=> ! [X1,X0] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.45  fof(f73,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) ) | (~spl2_3 | ~spl2_9)),
% 0.21/0.45    inference(superposition,[],[f71,f45])).
% 0.21/0.45  fof(f45,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) ) | ~spl2_3),
% 0.21/0.45    inference(avatar_component_clause,[],[f44])).
% 0.21/0.45  fof(f44,plain,(
% 0.21/0.45    spl2_3 <=> ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.45  fof(f71,plain,(
% 0.21/0.45    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) ) | ~spl2_9),
% 0.21/0.45    inference(avatar_component_clause,[],[f70])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    spl2_9 <=> ! [X1,X0,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.45  fof(f116,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1)))) ) | (~spl2_2 | ~spl2_11 | ~spl2_15)),
% 0.21/0.45    inference(forward_demodulation,[],[f115,f41])).
% 0.21/0.45  fof(f41,plain,(
% 0.21/0.45    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) ) | ~spl2_2),
% 0.21/0.45    inference(avatar_component_clause,[],[f40])).
% 0.21/0.45  fof(f40,plain,(
% 0.21/0.45    spl2_2 <=> ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.45  fof(f115,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k3_xboole_0(k1_setfam_1(k1_tarski(X0)),X1)) ) | (~spl2_2 | ~spl2_11 | ~spl2_15)),
% 0.21/0.45    inference(forward_demodulation,[],[f111,f41])).
% 0.21/0.45  fof(f111,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(k1_tarski(X0),k1_tarski(X1))) = k3_xboole_0(k1_setfam_1(k1_tarski(X0)),k1_setfam_1(k1_tarski(X1)))) ) | (~spl2_11 | ~spl2_15)),
% 0.21/0.45    inference(unit_resulting_resolution,[],[f81,f81,f103])).
% 0.21/0.45  fof(f103,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) ) | ~spl2_15),
% 0.21/0.45    inference(avatar_component_clause,[],[f102])).
% 0.21/0.45  fof(f102,plain,(
% 0.21/0.45    spl2_15 <=> ! [X1,X0] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.45  fof(f81,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) != k1_xboole_0) ) | ~spl2_11),
% 0.21/0.45    inference(avatar_component_clause,[],[f80])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl2_11 <=> ! [X0] : k1_tarski(X0) != k1_xboole_0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1)) | spl2_1),
% 0.21/0.45    inference(avatar_component_clause,[],[f35])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    spl2_1 <=> k3_xboole_0(sK0,sK1) = k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.45  fof(f104,plain,(
% 0.21/0.45    spl2_15),
% 0.21/0.45    inference(avatar_split_clause,[],[f27,f102])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ( ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 0.21/0.45    inference(cnf_transformation,[],[f17])).
% 0.21/0.45  fof(f17,plain,(
% 0.21/0.45    ! [X0,X1] : (k1_setfam_1(k2_xboole_0(X0,X1)) = k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 0.21/0.45    inference(ennf_transformation,[],[f12])).
% 0.21/0.45  fof(f12,axiom,(
% 0.21/0.45    ! [X0,X1] : ~(k1_setfam_1(k2_xboole_0(X0,X1)) != k3_xboole_0(k1_setfam_1(X0),k1_setfam_1(X1)) & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 0.21/0.45    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_setfam_1)).
% 0.21/0.45  fof(f82,plain,(
% 0.21/0.45    spl2_11 | ~spl2_4 | ~spl2_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f63,f52,f48,f80])).
% 0.21/0.45  fof(f48,plain,(
% 0.21/0.45    spl2_4 <=> ! [X1,X0] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.45  fof(f52,plain,(
% 0.21/0.45    spl2_5 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.45  fof(f63,plain,(
% 0.21/0.45    ( ! [X0] : (k1_tarski(X0) != k1_xboole_0) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.45    inference(superposition,[],[f49,f53])).
% 0.21/0.46  fof(f53,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl2_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f52])).
% 0.21/0.46  fof(f49,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) ) | ~spl2_4),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f72,plain,(
% 0.21/0.46    spl2_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f29,f70])).
% 0.21/0.46  fof(f29,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_xboole_0(k2_tarski(X0,X1),k1_tarski(X2))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_enumset1)).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl2_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f25,f56])).
% 0.21/0.46  fof(f25,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f7])).
% 0.21/0.46  fof(f7,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_tarski(X0,X1) = k1_enumset1(X0,X0,X1)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl2_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f52])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    spl2_4),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f48])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0,X1] : k2_xboole_0(k1_tarski(X0),X1) != k1_xboole_0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl2_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f44])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f6])).
% 0.21/0.46  fof(f6,axiom,(
% 0.21/0.46    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.46  fof(f42,plain,(
% 0.21/0.46    spl2_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f21,f40])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    ( ! [X0] : (k1_setfam_1(k1_tarski(X0)) = X0) )),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    ! [X0] : k1_setfam_1(k1_tarski(X0)) = X0),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    ~spl2_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f20,f35])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1)) => k3_xboole_0(sK0,sK1) != k1_setfam_1(k2_tarski(sK0,sK1))),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0,X1] : k3_xboole_0(X0,X1) != k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,negated_conjecture,(
% 0.21/0.46    ~! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    inference(negated_conjecture,[],[f14])).
% 0.21/0.46  fof(f14,conjecture,(
% 0.21/0.46    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (32019)------------------------------
% 0.21/0.46  % (32019)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (32019)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (32019)Memory used [KB]: 6140
% 0.21/0.46  % (32019)Time elapsed: 0.010 s
% 0.21/0.46  % (32019)------------------------------
% 0.21/0.46  % (32019)------------------------------
% 0.21/0.46  % (32013)Success in time 0.101 s
%------------------------------------------------------------------------------
