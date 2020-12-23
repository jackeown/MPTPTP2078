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
% DateTime   : Thu Dec  3 12:50:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   55 (  69 expanded)
%              Number of leaves         :   16 (  26 expanded)
%              Depth                    :   10
%              Number of atoms          :   96 ( 119 expanded)
%              Number of equality atoms :   39 (  47 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f99,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f57,f66,f98])).

fof(f98,plain,
    ( spl1_1
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(avatar_contradiction_clause,[],[f94])).

fof(f94,plain,
    ( $false
    | spl1_1
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f35,f85])).

fof(f85,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_6 ),
    inference(forward_demodulation,[],[f84,f64])).

fof(f64,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl1_6
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f84,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f75,f69])).

fof(f69,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)) ),
    inference(superposition,[],[f30,f22])).

fof(f22,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f30,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f27,f29])).

fof(f29,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1)) ),
    inference(definition_unfolding,[],[f25,f26])).

fof(f26,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f27,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f75,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)))
    | ~ spl1_3
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f72,f45])).

fof(f45,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl1_3
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f72,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_setfam_1(k1_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X0)))
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f56,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0))) ) ),
    inference(definition_unfolding,[],[f28,f29])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

fof(f56,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f35,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f66,plain,
    ( spl1_6
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f60,f54,f62])).

fof(f60,plain,
    ( k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_5 ),
    inference(resolution,[],[f24,f56])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

fof(f57,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f52,f38,f54])).

fof(f38,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f52,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(unit_resulting_resolution,[],[f40,f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f40,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f46,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f21,f43])).

fof(f21,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f41,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f36,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f18,f33])).

fof(f18,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).

fof(f16,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 19:23:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (10647)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.43  % (10647)Refutation found. Thanks to Tanya!
% 0.21/0.43  % SZS status Theorem for theBenchmark
% 0.21/0.43  % SZS output start Proof for theBenchmark
% 0.21/0.43  fof(f99,plain,(
% 0.21/0.43    $false),
% 0.21/0.43    inference(avatar_sat_refutation,[],[f36,f41,f46,f57,f66,f98])).
% 0.21/0.43  fof(f98,plain,(
% 0.21/0.43    spl1_1 | ~spl1_3 | ~spl1_5 | ~spl1_6),
% 0.21/0.43    inference(avatar_contradiction_clause,[],[f94])).
% 0.21/0.43  fof(f94,plain,(
% 0.21/0.43    $false | (spl1_1 | ~spl1_3 | ~spl1_5 | ~spl1_6)),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f35,f85])).
% 0.21/0.43  fof(f85,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl1_3 | ~spl1_5 | ~spl1_6)),
% 0.21/0.43    inference(forward_demodulation,[],[f84,f64])).
% 0.21/0.43  fof(f64,plain,(
% 0.21/0.43    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_6),
% 0.21/0.43    inference(avatar_component_clause,[],[f62])).
% 0.21/0.43  fof(f62,plain,(
% 0.21/0.43    spl1_6 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.43  fof(f84,plain,(
% 0.21/0.43    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_xboole_0)) ) | (~spl1_3 | ~spl1_5)),
% 0.21/0.43    inference(forward_demodulation,[],[f75,f69])).
% 0.21/0.43  fof(f69,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0))) )),
% 0.21/0.43    inference(superposition,[],[f30,f22])).
% 0.21/0.43  fof(f22,plain,(
% 0.21/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f3])).
% 0.21/0.43  fof(f3,axiom,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.43  fof(f30,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f27,f29])).
% 0.21/0.43  fof(f29,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k1_enumset1(X0,X0,X1))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f25,f26])).
% 0.21/0.43  fof(f26,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f4])).
% 0.21/0.43  fof(f4,axiom,(
% 0.21/0.43    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).
% 0.21/0.43  fof(f25,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.21/0.43    inference(cnf_transformation,[],[f5])).
% 0.21/0.43  fof(f5,axiom,(
% 0.21/0.43    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.21/0.43  fof(f27,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f2])).
% 0.21/0.43  fof(f2,axiom,(
% 0.21/0.43    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.43  fof(f75,plain,(
% 0.21/0.43    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_setfam_1(k1_enumset1(k1_xboole_0,k1_xboole_0,X0)))) ) | (~spl1_3 | ~spl1_5)),
% 0.21/0.43    inference(forward_demodulation,[],[f72,f45])).
% 0.21/0.43  fof(f45,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.43    inference(avatar_component_clause,[],[f43])).
% 0.21/0.43  fof(f43,plain,(
% 0.21/0.43    spl1_3 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.43  fof(f72,plain,(
% 0.21/0.43    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k10_relat_1(k1_xboole_0,k1_setfam_1(k1_enumset1(k2_relat_1(k1_xboole_0),k2_relat_1(k1_xboole_0),X0)))) ) | ~spl1_5),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f56,f31])).
% 0.21/0.43  fof(f31,plain,(
% 0.21/0.43    ( ! [X0,X1] : (~v1_relat_1(X1) | k10_relat_1(X1,X0) = k10_relat_1(X1,k1_setfam_1(k1_enumset1(k2_relat_1(X1),k2_relat_1(X1),X0)))) )),
% 0.21/0.43    inference(definition_unfolding,[],[f28,f29])).
% 0.21/0.43  fof(f28,plain,(
% 0.21/0.43    ( ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f15])).
% 0.21/0.43  fof(f15,plain,(
% 0.21/0.43    ! [X0,X1] : (k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.43    inference(ennf_transformation,[],[f7])).
% 0.21/0.43  fof(f7,axiom,(
% 0.21/0.43    ! [X0,X1] : (v1_relat_1(X1) => k10_relat_1(X1,X0) = k10_relat_1(X1,k3_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).
% 0.21/0.43  fof(f56,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.21/0.43    inference(avatar_component_clause,[],[f54])).
% 0.21/0.43  fof(f54,plain,(
% 0.21/0.43    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.43  fof(f35,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.43    inference(avatar_component_clause,[],[f33])).
% 0.21/0.43  fof(f33,plain,(
% 0.21/0.43    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.43  fof(f66,plain,(
% 0.21/0.43    spl1_6 | ~spl1_5),
% 0.21/0.43    inference(avatar_split_clause,[],[f60,f54,f62])).
% 0.21/0.43  fof(f60,plain,(
% 0.21/0.43    k1_xboole_0 = k10_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_5),
% 0.21/0.43    inference(resolution,[],[f24,f56])).
% 0.21/0.43  fof(f24,plain,(
% 0.21/0.43    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f14])).
% 0.21/0.43  fof(f14,plain,(
% 0.21/0.43    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f8])).
% 0.21/0.43  fof(f8,axiom,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).
% 0.21/0.43  fof(f57,plain,(
% 0.21/0.43    spl1_5 | ~spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f52,f38,f54])).
% 0.21/0.43  fof(f38,plain,(
% 0.21/0.43    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.43  fof(f52,plain,(
% 0.21/0.43    v1_relat_1(k1_xboole_0) | ~spl1_2),
% 0.21/0.43    inference(unit_resulting_resolution,[],[f40,f23])).
% 0.21/0.43  fof(f23,plain,(
% 0.21/0.43    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.43    inference(cnf_transformation,[],[f13])).
% 0.21/0.43  fof(f13,plain,(
% 0.21/0.43    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.43    inference(ennf_transformation,[],[f6])).
% 0.21/0.43  fof(f6,axiom,(
% 0.21/0.43    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.43  fof(f40,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.21/0.43    inference(avatar_component_clause,[],[f38])).
% 0.21/0.43  fof(f46,plain,(
% 0.21/0.43    spl1_3),
% 0.21/0.43    inference(avatar_split_clause,[],[f21,f43])).
% 0.21/0.43  fof(f21,plain,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f9])).
% 0.21/0.43  fof(f9,axiom,(
% 0.21/0.43    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.43  fof(f41,plain,(
% 0.21/0.43    spl1_2),
% 0.21/0.43    inference(avatar_split_clause,[],[f19,f38])).
% 0.21/0.43  fof(f19,plain,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    inference(cnf_transformation,[],[f1])).
% 0.21/0.43  fof(f1,axiom,(
% 0.21/0.43    v1_xboole_0(k1_xboole_0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.43  fof(f36,plain,(
% 0.21/0.43    ~spl1_1),
% 0.21/0.43    inference(avatar_split_clause,[],[f18,f33])).
% 0.21/0.43  fof(f18,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    inference(cnf_transformation,[],[f17])).
% 0.21/0.43  fof(f17,plain,(
% 0.21/0.43    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f12,f16])).
% 0.21/0.43  fof(f16,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.43    introduced(choice_axiom,[])).
% 0.21/0.43  fof(f12,plain,(
% 0.21/0.43    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(ennf_transformation,[],[f11])).
% 0.21/0.43  fof(f11,negated_conjecture,(
% 0.21/0.43    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    inference(negated_conjecture,[],[f10])).
% 0.21/0.43  fof(f10,conjecture,(
% 0.21/0.43    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.43    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.43  % SZS output end Proof for theBenchmark
% 0.21/0.43  % (10647)------------------------------
% 0.21/0.43  % (10647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.43  % (10647)Termination reason: Refutation
% 0.21/0.43  
% 0.21/0.43  % (10647)Memory used [KB]: 6140
% 0.21/0.43  % (10647)Time elapsed: 0.047 s
% 0.21/0.44  % (10647)------------------------------
% 0.21/0.44  % (10647)------------------------------
% 0.21/0.44  % (10640)Success in time 0.08 s
%------------------------------------------------------------------------------
