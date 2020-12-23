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
% DateTime   : Thu Dec  3 12:48:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 104 expanded)
%              Number of leaves         :   15 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :  118 ( 179 expanded)
%              Number of equality atoms :   43 (  81 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f73,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f58,f66,f72])).

fof(f72,plain,
    ( spl0_2
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(avatar_contradiction_clause,[],[f71])).

fof(f71,plain,
    ( $false
    | spl0_2
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(subsumption_resolution,[],[f70,f40])).

fof(f40,plain,
    ( k1_xboole_0 != k3_relat_1(k1_xboole_0)
    | spl0_2 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl0_2
  <=> k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).

fof(f70,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f69,f31])).

fof(f31,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(forward_demodulation,[],[f29,f30])).

fof(f30,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f27,f21])).

fof(f21,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f27,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f20,f26])).

fof(f26,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f29,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f24,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f69,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f68,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl0_4 ),
    inference(avatar_component_clause,[],[f48])).

fof(f48,plain,
    ( spl0_4
  <=> k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).

fof(f68,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl0_3
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f67,f21])).

fof(f67,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl0_3
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f60,f45])).

fof(f45,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl0_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl0_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).

fof(f60,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
    | ~ spl0_5 ),
    inference(resolution,[],[f28,f57])).

fof(f57,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl0_5 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl0_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0))) ) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

fof(f66,plain,
    ( spl0_2
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(avatar_contradiction_clause,[],[f65])).

fof(f65,plain,
    ( $false
    | spl0_2
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(subsumption_resolution,[],[f64,f40])).

fof(f64,plain,
    ( k1_xboole_0 = k3_relat_1(k1_xboole_0)
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f63,f31])).

fof(f63,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl0_3
    | ~ spl0_4
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f62,f50])).

fof(f62,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0))
    | ~ spl0_3
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f61,f21])).

fof(f61,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0))
    | ~ spl0_3
    | ~ spl0_5 ),
    inference(forward_demodulation,[],[f59,f45])).

fof(f59,plain,
    ( k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0)))
    | ~ spl0_5 ),
    inference(unit_resulting_resolution,[],[f57,f28])).

fof(f58,plain,
    ( spl0_5
    | ~ spl0_1 ),
    inference(avatar_split_clause,[],[f52,f33,f55])).

fof(f33,plain,
    ( spl0_1
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).

fof(f52,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl0_1 ),
    inference(unit_resulting_resolution,[],[f35,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f35,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl0_1 ),
    inference(avatar_component_clause,[],[f33])).

fof(f51,plain,(
    spl0_4 ),
    inference(avatar_split_clause,[],[f19,f48])).

fof(f19,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f46,plain,(
    spl0_3 ),
    inference(avatar_split_clause,[],[f18,f43])).

fof(f18,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,(
    ~ spl0_2 ),
    inference(avatar_split_clause,[],[f16,f38])).

fof(f16,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(flattening,[],[f11])).

fof(f11,negated_conjecture,(
    k1_xboole_0 != k3_relat_1(k1_xboole_0) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    k1_xboole_0 = k3_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).

fof(f36,plain,(
    spl0_1 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:43:38 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.41  % (5719)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.48  % (5719)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f36,f41,f46,f51,f58,f66,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl0_2 | ~spl0_3 | ~spl0_4 | ~spl0_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    $false | (spl0_2 | ~spl0_3 | ~spl0_4 | ~spl0_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f70,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    k1_xboole_0 != k3_relat_1(k1_xboole_0) | spl0_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    spl0_2 <=> k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl0_2])])).
% 0.21/0.48  fof(f70,plain,(
% 0.21/0.48    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl0_3 | ~spl0_4 | ~spl0_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f69,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(forward_demodulation,[],[f29,f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.48    inference(backward_demodulation,[],[f27,f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f20,f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.48    inference(definition_unfolding,[],[f24,f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    inference(rectify,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl0_3 | ~spl0_4 | ~spl0_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f68,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) | ~spl0_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    spl0_4 <=> k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl0_4])])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl0_3 | ~spl0_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f67,f21])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl0_3 | ~spl0_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f60,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl0_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f43])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    spl0_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl0_3])])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) | ~spl0_5),
% 0.21/0.48    inference(resolution,[],[f28,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    v1_relat_1(k1_xboole_0) | ~spl0_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl0_5 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl0_5])])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k3_relat_1(X0) = k5_xboole_0(k1_relat_1(X0),k4_xboole_0(k2_relat_1(X0),k1_relat_1(X0)))) )),
% 0.21/0.48    inference(definition_unfolding,[],[f23,f25])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ( ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k3_relat_1(X0) = k2_xboole_0(k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl0_2 | ~spl0_3 | ~spl0_4 | ~spl0_5),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f65])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    $false | (spl0_2 | ~spl0_3 | ~spl0_4 | ~spl0_5)),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f40])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    k1_xboole_0 = k3_relat_1(k1_xboole_0) | (~spl0_3 | ~spl0_4 | ~spl0_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f63,f31])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl0_3 | ~spl0_4 | ~spl0_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f62,f50])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k2_relat_1(k1_xboole_0)) | (~spl0_3 | ~spl0_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f61,f21])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k2_relat_1(k1_xboole_0),k1_xboole_0)) | (~spl0_3 | ~spl0_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f59,f45])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    k3_relat_1(k1_xboole_0) = k5_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k2_relat_1(k1_xboole_0),k1_relat_1(k1_xboole_0))) | ~spl0_5),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f57,f28])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl0_5 | ~spl0_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f52,f33,f55])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    spl0_1 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl0_1])])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    v1_relat_1(k1_xboole_0) | ~spl0_1),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f35,f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl0_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f33])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl0_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f19,f48])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    spl0_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f18,f43])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f9])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ~spl0_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f16,f38])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    k1_xboole_0 != k3_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,negated_conjecture,(
% 0.21/0.48    ~k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.48    inference(negated_conjecture,[],[f10])).
% 0.21/0.48  fof(f10,conjecture,(
% 0.21/0.48    k1_xboole_0 = k3_relat_1(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_relat_1)).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    spl0_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f17,f33])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (5719)------------------------------
% 0.21/0.48  % (5719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (5719)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (5719)Memory used [KB]: 6140
% 0.21/0.48  % (5719)Time elapsed: 0.054 s
% 0.21/0.48  % (5719)------------------------------
% 0.21/0.48  % (5719)------------------------------
% 0.21/0.48  % (5704)Success in time 0.122 s
%------------------------------------------------------------------------------
