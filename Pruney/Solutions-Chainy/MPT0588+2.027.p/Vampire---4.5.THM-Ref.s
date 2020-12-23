%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:59 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   51 (  90 expanded)
%              Number of leaves         :   12 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   99 ( 155 expanded)
%              Number of equality atoms :   38 (  72 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f32,f37,f46,f71,f103])).

fof(f103,plain,
    ( ~ spl2_2
    | ~ spl2_3
    | spl2_6 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_3
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f70,f90])).

fof(f90,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k1_relat_1(sK1))))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f85,f75])).

fof(f75,plain,
    ( ! [X1] : k7_relat_1(sK1,X1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k7_relat_1(sK1,X1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f55,f25])).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f19,f20,f20])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f55,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k4_xboole_0(k7_relat_1(sK1,X0),k4_xboole_0(k7_relat_1(sK1,X0),sK1))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f38,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ) ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f38,plain,
    ( ! [X0] : r1_tarski(k7_relat_1(sK1,X0),sK1)
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f36,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( r1_tarski(k7_relat_1(X1,X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k7_relat_1(X1,X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

fof(f36,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_2
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f85,plain,
    ( ! [X0] : k4_xboole_0(sK1,k4_xboole_0(sK1,k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k1_relat_1(sK1))))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f80,f25])).

fof(f80,plain,
    ( ! [X0] : k4_xboole_0(k7_relat_1(sK1,X0),k4_xboole_0(k7_relat_1(sK1,X0),sK1)) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k1_relat_1(sK1))))
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(superposition,[],[f72,f44])).

fof(f44,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl2_3
  <=> sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f72,plain,
    ( ! [X0,X1] : k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(sK1,X0),k4_xboole_0(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)))
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f36,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(X2,X0),k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))) ) ),
    inference(definition_unfolding,[],[f23,f20,f20])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

fof(f70,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_6
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f71,plain,
    ( ~ spl2_6
    | spl2_1 ),
    inference(avatar_split_clause,[],[f66,f29,f68])).

fof(f29,plain,
    ( spl2_1
  <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f66,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))
    | spl2_1 ),
    inference(backward_demodulation,[],[f31,f25])).

fof(f31,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f29])).

fof(f46,plain,
    ( spl2_3
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f40,f34,f42])).

fof(f40,plain,
    ( sK1 = k7_relat_1(sK1,k1_relat_1(sK1))
    | ~ spl2_2 ),
    inference(resolution,[],[f18,f36])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f34])).

fof(f16,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,
    ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).

fof(f14,plain,
    ( ? [X0,X1] :
        ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
        & v1_relat_1(X1) )
   => ( k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0,X1] :
      ( k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

fof(f32,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f24,f29])).

fof(f24,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) ),
    inference(definition_unfolding,[],[f17,f20])).

fof(f17,plain,(
    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:41:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.47  % (12654)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.47  % (12656)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (12656)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f106,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f32,f37,f46,f71,f103])).
% 0.22/0.48  fof(f103,plain,(
% 0.22/0.48    ~spl2_2 | ~spl2_3 | spl2_6),
% 0.22/0.48    inference(avatar_contradiction_clause,[],[f91])).
% 0.22/0.48  fof(f91,plain,(
% 0.22/0.48    $false | (~spl2_2 | ~spl2_3 | spl2_6)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f70,f90])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relat_1(sK1,X0) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k1_relat_1(sK1))))) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.48    inference(forward_demodulation,[],[f85,f75])).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    ( ! [X1] : (k7_relat_1(sK1,X1) = k4_xboole_0(sK1,k4_xboole_0(sK1,k7_relat_1(sK1,X1)))) ) | ~spl2_2),
% 0.22/0.48    inference(superposition,[],[f55,f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f19,f20,f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.22/0.48  fof(f55,plain,(
% 0.22/0.48    ( ! [X0] : (k7_relat_1(sK1,X0) = k4_xboole_0(k7_relat_1(sK1,X0),k4_xboole_0(k7_relat_1(sK1,X0),sK1))) ) | ~spl2_2),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f38,f26])).
% 0.22/0.48  fof(f26,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0) )),
% 0.22/0.48    inference(definition_unfolding,[],[f22,f20])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0] : (r1_tarski(k7_relat_1(sK1,X0),sK1)) ) | ~spl2_2),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f36,f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,plain,(
% 0.22/0.48    ! [X0,X1] : (r1_tarski(k7_relat_1(X1,X0),X1) | ~v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k7_relat_1(X1,X0),X1))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    v1_relat_1(sK1) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f34])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    spl2_2 <=> v1_relat_1(sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f85,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(sK1,k4_xboole_0(sK1,k7_relat_1(sK1,X0))) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k1_relat_1(sK1))))) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.48    inference(forward_demodulation,[],[f80,f25])).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    ( ! [X0] : (k4_xboole_0(k7_relat_1(sK1,X0),k4_xboole_0(k7_relat_1(sK1,X0),sK1)) = k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,k1_relat_1(sK1))))) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.48    inference(superposition,[],[f72,f44])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) | ~spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f42])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    spl2_3 <=> sK1 = k7_relat_1(sK1,k1_relat_1(sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f72,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k7_relat_1(sK1,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(sK1,X0),k4_xboole_0(k7_relat_1(sK1,X0),k7_relat_1(sK1,X1)))) ) | ~spl2_2),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f36,f27])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k7_relat_1(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(k7_relat_1(X2,X0),k4_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f23,f20,f20])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f13])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)) | ~v1_relat_1(X2))),
% 0.22/0.48    inference(ennf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) => k7_relat_1(X2,k3_xboole_0(X0,X1)) = k3_xboole_0(k7_relat_1(X2,X0),k7_relat_1(X2,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).
% 0.22/0.48  fof(f70,plain,(
% 0.22/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) | spl2_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f68])).
% 0.22/0.48  fof(f68,plain,(
% 0.22/0.48    spl2_6 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1))))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    ~spl2_6 | spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f66,f29,f68])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    spl2_1 <=> k7_relat_1(sK1,sK0) = k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f66,plain,(
% 0.22/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(sK0,k4_xboole_0(sK0,k1_relat_1(sK1)))) | spl2_1),
% 0.22/0.48    inference(backward_demodulation,[],[f31,f25])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0))) | spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f29])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    spl2_3 | ~spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f40,f34,f42])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    sK1 = k7_relat_1(sK1,k1_relat_1(sK1)) | ~spl2_2),
% 0.22/0.48    inference(resolution,[],[f18,f36])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 0.22/0.48    inference(cnf_transformation,[],[f10])).
% 0.22/0.48  fof(f10,plain,(
% 0.22/0.48    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f16,f34])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    v1_relat_1(sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f9,f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1)) => (k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0)) & v1_relat_1(sK1))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f9,plain,(
% 0.22/0.48    ? [X0,X1] : (k7_relat_1(X1,X0) != k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,negated_conjecture,(
% 0.22/0.48    ~! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.48    inference(negated_conjecture,[],[f7])).
% 0.22/0.48  fof(f7,conjecture,(
% 0.22/0.48    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k7_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.22/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ~spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f24,f29])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k4_xboole_0(k1_relat_1(sK1),k4_xboole_0(k1_relat_1(sK1),sK0)))),
% 0.22/0.48    inference(definition_unfolding,[],[f17,f20])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    k7_relat_1(sK1,sK0) != k7_relat_1(sK1,k3_xboole_0(k1_relat_1(sK1),sK0))),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (12656)------------------------------
% 0.22/0.48  % (12656)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (12656)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (12656)Memory used [KB]: 6140
% 0.22/0.48  % (12656)Time elapsed: 0.054 s
% 0.22/0.48  % (12656)------------------------------
% 0.22/0.48  % (12656)------------------------------
% 0.22/0.48  % (12662)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.48  % (12649)Success in time 0.113 s
%------------------------------------------------------------------------------
