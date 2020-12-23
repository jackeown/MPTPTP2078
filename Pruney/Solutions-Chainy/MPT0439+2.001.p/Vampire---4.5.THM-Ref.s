%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:46:56 EST 2020

% Result     : Theorem 0.14s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   48 (  66 expanded)
%              Number of leaves         :   14 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :  106 ( 149 expanded)
%              Number of equality atoms :   28 (  42 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f23,f28,f32,f40,f44,f48,f66,f103,f116])).

fof(f116,plain,
    ( spl1_2
    | ~ spl1_8
    | ~ spl1_14 ),
    inference(avatar_contradiction_clause,[],[f115])).

fof(f115,plain,
    ( $false
    | spl1_2
    | ~ spl1_8
    | ~ spl1_14 ),
    inference(subsumption_resolution,[],[f27,f104])).

fof(f104,plain,
    ( sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_8
    | ~ spl1_14 ),
    inference(unit_resulting_resolution,[],[f65,f102])).

fof(f102,plain,
    ( ! [X2,X1] :
        ( k3_xboole_0(X1,X2) = X1
        | ~ r1_tarski(X1,X2) )
    | ~ spl1_14 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl1_14
  <=> ! [X1,X2] :
        ( k3_xboole_0(X1,X2) = X1
        | ~ r1_tarski(X1,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).

fof(f65,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl1_8
  <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f27,plain,
    ( sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | spl1_2 ),
    inference(avatar_component_clause,[],[f25])).

fof(f25,plain,
    ( spl1_2
  <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f103,plain,
    ( spl1_14
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f61,f46,f38,f30,f101])).

fof(f30,plain,
    ( spl1_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f38,plain,
    ( spl1_5
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f46,plain,
    ( spl1_7
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f61,plain,
    ( ! [X2,X1] :
        ( k3_xboole_0(X1,X2) = X1
        | ~ r1_tarski(X1,X2) )
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(forward_demodulation,[],[f56,f31])).

fof(f31,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f30])).

fof(f56,plain,
    ( ! [X2,X1] :
        ( k3_xboole_0(X1,X2) = k4_xboole_0(X1,k1_xboole_0)
        | ~ r1_tarski(X1,X2) )
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(superposition,[],[f47,f39])).

fof(f39,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f38])).

fof(f47,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f46])).

fof(f66,plain,
    ( spl1_8
    | ~ spl1_1
    | ~ spl1_6 ),
    inference(avatar_split_clause,[],[f54,f42,f20,f63])).

fof(f20,plain,
    ( spl1_1
  <=> v1_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f42,plain,
    ( spl1_6
  <=> ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f54,plain,
    ( r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    | ~ spl1_1
    | ~ spl1_6 ),
    inference(unit_resulting_resolution,[],[f22,f43])).

fof(f43,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
        | ~ v1_relat_1(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f42])).

fof(f22,plain,
    ( v1_relat_1(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f20])).

fof(f48,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f16,f46])).

fof(f16,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f44,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f15,f42])).

fof(f15,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

fof(f40,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f18,f38])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f32,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f14,f30])).

fof(f14,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f28,plain,(
    ~ spl1_2 ),
    inference(avatar_split_clause,[],[f13,f25])).

fof(f13,plain,(
    sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,
    ( sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
    & v1_relat_1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).

fof(f9,plain,
    ( ? [X0] :
        ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0
        & v1_relat_1(X0) )
   => ( sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))
      & v1_relat_1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0
      & v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( v1_relat_1(X0)
       => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

fof(f23,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f12,f20])).

fof(f12,plain,(
    v1_relat_1(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:11:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.41  % (19536)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.14/0.41  % (19536)Refutation found. Thanks to Tanya!
% 0.14/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.42  % (19539)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f117,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f23,f28,f32,f40,f44,f48,f66,f103,f116])).
% 0.21/0.42  fof(f116,plain,(
% 0.21/0.42    spl1_2 | ~spl1_8 | ~spl1_14),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f115])).
% 0.21/0.42  fof(f115,plain,(
% 0.21/0.42    $false | (spl1_2 | ~spl1_8 | ~spl1_14)),
% 0.21/0.42    inference(subsumption_resolution,[],[f27,f104])).
% 0.21/0.42  fof(f104,plain,(
% 0.21/0.42    sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | (~spl1_8 | ~spl1_14)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f65,f102])).
% 0.21/0.42  fof(f102,plain,(
% 0.21/0.42    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) ) | ~spl1_14),
% 0.21/0.42    inference(avatar_component_clause,[],[f101])).
% 0.21/0.42  fof(f101,plain,(
% 0.21/0.42    spl1_14 <=> ! [X1,X2] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_14])])).
% 0.21/0.42  fof(f65,plain,(
% 0.21/0.42    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | ~spl1_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f63])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl1_8 <=> r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | spl1_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f25])).
% 0.21/0.42  fof(f25,plain,(
% 0.21/0.42    spl1_2 <=> sK0 = k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.42  fof(f103,plain,(
% 0.21/0.42    spl1_14 | ~spl1_3 | ~spl1_5 | ~spl1_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f61,f46,f38,f30,f101])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl1_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl1_5 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl1_7 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = X1 | ~r1_tarski(X1,X2)) ) | (~spl1_3 | ~spl1_5 | ~spl1_7)),
% 0.21/0.42    inference(forward_demodulation,[],[f56,f31])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl1_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    ( ! [X2,X1] : (k3_xboole_0(X1,X2) = k4_xboole_0(X1,k1_xboole_0) | ~r1_tarski(X1,X2)) ) | (~spl1_5 | ~spl1_7)),
% 0.21/0.42    inference(superposition,[],[f47,f39])).
% 0.21/0.42  fof(f39,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) ) | ~spl1_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f38])).
% 0.21/0.42  fof(f47,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) ) | ~spl1_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl1_8 | ~spl1_1 | ~spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f54,f42,f20,f63])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    spl1_1 <=> v1_relat_1(sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.42  fof(f42,plain,(
% 0.21/0.42    spl1_6 <=> ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    r1_tarski(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) | (~spl1_1 | ~spl1_6)),
% 0.21/0.42    inference(unit_resulting_resolution,[],[f22,f43])).
% 0.21/0.42  fof(f43,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) ) | ~spl1_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f42])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    v1_relat_1(sK0) | ~spl1_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f20])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    spl1_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f46])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f42])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,plain,(
% 0.21/0.42    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).
% 0.21/0.42  fof(f40,plain,(
% 0.21/0.42    spl1_5),
% 0.21/0.42    inference(avatar_split_clause,[],[f18,f38])).
% 0.21/0.42  fof(f18,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 0.21/0.42    inference(nnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f14,f30])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    ~spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f13,f25])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0)))),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) & v1_relat_1(sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0 & v1_relat_1(X0)) => (sK0 != k3_xboole_0(sK0,k2_zfmisc_1(k1_relat_1(sK0),k2_relat_1(sK0))) & v1_relat_1(sK0))),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f7,plain,(
% 0.21/0.42    ? [X0] : (k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) != X0 & v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,negated_conjecture,(
% 0.21/0.42    ~! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f5])).
% 0.21/0.42  fof(f5,conjecture,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k3_xboole_0(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = X0)),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f12,f20])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    v1_relat_1(sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f10])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (19536)------------------------------
% 0.21/0.42  % (19536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (19536)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (19536)Memory used [KB]: 6140
% 0.21/0.42  % (19536)Time elapsed: 0.031 s
% 0.21/0.42  % (19536)------------------------------
% 0.21/0.42  % (19536)------------------------------
% 0.21/0.42  % (19530)Success in time 0.071 s
%------------------------------------------------------------------------------
