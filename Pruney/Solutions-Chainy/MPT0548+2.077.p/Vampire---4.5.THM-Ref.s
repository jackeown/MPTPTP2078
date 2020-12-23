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
% DateTime   : Thu Dec  3 12:49:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   59 (  74 expanded)
%              Number of leaves         :   18 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :  123 ( 156 expanded)
%              Number of equality atoms :   42 (  51 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f86,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f28,f33,f38,f49,f54,f58,f62,f69,f78,f85])).

fof(f85,plain,
    ( ~ spl1_3
    | ~ spl1_5
    | spl1_6
    | ~ spl1_7
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(avatar_contradiction_clause,[],[f84])).

fof(f84,plain,
    ( $false
    | ~ spl1_3
    | ~ spl1_5
    | spl1_6
    | ~ spl1_7
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f53,f83])).

fof(f83,plain,
    ( ! [X2] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f82,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl1_9
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f82,plain,
    ( ! [X2] : k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(k1_xboole_0,X2)
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_7
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f81,f57])).

fof(f57,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f56])).

fof(f56,plain,
    ( spl1_7
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f81,plain,
    ( ! [X2] : k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))
    | ~ spl1_3
    | ~ spl1_5
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f80,f37])).

fof(f37,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f80,plain,
    ( ! [X2] : k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k1_relat_1(k1_xboole_0),X2)))
    | ~ spl1_5
    | ~ spl1_11 ),
    inference(resolution,[],[f77,f48])).

fof(f48,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f46])).

fof(f46,plain,
    ( spl1_5
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ v1_relat_1(X1)
        | k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl1_11
  <=> ! [X1,X0] :
        ( k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f53,plain,
    ( k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)
    | spl1_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl1_6
  <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f78,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f24,f76])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))
      | ~ v1_relat_1(X1) ) ),
    inference(definition_unfolding,[],[f23,f22])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).

fof(f69,plain,
    ( spl1_9
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f64,f60,f46,f66])).

fof(f60,plain,
    ( spl1_8
  <=> ! [X0] :
        ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f64,plain,
    ( k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)
    | ~ spl1_5
    | ~ spl1_8 ),
    inference(resolution,[],[f61,f48])).

fof(f61,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f21,f60])).

fof(f21,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

fof(f58,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f20,f56])).

fof(f20,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f54,plain,(
    ~ spl1_6 ),
    inference(avatar_split_clause,[],[f15,f51])).

fof(f15,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).

fof(f13,plain,
    ( ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

fof(f49,plain,
    ( spl1_5
    | ~ spl1_1
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f44,f30,f26,f46])).

fof(f26,plain,
    ( spl1_1
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f30,plain,
    ( spl1_2
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f44,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_1
    | ~ spl1_2 ),
    inference(superposition,[],[f27,f32])).

fof(f32,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f30])).

fof(f27,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f38,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f33,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f16,f30])).

fof(f16,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f28,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f19,f26])).

fof(f19,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 09:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (16136)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.42  % (16136)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.42  % SZS output start Proof for theBenchmark
% 0.21/0.42  fof(f86,plain,(
% 0.21/0.42    $false),
% 0.21/0.42    inference(avatar_sat_refutation,[],[f28,f33,f38,f49,f54,f58,f62,f69,f78,f85])).
% 0.21/0.42  fof(f85,plain,(
% 0.21/0.42    ~spl1_3 | ~spl1_5 | spl1_6 | ~spl1_7 | ~spl1_9 | ~spl1_11),
% 0.21/0.42    inference(avatar_contradiction_clause,[],[f84])).
% 0.21/0.42  fof(f84,plain,(
% 0.21/0.42    $false | (~spl1_3 | ~spl1_5 | spl1_6 | ~spl1_7 | ~spl1_9 | ~spl1_11)),
% 0.21/0.42    inference(subsumption_resolution,[],[f53,f83])).
% 0.21/0.42  fof(f83,plain,(
% 0.21/0.42    ( ! [X2] : (k1_xboole_0 = k9_relat_1(k1_xboole_0,X2)) ) | (~spl1_3 | ~spl1_5 | ~spl1_7 | ~spl1_9 | ~spl1_11)),
% 0.21/0.42    inference(forward_demodulation,[],[f82,f68])).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | ~spl1_9),
% 0.21/0.42    inference(avatar_component_clause,[],[f66])).
% 0.21/0.42  fof(f66,plain,(
% 0.21/0.42    spl1_9 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.42  fof(f82,plain,(
% 0.21/0.42    ( ! [X2] : (k9_relat_1(k1_xboole_0,k1_xboole_0) = k9_relat_1(k1_xboole_0,X2)) ) | (~spl1_3 | ~spl1_5 | ~spl1_7 | ~spl1_11)),
% 0.21/0.42    inference(forward_demodulation,[],[f81,f57])).
% 0.21/0.42  fof(f57,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl1_7),
% 0.21/0.42    inference(avatar_component_clause,[],[f56])).
% 0.21/0.42  fof(f56,plain,(
% 0.21/0.42    spl1_7 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.42  fof(f81,plain,(
% 0.21/0.42    ( ! [X2] : (k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X2)))) ) | (~spl1_3 | ~spl1_5 | ~spl1_11)),
% 0.21/0.42    inference(forward_demodulation,[],[f80,f37])).
% 0.21/0.42  fof(f37,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.42    inference(avatar_component_clause,[],[f35])).
% 0.21/0.42  fof(f35,plain,(
% 0.21/0.42    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.42  fof(f80,plain,(
% 0.21/0.42    ( ! [X2] : (k9_relat_1(k1_xboole_0,X2) = k9_relat_1(k1_xboole_0,k4_xboole_0(k1_relat_1(k1_xboole_0),k4_xboole_0(k1_relat_1(k1_xboole_0),X2)))) ) | (~spl1_5 | ~spl1_11)),
% 0.21/0.42    inference(resolution,[],[f77,f48])).
% 0.21/0.42  fof(f48,plain,(
% 0.21/0.42    v1_relat_1(k1_xboole_0) | ~spl1_5),
% 0.21/0.42    inference(avatar_component_clause,[],[f46])).
% 0.21/0.42  fof(f46,plain,(
% 0.21/0.42    spl1_5 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.42  fof(f77,plain,(
% 0.21/0.42    ( ! [X0,X1] : (~v1_relat_1(X1) | k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0)))) ) | ~spl1_11),
% 0.21/0.42    inference(avatar_component_clause,[],[f76])).
% 0.21/0.42  fof(f76,plain,(
% 0.21/0.42    spl1_11 <=> ! [X1,X0] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) | ~v1_relat_1(X1))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0) | spl1_6),
% 0.21/0.42    inference(avatar_component_clause,[],[f51])).
% 0.21/0.42  fof(f51,plain,(
% 0.21/0.42    spl1_6 <=> k1_xboole_0 = k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.42  fof(f78,plain,(
% 0.21/0.42    spl1_11),
% 0.21/0.42    inference(avatar_split_clause,[],[f24,f76])).
% 0.21/0.42  fof(f24,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k4_xboole_0(k1_relat_1(X1),k4_xboole_0(k1_relat_1(X1),X0))) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(definition_unfolding,[],[f23,f22])).
% 0.21/0.42  fof(f22,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f1])).
% 0.21/0.42  fof(f1,axiom,(
% 0.21/0.42    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.42  fof(f23,plain,(
% 0.21/0.42    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f12])).
% 0.21/0.42  fof(f12,plain,(
% 0.21/0.42    ! [X0,X1] : (k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.42    inference(ennf_transformation,[],[f4])).
% 0.21/0.42  fof(f4,axiom,(
% 0.21/0.42    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k9_relat_1(X1,k3_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_relat_1)).
% 0.21/0.42  fof(f69,plain,(
% 0.21/0.42    spl1_9 | ~spl1_5 | ~spl1_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f64,f60,f46,f66])).
% 0.21/0.42  fof(f60,plain,(
% 0.21/0.42    spl1_8 <=> ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.42  fof(f64,plain,(
% 0.21/0.42    k1_xboole_0 = k9_relat_1(k1_xboole_0,k1_xboole_0) | (~spl1_5 | ~spl1_8)),
% 0.21/0.42    inference(resolution,[],[f61,f48])).
% 0.21/0.42  fof(f61,plain,(
% 0.21/0.42    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k9_relat_1(X0,k1_xboole_0)) ) | ~spl1_8),
% 0.21/0.42    inference(avatar_component_clause,[],[f60])).
% 0.21/0.42  fof(f62,plain,(
% 0.21/0.42    spl1_8),
% 0.21/0.42    inference(avatar_split_clause,[],[f21,f60])).
% 0.21/0.42  fof(f21,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f11])).
% 0.21/0.42  fof(f11,plain,(
% 0.21/0.42    ! [X0] : (k1_xboole_0 = k9_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.42    inference(ennf_transformation,[],[f5])).
% 0.21/0.42  fof(f5,axiom,(
% 0.21/0.42    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k9_relat_1(X0,k1_xboole_0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl1_7),
% 0.21/0.42    inference(avatar_split_clause,[],[f20,f56])).
% 0.21/0.42  fof(f20,plain,(
% 0.21/0.42    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.42    inference(cnf_transformation,[],[f2])).
% 0.21/0.42  fof(f2,axiom,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.42  fof(f54,plain,(
% 0.21/0.42    ~spl1_6),
% 0.21/0.42    inference(avatar_split_clause,[],[f15,f51])).
% 0.21/0.42  fof(f15,plain,(
% 0.21/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(cnf_transformation,[],[f14])).
% 0.21/0.42  fof(f14,plain,(
% 0.21/0.42    k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f10,f13])).
% 0.21/0.42  fof(f13,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k9_relat_1(k1_xboole_0,sK0)),
% 0.21/0.42    introduced(choice_axiom,[])).
% 0.21/0.42  fof(f10,plain,(
% 0.21/0.42    ? [X0] : k1_xboole_0 != k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(ennf_transformation,[],[f9])).
% 0.21/0.42  fof(f9,negated_conjecture,(
% 0.21/0.42    ~! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    inference(negated_conjecture,[],[f8])).
% 0.21/0.42  fof(f8,conjecture,(
% 0.21/0.42    ! [X0] : k1_xboole_0 = k9_relat_1(k1_xboole_0,X0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).
% 0.21/0.42  fof(f49,plain,(
% 0.21/0.42    spl1_5 | ~spl1_1 | ~spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f44,f30,f26,f46])).
% 0.21/0.42  fof(f26,plain,(
% 0.21/0.42    spl1_1 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    spl1_2 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.42  fof(f44,plain,(
% 0.21/0.42    v1_relat_1(k1_xboole_0) | (~spl1_1 | ~spl1_2)),
% 0.21/0.42    inference(superposition,[],[f27,f32])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl1_2),
% 0.21/0.42    inference(avatar_component_clause,[],[f30])).
% 0.21/0.42  fof(f27,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl1_1),
% 0.21/0.42    inference(avatar_component_clause,[],[f26])).
% 0.21/0.42  fof(f38,plain,(
% 0.21/0.42    spl1_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.42  fof(f17,plain,(
% 0.21/0.42    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f6])).
% 0.21/0.42  fof(f6,axiom,(
% 0.21/0.42    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    spl1_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f16,f30])).
% 0.21/0.42  fof(f16,plain,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    inference(cnf_transformation,[],[f7])).
% 0.21/0.42  fof(f7,axiom,(
% 0.21/0.42    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 0.21/0.42  fof(f28,plain,(
% 0.21/0.42    spl1_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f19,f26])).
% 0.21/0.42  fof(f19,plain,(
% 0.21/0.42    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.42    inference(cnf_transformation,[],[f3])).
% 0.21/0.42  fof(f3,axiom,(
% 0.21/0.42    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.42    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (16136)------------------------------
% 0.21/0.42  % (16136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (16136)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (16136)Memory used [KB]: 6140
% 0.21/0.42  % (16136)Time elapsed: 0.005 s
% 0.21/0.42  % (16136)------------------------------
% 0.21/0.42  % (16136)------------------------------
% 0.21/0.42  % (16128)Success in time 0.064 s
%------------------------------------------------------------------------------
