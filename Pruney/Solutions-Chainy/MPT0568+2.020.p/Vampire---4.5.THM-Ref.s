%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:50:12 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   56 (  70 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :  116 ( 149 expanded)
%              Number of equality atoms :   25 (  30 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f122,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f46,f51,f60,f64,f78,f82,f88,f117,f121])).

fof(f121,plain,
    ( spl1_1
    | ~ spl1_6
    | ~ spl1_10
    | ~ spl1_17 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | spl1_1
    | ~ spl1_6
    | ~ spl1_10
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f40,f119])).

fof(f119,plain,
    ( ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)
    | ~ spl1_6
    | ~ spl1_10
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f118,f63])).

fof(f63,plain,
    ( ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl1_6
  <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f118,plain,
    ( ! [X0] : k10_relat_1(k1_xboole_0,X0) = k3_xboole_0(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_10
    | ~ spl1_17 ),
    inference(unit_resulting_resolution,[],[f116,f81])).

fof(f81,plain,
    ( ! [X0,X1] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) )
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl1_10
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f116,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f115])).

fof(f115,plain,
    ( spl1_17
  <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f40,plain,
    ( k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)
    | spl1_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f38,plain,
    ( spl1_1
  <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f117,plain,
    ( spl1_17
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f89,f85,f76,f48,f115])).

fof(f48,plain,
    ( spl1_3
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f76,plain,
    ( spl1_9
  <=> ! [X1,X0] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f85,plain,
    ( spl1_11
  <=> v1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f89,plain,
    ( ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
    | ~ spl1_3
    | ~ spl1_9
    | ~ spl1_11 ),
    inference(subsumption_resolution,[],[f83,f87])).

fof(f87,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f85])).

fof(f83,plain,
    ( ! [X0] :
        ( r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)
        | ~ v1_relat_1(k1_xboole_0) )
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(superposition,[],[f77,f50])).

fof(f50,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f48])).

fof(f77,plain,
    ( ! [X0,X1] :
        ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f76])).

fof(f88,plain,
    ( spl1_11
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f65,f58,f43,f85])).

fof(f43,plain,
    ( spl1_2
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f58,plain,
    ( spl1_5
  <=> ! [X0] :
        ( v1_relat_1(X0)
        | ~ v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f65,plain,
    ( v1_relat_1(k1_xboole_0)
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(unit_resulting_resolution,[],[f45,f59])).

fof(f59,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v1_relat_1(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f58])).

fof(f45,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f82,plain,(
    spl1_10 ),
    inference(avatar_split_clause,[],[f31,f80])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f78,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f30,f76])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

fof(f64,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f26,f62])).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f60,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f27,f58])).

fof(f27,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

fof(f51,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f24,f48])).

fof(f24,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

fof(f46,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f23,f43])).

fof(f23,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f41,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f22,f38])).

fof(f22,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f20])).

fof(f20,plain,
    ( ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)
   => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:29:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (25917)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.46  % (25917)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f41,f46,f51,f60,f64,f78,f82,f88,f117,f121])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    spl1_1 | ~spl1_6 | ~spl1_10 | ~spl1_17),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f120])).
% 0.21/0.46  fof(f120,plain,(
% 0.21/0.46    $false | (spl1_1 | ~spl1_6 | ~spl1_10 | ~spl1_17)),
% 0.21/0.46    inference(subsumption_resolution,[],[f40,f119])).
% 0.21/0.46  fof(f119,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)) ) | (~spl1_6 | ~spl1_10 | ~spl1_17)),
% 0.21/0.46    inference(forward_demodulation,[],[f118,f63])).
% 0.21/0.46  fof(f63,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) ) | ~spl1_6),
% 0.21/0.46    inference(avatar_component_clause,[],[f62])).
% 0.21/0.46  fof(f62,plain,(
% 0.21/0.46    spl1_6 <=> ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    ( ! [X0] : (k10_relat_1(k1_xboole_0,X0) = k3_xboole_0(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl1_10 | ~spl1_17)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f116,f81])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) ) | ~spl1_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f80])).
% 0.21/0.46  fof(f80,plain,(
% 0.21/0.46    spl1_10 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.46  fof(f116,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | ~spl1_17),
% 0.21/0.46    inference(avatar_component_clause,[],[f115])).
% 0.21/0.46  fof(f115,plain,(
% 0.21/0.46    spl1_17 <=> ! [X0] : r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.46  fof(f40,plain,(
% 0.21/0.46    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0) | spl1_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f38])).
% 0.21/0.46  fof(f38,plain,(
% 0.21/0.46    spl1_1 <=> k1_xboole_0 = k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl1_17 | ~spl1_3 | ~spl1_9 | ~spl1_11),
% 0.21/0.46    inference(avatar_split_clause,[],[f89,f85,f76,f48,f115])).
% 0.21/0.46  fof(f48,plain,(
% 0.21/0.46    spl1_3 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.46  fof(f76,plain,(
% 0.21/0.46    spl1_9 <=> ! [X1,X0] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.46  fof(f85,plain,(
% 0.21/0.46    spl1_11 <=> v1_relat_1(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0)) ) | (~spl1_3 | ~spl1_9 | ~spl1_11)),
% 0.21/0.46    inference(subsumption_resolution,[],[f83,f87])).
% 0.21/0.46  fof(f87,plain,(
% 0.21/0.46    v1_relat_1(k1_xboole_0) | ~spl1_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f85])).
% 0.21/0.46  fof(f83,plain,(
% 0.21/0.46    ( ! [X0] : (r1_tarski(k10_relat_1(k1_xboole_0,X0),k1_xboole_0) | ~v1_relat_1(k1_xboole_0)) ) | (~spl1_3 | ~spl1_9)),
% 0.21/0.46    inference(superposition,[],[f77,f50])).
% 0.21/0.46  fof(f50,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl1_3),
% 0.21/0.46    inference(avatar_component_clause,[],[f48])).
% 0.21/0.46  fof(f77,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) ) | ~spl1_9),
% 0.21/0.46    inference(avatar_component_clause,[],[f76])).
% 0.21/0.46  fof(f88,plain,(
% 0.21/0.46    spl1_11 | ~spl1_2 | ~spl1_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f65,f58,f43,f85])).
% 0.21/0.46  fof(f43,plain,(
% 0.21/0.46    spl1_2 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.46  fof(f58,plain,(
% 0.21/0.46    spl1_5 <=> ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.46  fof(f65,plain,(
% 0.21/0.46    v1_relat_1(k1_xboole_0) | (~spl1_2 | ~spl1_5)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f45,f59])).
% 0.21/0.46  fof(f59,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(X0) | v1_relat_1(X0)) ) | ~spl1_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f58])).
% 0.21/0.46  fof(f45,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0) | ~spl1_2),
% 0.21/0.46    inference(avatar_component_clause,[],[f43])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    spl1_10),
% 0.21/0.46    inference(avatar_split_clause,[],[f31,f80])).
% 0.21/0.46  fof(f31,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f19])).
% 0.21/0.46  fof(f19,plain,(
% 0.21/0.46    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f2])).
% 0.21/0.46  fof(f2,axiom,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.21/0.46  fof(f78,plain,(
% 0.21/0.46    spl1_9),
% 0.21/0.46    inference(avatar_split_clause,[],[f30,f76])).
% 0.21/0.46  fof(f30,plain,(
% 0.21/0.46    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f18])).
% 0.21/0.46  fof(f18,plain,(
% 0.21/0.46    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 0.21/0.46    inference(ennf_transformation,[],[f12])).
% 0.21/0.46  fof(f12,axiom,(
% 0.21/0.46    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).
% 0.21/0.46  fof(f64,plain,(
% 0.21/0.46    spl1_6),
% 0.21/0.46    inference(avatar_split_clause,[],[f26,f62])).
% 0.21/0.46  fof(f26,plain,(
% 0.21/0.46    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f3])).
% 0.21/0.46  fof(f3,axiom,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.21/0.46  fof(f60,plain,(
% 0.21/0.46    spl1_5),
% 0.21/0.46    inference(avatar_split_clause,[],[f27,f58])).
% 0.21/0.46  fof(f27,plain,(
% 0.21/0.46    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 0.21/0.46    inference(cnf_transformation,[],[f17])).
% 0.21/0.46  fof(f17,plain,(
% 0.21/0.46    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.46    inference(ennf_transformation,[],[f11])).
% 0.21/0.46  fof(f11,axiom,(
% 0.21/0.46    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).
% 0.21/0.46  fof(f51,plain,(
% 0.21/0.46    spl1_3),
% 0.21/0.46    inference(avatar_split_clause,[],[f24,f48])).
% 0.21/0.46  fof(f24,plain,(
% 0.21/0.46    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f13])).
% 0.21/0.46  fof(f13,axiom,(
% 0.21/0.46    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.46  fof(f46,plain,(
% 0.21/0.46    spl1_2),
% 0.21/0.46    inference(avatar_split_clause,[],[f23,f43])).
% 0.21/0.46  fof(f23,plain,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    inference(cnf_transformation,[],[f1])).
% 0.21/0.46  fof(f1,axiom,(
% 0.21/0.46    v1_xboole_0(k1_xboole_0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.46  fof(f41,plain,(
% 0.21/0.46    ~spl1_1),
% 0.21/0.46    inference(avatar_split_clause,[],[f22,f38])).
% 0.21/0.46  fof(f22,plain,(
% 0.21/0.46    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    inference(cnf_transformation,[],[f21])).
% 0.21/0.46  fof(f21,plain,(
% 0.21/0.46    k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f16,f20])).
% 0.21/0.46  fof(f20,plain,(
% 0.21/0.46    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0) => k1_xboole_0 != k10_relat_1(k1_xboole_0,sK0)),
% 0.21/0.46    introduced(choice_axiom,[])).
% 0.21/0.46  fof(f16,plain,(
% 0.21/0.46    ? [X0] : k1_xboole_0 != k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.46    inference(ennf_transformation,[],[f15])).
% 0.21/0.46  fof(f15,negated_conjecture,(
% 0.21/0.46    ~! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.46    inference(negated_conjecture,[],[f14])).
% 0.21/0.46  fof(f14,conjecture,(
% 0.21/0.46    ! [X0] : k1_xboole_0 = k10_relat_1(k1_xboole_0,X0)),
% 0.21/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).
% 0.21/0.46  % SZS output end Proof for theBenchmark
% 0.21/0.46  % (25917)------------------------------
% 0.21/0.46  % (25917)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.46  % (25917)Termination reason: Refutation
% 0.21/0.46  
% 0.21/0.46  % (25917)Memory used [KB]: 6140
% 0.21/0.46  % (25917)Time elapsed: 0.010 s
% 0.21/0.46  % (25917)------------------------------
% 0.21/0.46  % (25917)------------------------------
% 0.21/0.47  % (25915)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (25911)Success in time 0.104 s
%------------------------------------------------------------------------------
