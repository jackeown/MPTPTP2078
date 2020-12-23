%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : relat_1__t208_relat_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:59 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   26 (  29 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  37 expanded)
%              Number of equality atoms :   17 (  20 expanded)
%              Maximal formula depth    :    4 (   2 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f100,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f68,f75,f83,f99])).

fof(f99,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f97,f47])).

fof(f47,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t208_relat_1.p',t69_enumset1)).

fof(f97,plain,
    ( k1_tarski(sK0) != k2_tarski(sK0,sK0)
    | ~ spl2_5 ),
    inference(superposition,[],[f82,f55])).

fof(f55,plain,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_relat_1(k1_tarski(k4_tarski(X0,X1))) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t208_relat_1.p',t32_relat_1)).

fof(f82,plain,
    ( k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0)))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl2_5
  <=> k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f83,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f43,f81])).

fof(f43,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f39])).

fof(f39,plain,
    ( ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0)))
   => k1_tarski(sK0) != k3_relat_1(k1_tarski(k4_tarski(sK0,sK0))) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0] : k1_tarski(X0) != k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] : k1_tarski(X0) = k3_relat_1(k1_tarski(k4_tarski(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t208_relat_1.p',t208_relat_1)).

fof(f75,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f45,f73])).

fof(f73,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f45,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t208_relat_1.p',d2_xboole_0)).

fof(f68,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f61,f66])).

fof(f66,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f61,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f44,f45])).

fof(f44,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/relat_1__t208_relat_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
