%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t46_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:27 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   29 (  32 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  44 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f95,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f48,f55,f65,f94])).

fof(f94,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f92])).

fof(f92,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ spl2_5 ),
    inference(superposition,[],[f64,f83])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(resolution,[],[f39,f37])).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t46_xboole_1.p',t7_xboole_1)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t46_xboole_1.p',l32_xboole_1)).

fof(f64,plain,
    ( k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) != k1_xboole_0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl2_5
  <=> k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f65,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f29,f63])).

fof(f29,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f23,f27])).

fof(f27,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) != k1_xboole_0
   => k4_xboole_0(sK0,k2_xboole_0(sK0,sK1)) != k1_xboole_0 ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) != k1_xboole_0 ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X0,X1)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t46_xboole_1.p',t46_xboole_1)).

fof(f55,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f53,plain,
    ( spl2_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f31,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t46_xboole_1.p',d2_xboole_0)).

fof(f48,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f41,f46])).

fof(f46,plain,
    ( spl2_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f41,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f30,f31])).

fof(f30,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t46_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
