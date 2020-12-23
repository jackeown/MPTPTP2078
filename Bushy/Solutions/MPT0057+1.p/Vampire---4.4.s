%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t50_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:28 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   44 (  49 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 (  67 expanded)
%              Number of equality atoms :   32 (  37 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5131,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f67,f120,f128,f5100])).

fof(f5100,plain,(
    spl3_7 ),
    inference(avatar_contradiction_clause,[],[f5099])).

fof(f5099,plain,
    ( $false
    | ~ spl3_7 ),
    inference(trivial_inequality_removal,[],[f5059])).

fof(f5059,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl3_7 ),
    inference(superposition,[],[f127,f883])).

fof(f883,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k3_xboole_0(X22,X23),X24) = k4_xboole_0(k3_xboole_0(X22,X23),k3_xboole_0(X22,X24)) ),
    inference(forward_demodulation,[],[f844,f71])).

fof(f71,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f47,f40])).

fof(f40,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t50_xboole_1.p',t1_boole)).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t50_xboole_1.p',commutativity_k2_xboole_0)).

fof(f844,plain,(
    ! [X24,X23,X22] : k4_xboole_0(k3_xboole_0(X22,X23),k3_xboole_0(X22,X24)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(k3_xboole_0(X22,X23),X24)) ),
    inference(superposition,[],[f52,f96])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(resolution,[],[f49,f46])).

fof(f46,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t50_xboole_1.p',t17_xboole_1)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t50_xboole_1.p',l32_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t50_xboole_1.p',l36_xboole_1)).

fof(f127,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f126,plain,
    ( spl3_7
  <=> k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f128,plain,
    ( ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f121,f118,f126])).

fof(f118,plain,
    ( spl3_5
  <=> k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f121,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),sK2) != k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))
    | ~ spl3_5 ),
    inference(forward_demodulation,[],[f119,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t50_xboole_1.p',t49_xboole_1)).

fof(f119,plain,
    ( k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f120,plain,(
    ~ spl3_5 ),
    inference(avatar_split_clause,[],[f36,f118])).

fof(f36,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f30,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k3_xboole_0(X0,k4_xboole_0(X1,X2))
   => k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) != k3_xboole_0(sK0,k4_xboole_0(sK1,sK2)) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ? [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) != k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) = k3_xboole_0(X0,k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t50_xboole_1.p',t50_xboole_1)).

fof(f67,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f38,f65])).

fof(f65,plain,
    ( spl3_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f38,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t50_xboole_1.p',d2_xboole_0)).

fof(f60,plain,(
    spl3_0 ),
    inference(avatar_split_clause,[],[f53,f58])).

fof(f58,plain,
    ( spl3_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_0])])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f37,f38])).

fof(f37,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/xboole_1__t50_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
