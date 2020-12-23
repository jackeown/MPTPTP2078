%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : xboole_1__t100_xboole_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:19 EDT 2019

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   43 (  49 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :   11
%              Number of atoms          :   68 (  80 expanded)
%              Number of equality atoms :   32 (  36 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f288,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f62,f70,f86,f281])).

fof(f281,plain,
    ( ~ spl2_2
    | spl2_5 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(trivial_inequality_removal,[],[f279])).

fof(f279,plain,
    ( k4_xboole_0(sK0,sK1) != k4_xboole_0(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(superposition,[],[f85,f233])).

fof(f233,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f232,f74])).

fof(f74,plain,
    ( ! [X0] : k2_xboole_0(X0,o_0_0_xboole_0) = X0
    | ~ spl2_2 ),
    inference(superposition,[],[f41,f69])).

fof(f69,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f41,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t100_xboole_1.p',t1_boole)).

fof(f232,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),o_0_0_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f208,f156])).

fof(f156,plain,
    ( ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = o_0_0_xboole_0
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f152,f69])).

fof(f152,plain,(
    ! [X0,X1] : k4_xboole_0(k3_xboole_0(X0,X1),X0) = k1_xboole_0 ),
    inference(resolution,[],[f54,f48])).

fof(f48,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t100_xboole_1.p',t17_xboole_1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k4_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t100_xboole_1.p',l32_xboole_1)).

fof(f208,plain,(
    ! [X2,X1] : k5_xboole_0(X1,k3_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(k3_xboole_0(X1,X2),X1)) ),
    inference(superposition,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t100_xboole_1.p',t47_xboole_1)).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t100_xboole_1.p',d6_xboole_0)).

fof(f85,plain,
    ( k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_5
  <=> k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f86,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f38,f84])).

fof(f38,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f36])).

fof(f36,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t100_xboole_1.p',t100_xboole_1)).

fof(f70,plain,
    ( spl2_2
    | ~ spl2_0 ),
    inference(avatar_split_clause,[],[f63,f60,f68])).

fof(f60,plain,
    ( spl2_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f63,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl2_0 ),
    inference(resolution,[],[f45,f61])).

fof(f61,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f60])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t100_xboole_1.p',t6_boole)).

fof(f62,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f39,f60])).

fof(f39,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/xboole_1__t100_xboole_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
