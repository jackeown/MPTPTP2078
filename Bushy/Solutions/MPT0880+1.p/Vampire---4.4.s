%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t40_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:07 EDT 2019

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   40 (  58 expanded)
%              Number of leaves         :   11 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  78 expanded)
%              Number of equality atoms :   32 (  51 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1109,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f63,f80,f1088])).

fof(f1088,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f1087])).

fof(f1087,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f1050,f302])).

fof(f302,plain,(
    ! [X6,X4,X5,X3] : k3_zfmisc_1(k2_tarski(X3,X4),k1_tarski(X5),X6) = k3_zfmisc_1(k2_tarski(X4,X3),k1_tarski(X5),X6) ),
    inference(superposition,[],[f165,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t40_mcart_1.p',d3_zfmisc_1)).

fof(f165,plain,(
    ! [X4,X2,X5,X3] : k3_zfmisc_1(k2_tarski(X2,X3),k1_tarski(X4),X5) = k2_zfmisc_1(k2_zfmisc_1(k2_tarski(X3,X2),k1_tarski(X4)),X5) ),
    inference(superposition,[],[f46,f145])).

fof(f145,plain,(
    ! [X8,X7,X9] : k2_zfmisc_1(k2_tarski(X7,X9),k1_tarski(X8)) = k2_zfmisc_1(k2_tarski(X9,X7),k1_tarski(X8)) ),
    inference(superposition,[],[f98,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t40_mcart_1.p',t36_zfmisc_1)).

fof(f98,plain,(
    ! [X6,X7,X5] : k2_tarski(k4_tarski(X7,X6),k4_tarski(X5,X6)) = k2_zfmisc_1(k2_tarski(X5,X7),k1_tarski(X6)) ),
    inference(superposition,[],[f48,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t40_mcart_1.p',commutativity_k2_tarski)).

fof(f1050,plain,
    ( k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) != k3_zfmisc_1(k2_tarski(sK1,sK0),k1_tarski(sK2),k1_tarski(sK3))
    | ~ spl5_5 ),
    inference(superposition,[],[f79,f368])).

fof(f368,plain,(
    ! [X10,X8,X11,X9] : k2_tarski(k3_mcart_1(X8,X9,X11),k3_mcart_1(X10,X9,X11)) = k3_zfmisc_1(k2_tarski(X10,X8),k1_tarski(X9),k1_tarski(X11)) ),
    inference(forward_demodulation,[],[f367,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t40_mcart_1.p',d3_mcart_1)).

fof(f367,plain,(
    ! [X10,X8,X11,X9] : k2_tarski(k3_mcart_1(X8,X9,X11),k4_tarski(k4_tarski(X10,X9),X11)) = k3_zfmisc_1(k2_tarski(X10,X8),k1_tarski(X9),k1_tarski(X11)) ),
    inference(forward_demodulation,[],[f337,f46])).

fof(f337,plain,(
    ! [X10,X8,X11,X9] : k2_tarski(k3_mcart_1(X8,X9,X11),k4_tarski(k4_tarski(X10,X9),X11)) = k2_zfmisc_1(k2_zfmisc_1(k2_tarski(X10,X8),k1_tarski(X9)),k1_tarski(X11)) ),
    inference(superposition,[],[f93,f98])).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(k3_mcart_1(X0,X1,X2),k4_tarski(X3,X2)) = k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X3),k1_tarski(X2)) ),
    inference(superposition,[],[f48,f45])).

fof(f79,plain,
    ( k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl5_5
  <=> k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f80,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f35,f78])).

fof(f35,plain,(
    k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f31])).

fof(f31,plain,
    ( ? [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3))
   => k2_tarski(k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK1,sK2,sK3)) != k3_zfmisc_1(k2_tarski(sK0,sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) != k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X2,X3),k3_mcart_1(X1,X2,X3)) = k3_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t40_mcart_1.p',t40_mcart_1)).

fof(f63,plain,
    ( spl5_2
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f56,f53,f61])).

fof(f61,plain,
    ( spl5_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f53,plain,
    ( spl5_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f56,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_0 ),
    inference(resolution,[],[f37,f54])).

fof(f54,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f53])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t40_mcart_1.p',t6_boole)).

fof(f55,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f36,f53])).

fof(f36,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t40_mcart_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
