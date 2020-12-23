%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t45_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:08 EDT 2019

% Result     : Theorem 1.24s
% Output     : Refutation 1.24s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   13 (  21 expanded)
%              Depth                    :   10
%              Number of atoms          :   62 (  78 expanded)
%              Number of equality atoms :   34 (  43 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f27420,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f68,f161,f4859,f27419])).

fof(f27419,plain,(
    spl6_7 ),
    inference(avatar_contradiction_clause,[],[f27418])).

fof(f27418,plain,
    ( $false
    | ~ spl6_7 ),
    inference(subsumption_resolution,[],[f27417,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t45_mcart_1.p',d3_zfmisc_1)).

fof(f27417,plain,
    ( k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2)),k2_tarski(sK3,sK4))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f27414,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t45_mcart_1.p',t36_zfmisc_1)).

fof(f27414,plain,
    ( k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_zfmisc_1(k2_tarski(k4_tarski(sK0,sK1),k4_tarski(sK0,sK2)),k2_tarski(sK3,sK4))
    | ~ spl6_7 ),
    inference(superposition,[],[f4858,f7430])).

fof(f7430,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X5)) = k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) ),
    inference(forward_demodulation,[],[f7416,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t45_mcart_1.p',d3_mcart_1)).

fof(f7416,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k2_enumset1(k3_mcart_1(X3,X4,X2),k3_mcart_1(X3,X4,X5),k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X5)) = k2_zfmisc_1(k2_tarski(k4_tarski(X3,X4),k4_tarski(X0,X1)),k2_tarski(X2,X5)) ),
    inference(superposition,[],[f1065,f49])).

fof(f1065,plain,(
    ! [X4,X2,X0,X3,X1] : k2_enumset1(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3),k4_tarski(X4,X2),k4_tarski(X4,X3)) = k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X4),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f1049,f49])).

fof(f1049,plain,(
    ! [X4,X2,X0,X3,X1] : k2_enumset1(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X3),k4_tarski(X4,X2),k4_tarski(X4,X3)) = k2_zfmisc_1(k2_tarski(k4_tarski(X0,X1),X4),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f53,f49])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) = k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t45_mcart_1.p',t25_mcart_1)).

fof(f4858,plain,
    ( k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f4857])).

fof(f4857,plain,
    ( spl6_7
  <=> k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f4859,plain,
    ( ~ spl6_7
    | spl6_5 ),
    inference(avatar_split_clause,[],[f2651,f159,f4857])).

fof(f159,plain,
    ( spl6_5
  <=> k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f2651,plain,
    ( k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK2,sK4))
    | ~ spl6_5 ),
    inference(superposition,[],[f160,f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_enumset1(X0,X2,X1,X3) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t45_mcart_1.p',t104_enumset1)).

fof(f160,plain,
    ( k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f161,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f38,f159])).

fof(f38,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f26,f34])).

fof(f34,plain,
    ( ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4))
   => k3_zfmisc_1(k1_tarski(sK0),k2_tarski(sK1,sK2),k2_tarski(sK3,sK4)) != k2_enumset1(k3_mcart_1(sK0,sK1,sK3),k3_mcart_1(sK0,sK2,sK3),k3_mcart_1(sK0,sK1,sK4),k3_mcart_1(sK0,sK2,sK4)) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ? [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) != k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4] : k3_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2),k2_tarski(X3,X4)) = k2_enumset1(k3_mcart_1(X0,X1,X3),k3_mcart_1(X0,X2,X3),k3_mcart_1(X0,X1,X4),k3_mcart_1(X0,X2,X4)) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t45_mcart_1.p',t45_mcart_1)).

fof(f68,plain,
    ( spl6_2
    | ~ spl6_0 ),
    inference(avatar_split_clause,[],[f61,f58,f66])).

fof(f66,plain,
    ( spl6_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f58,plain,
    ( spl6_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f61,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl6_0 ),
    inference(resolution,[],[f40,f59])).

fof(f59,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f58])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t45_mcart_1.p',t6_boole)).

fof(f60,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f39,f58])).

fof(f39,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/mcart_1__t45_mcart_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
