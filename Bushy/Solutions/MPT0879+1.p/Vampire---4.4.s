%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t39_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:07 EDT 2019

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :   33 (  38 expanded)
%              Number of leaves         :   10 (  14 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  54 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f90,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f59,f72,f88])).

fof(f88,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f87])).

fof(f87,plain,
    ( $false
    | ~ spl4_5 ),
    inference(trivial_inequality_removal,[],[f85])).

fof(f85,plain,
    ( k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k1_tarski(k3_mcart_1(sK0,sK1,sK2))
    | ~ spl4_5 ),
    inference(superposition,[],[f71,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    inference(forward_demodulation,[],[f77,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t39_mcart_1.p',d3_mcart_1)).

fof(f77,plain,(
    ! [X2,X0,X1] : k1_tarski(k4_tarski(k4_tarski(X0,X1),X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    inference(superposition,[],[f73,f37])).

fof(f37,plain,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t39_mcart_1.p',t35_zfmisc_1)).

fof(f73,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2) ),
    inference(superposition,[],[f43,f37])).

fof(f43,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t39_mcart_1.p',d3_zfmisc_1)).

fof(f71,plain,
    ( k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_5
  <=> k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f72,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f33,f70])).

fof(f33,plain,(
    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f21,f29])).

fof(f29,plain,
    ( ? [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) != k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2))
   => k1_tarski(k3_mcart_1(sK0,sK1,sK2)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2)) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) != k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t39_mcart_1.p',t39_mcart_1)).

fof(f59,plain,
    ( spl4_2
    | ~ spl4_0 ),
    inference(avatar_split_clause,[],[f52,f49,f57])).

fof(f57,plain,
    ( spl4_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f49,plain,
    ( spl4_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_0])])).

fof(f52,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl4_0 ),
    inference(resolution,[],[f35,f50])).

fof(f50,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl4_0 ),
    inference(avatar_component_clause,[],[f49])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t39_mcart_1.p',t6_boole)).

fof(f51,plain,(
    spl4_0 ),
    inference(avatar_split_clause,[],[f34,f49])).

fof(f34,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t39_mcart_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
