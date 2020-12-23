%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t42_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:07 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   11 (  15 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  58 expanded)
%              Number of equality atoms :   28 (  31 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f768,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f65,f92,f743])).

fof(f743,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f742])).

fof(f742,plain,
    ( $false
    | ~ spl5_5 ),
    inference(trivial_inequality_removal,[],[f718])).

fof(f718,plain,
    ( k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3))
    | ~ spl5_5 ),
    inference(superposition,[],[f91,f102])).

fof(f102,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f101,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t42_mcart_1.p',d3_mcart_1)).

fof(f101,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X3)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(forward_demodulation,[],[f93,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2) ),
    inference(superposition,[],[f47,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t42_mcart_1.p',t35_zfmisc_1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k3_zfmisc_1(X0,X1,X2) = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t42_mcart_1.p',d3_zfmisc_1)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k2_tarski(k3_mcart_1(X0,X1,X2),k4_tarski(k4_tarski(X0,X1),X3)) = k2_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),k2_tarski(X2,X3)) ),
    inference(superposition,[],[f49,f48])).

fof(f49,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t42_mcart_1.p',t36_zfmisc_1)).

fof(f91,plain,
    ( k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_5
  <=> k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f92,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f24,f32])).

fof(f32,plain,
    ( ? [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) != k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3))
   => k2_tarski(k3_mcart_1(sK0,sK1,sK2),k3_mcart_1(sK0,sK1,sK3)) != k3_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k2_tarski(sK2,sK3)) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) != k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k2_tarski(k3_mcart_1(X0,X1,X2),k3_mcart_1(X0,X1,X3)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t42_mcart_1.p',t42_mcart_1)).

fof(f65,plain,
    ( spl5_2
    | ~ spl5_0 ),
    inference(avatar_split_clause,[],[f58,f55,f63])).

fof(f63,plain,
    ( spl5_2
  <=> o_0_0_xboole_0 = k1_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f55,plain,
    ( spl5_0
  <=> v1_xboole_0(o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f58,plain,
    ( o_0_0_xboole_0 = k1_xboole_0
    | ~ spl5_0 ),
    inference(resolution,[],[f38,f56])).

fof(f56,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f55])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t42_mcart_1.p',t6_boole)).

fof(f57,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f37,f55])).

fof(f37,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t42_mcart_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
