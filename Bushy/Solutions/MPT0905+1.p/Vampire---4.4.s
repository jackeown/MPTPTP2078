%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t65_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:12 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  44 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    8
%              Number of atoms          :   52 (  60 expanded)
%              Number of equality atoms :   30 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f113,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f65,f85,f112])).

fof(f112,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f111])).

fof(f111,plain,
    ( $false
    | ~ spl5_5 ),
    inference(trivial_inequality_removal,[],[f110])).

fof(f110,plain,
    ( k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3))
    | ~ spl5_5 ),
    inference(superposition,[],[f84,f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) = k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(forward_demodulation,[],[f93,f73])).

fof(f73,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k3_mcart_1(k4_tarski(X0,X1),X2,X3) ),
    inference(forward_demodulation,[],[f72,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] : k4_mcart_1(X0,X1,X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',d4_mcart_1)).

fof(f72,plain,(
    ! [X2,X0,X3,X1] : k3_mcart_1(k4_tarski(X0,X1),X2,X3) = k4_tarski(k3_mcart_1(X0,X1,X2),X3) ),
    inference(superposition,[],[f47,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_mcart_1(X0,X1,X2) = k4_tarski(k4_tarski(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',d3_mcart_1)).

fof(f93,plain,(
    ! [X2,X0,X3,X1] : k1_tarski(k3_mcart_1(k4_tarski(X0,X1),X2,X3)) = k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(superposition,[],[f75,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] : k1_tarski(k3_mcart_1(X0,X1,X2)) = k3_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',t39_mcart_1)).

fof(f75,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),X2,X3) = k3_zfmisc_1(k1_tarski(k4_tarski(X0,X1)),X2,X3) ),
    inference(superposition,[],[f50,f41])).

fof(f41,plain,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k1_tarski(k4_tarski(X0,X1)) = k2_zfmisc_1(k1_tarski(X0),k1_tarski(X1)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',t35_zfmisc_1)).

fof(f50,plain,(
    ! [X2,X0,X3,X1] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] : k4_zfmisc_1(X0,X1,X2,X3) = k3_zfmisc_1(k2_zfmisc_1(X0,X1),X2,X3) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',t54_mcart_1)).

fof(f84,plain,
    ( k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl5_5
  <=> k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f85,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f33])).

fof(f33,plain,
    ( ? [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) != k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3))
   => k1_tarski(k4_mcart_1(sK0,sK1,sK2,sK3)) != k4_zfmisc_1(k1_tarski(sK0),k1_tarski(sK1),k1_tarski(sK2),k1_tarski(sK3)) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) != k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) = k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k1_tarski(k4_mcart_1(X0,X1,X2,X3)) = k4_zfmisc_1(k1_tarski(X0),k1_tarski(X1),k1_tarski(X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',t65_mcart_1)).

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
    inference(resolution,[],[f39,f56])).

fof(f56,plain,
    ( v1_xboole_0(o_0_0_xboole_0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f55])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',t6_boole)).

fof(f57,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f38,f55])).

fof(f38,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t65_mcart_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
