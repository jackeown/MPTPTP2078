%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : mcart_1__t25_mcart_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:06 EDT 2019

% Result     : Theorem 0.93s
% Output     : Refutation 0.93s
% Verified   : 
% Statistics : Number of formulae       :   40 (  59 expanded)
%              Number of leaves         :   12 (  21 expanded)
%              Depth                    :    9
%              Number of atoms          :   49 (  74 expanded)
%              Number of equality atoms :   33 (  57 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f28419,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f73,f680,f28268])).

fof(f28268,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f28267])).

fof(f28267,plain,
    ( $false
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f28031,f693])).

fof(f693,plain,(
    ! [X4,X5,X3] : k2_zfmisc_1(k2_tarski(X3,X5),X4) = k2_zfmisc_1(k2_tarski(X5,X3),X4) ),
    inference(superposition,[],[f561,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X2,k2_tarski(X0,X1)) = k2_xboole_0(k2_zfmisc_1(X2,k1_tarski(X0)),k2_zfmisc_1(X2,k1_tarski(X1)))
      & k2_zfmisc_1(k2_tarski(X0,X1),X2) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X0),X2),k2_zfmisc_1(k1_tarski(X1),X2)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',t132_zfmisc_1)).

fof(f561,plain,(
    ! [X6,X7,X5] : k2_zfmisc_1(k2_tarski(X5,X7),X6) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X7),X6),k2_zfmisc_1(k1_tarski(X5),X6)) ),
    inference(superposition,[],[f56,f47])).

fof(f47,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',commutativity_k2_xboole_0)).

fof(f28031,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_zfmisc_1(k2_tarski(sK1,sK0),k2_tarski(sK2,sK3))
    | ~ spl5_5 ),
    inference(superposition,[],[f679,f24726])).

fof(f24726,plain,(
    ! [X6,X8,X7,X9] : k2_zfmisc_1(k2_tarski(X9,X6),k2_tarski(X7,X8)) = k2_enumset1(k4_tarski(X6,X7),k4_tarski(X6,X8),k4_tarski(X9,X7),k4_tarski(X9,X8)) ),
    inference(superposition,[],[f1731,f689])).

fof(f689,plain,(
    ! [X6,X8,X7,X9] : k2_zfmisc_1(k2_tarski(X6,X9),k2_tarski(X7,X8)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X9),k2_tarski(X7,X8)),k2_zfmisc_1(k1_tarski(X6),k2_tarski(X8,X7))) ),
    inference(superposition,[],[f561,f476])).

fof(f476,plain,(
    ! [X4,X5,X3] : k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X5,X4)) ),
    inference(superposition,[],[f144,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] : k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(k4_tarski(X0,X2),k4_tarski(X1,X2)) = k2_zfmisc_1(k2_tarski(X0,X1),k1_tarski(X2))
      & k2_tarski(k4_tarski(X0,X1),k4_tarski(X0,X2)) = k2_zfmisc_1(k1_tarski(X0),k2_tarski(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',t36_zfmisc_1)).

fof(f144,plain,(
    ! [X4,X5,X3] : k2_tarski(k4_tarski(X3,X5),k4_tarski(X3,X4)) = k2_zfmisc_1(k1_tarski(X3),k2_tarski(X4,X5)) ),
    inference(superposition,[],[f54,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',commutativity_k2_tarski)).

fof(f1731,plain,(
    ! [X14,X12,X10,X15,X13,X11] : k2_enumset1(k4_tarski(X13,X14),k4_tarski(X13,X15),k4_tarski(X10,X11),k4_tarski(X10,X12)) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X13),k2_tarski(X14,X15)),k2_zfmisc_1(k1_tarski(X10),k2_tarski(X12,X11))) ),
    inference(superposition,[],[f148,f144])).

fof(f148,plain,(
    ! [X6,X10,X8,X7,X9] : k2_enumset1(k4_tarski(X6,X7),k4_tarski(X6,X8),X9,X10) = k2_xboole_0(k2_zfmisc_1(k1_tarski(X6),k2_tarski(X7,X8)),k2_tarski(X9,X10)) ),
    inference(superposition,[],[f58,f54])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k2_tarski(X0,X1),k2_tarski(X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',t45_enumset1)).

fof(f679,plain,
    ( k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3))
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f678])).

fof(f678,plain,
    ( spl5_5
  <=> k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f680,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f40,f678])).

fof(f40,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f28,f36])).

fof(f36,plain,
    ( ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3))
   => k2_zfmisc_1(k2_tarski(sK0,sK1),k2_tarski(sK2,sK3)) != k2_enumset1(k4_tarski(sK0,sK2),k4_tarski(sK0,sK3),k4_tarski(sK1,sK2),k4_tarski(sK1,sK3)) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) != k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3] : k2_zfmisc_1(k2_tarski(X0,X1),k2_tarski(X2,X3)) = k2_enumset1(k4_tarski(X0,X2),k4_tarski(X0,X3),k4_tarski(X1,X2),k4_tarski(X1,X3)) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',t25_mcart_1)).

fof(f73,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f71])).

fof(f71,plain,
    ( spl5_2
  <=> k1_xboole_0 = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f42,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',d2_xboole_0)).

fof(f66,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f59,f64])).

fof(f64,plain,
    ( spl5_0
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(forward_demodulation,[],[f41,f42])).

fof(f41,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/mcart_1__t25_mcart_1.p',dt_o_0_0_xboole_0)).
%------------------------------------------------------------------------------
