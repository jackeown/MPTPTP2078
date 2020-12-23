%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t56_enumset1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:01 EDT 2019

% Result     : Theorem 15.34s
% Output     : Refutation 15.34s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :    7 (   8 expanded)
%              Depth                    :    8
%              Number of atoms          :   29 (  31 expanded)
%              Number of equality atoms :   21 (  22 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f198626,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2737,f198624])).

fof(f198624,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f198623])).

fof(f198623,plain,
    ( $false
    | ~ spl7_1 ),
    inference(trivial_inequality_removal,[],[f198620])).

fof(f198620,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)
    | ~ spl7_1 ),
    inference(superposition,[],[f2736,f82567])).

fof(f82567,plain,(
    ! [X6,X10,X8,X7,X5,X11,X9] : k5_enumset1(X11,X5,X6,X7,X8,X9,X10) = k2_xboole_0(k1_tarski(X11),k4_enumset1(X5,X6,X7,X8,X9,X10)) ),
    inference(forward_demodulation,[],[f82374,f25])).

fof(f25,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t56_enumset1.p',l68_enumset1)).

fof(f82374,plain,(
    ! [X6,X10,X8,X7,X5,X11,X9] : k2_xboole_0(k1_tarski(X11),k4_enumset1(X5,X6,X7,X8,X9,X10)) = k2_xboole_0(k2_enumset1(X11,X5,X6,X7),k1_enumset1(X8,X9,X10)) ),
    inference(superposition,[],[f2361,f24])).

fof(f24,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_enumset1(X3,X4,X5)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t56_enumset1.p',l62_enumset1)).

fof(f2361,plain,(
    ! [X12,X10,X8,X11,X9] : k2_xboole_0(k2_enumset1(X8,X9,X10,X11),X12) = k2_xboole_0(k1_tarski(X8),k2_xboole_0(k1_enumset1(X9,X10,X11),X12)) ),
    inference(superposition,[],[f22,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] : k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t56_enumset1.p',t44_enumset1)).

fof(f22,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t56_enumset1.p',t4_xboole_1)).

fof(f2736,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f2735])).

fof(f2735,plain,
    ( spl7_1
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f2737,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f19,f2735])).

fof(f19,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_tarski(sK0),k4_enumset1(sK1,sK2,sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_tarski(X0),k4_enumset1(X1,X2,X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox2/benchmark/enumset1__t56_enumset1.p',t56_enumset1)).
%------------------------------------------------------------------------------
