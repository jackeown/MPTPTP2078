%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : enumset1__t58_enumset1.p : TPTP v0.0.0. Released v0.0.0.
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

% Result     : Theorem 13.67s
% Output     : Refutation 13.67s
% Verified   : 
% Statistics : Number of formulae       :   36 (  56 expanded)
%              Number of leaves         :   10 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  74 expanded)
%              Number of equality atoms :   31 (  51 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f219293,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2498,f96684,f210283,f219292])).

fof(f219292,plain,(
    spl7_1 ),
    inference(avatar_contradiction_clause,[],[f219291])).

fof(f219291,plain,
    ( $false
    | ~ spl7_1 ),
    inference(trivial_inequality_removal,[],[f219289])).

fof(f219289,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6)
    | ~ spl7_1 ),
    inference(superposition,[],[f2497,f44693])).

fof(f44693,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_enumset1(X11,X12,X13,X7,X8,X9,X10) = k2_xboole_0(k1_enumset1(X11,X12,X13),k2_enumset1(X7,X8,X9,X10)) ),
    inference(forward_demodulation,[],[f44444,f24])).

fof(f24,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k2_enumset1(X0,X1,X2,X3),k1_enumset1(X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t58_enumset1.p',l68_enumset1)).

fof(f44444,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k2_xboole_0(k1_enumset1(X11,X12,X13),k2_enumset1(X7,X8,X9,X10)) = k2_xboole_0(k2_enumset1(X11,X12,X13,X7),k1_enumset1(X8,X9,X10)) ),
    inference(superposition,[],[f2360,f23])).

fof(f23,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_tarski(X0),k1_enumset1(X1,X2,X3)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t58_enumset1.p',t44_enumset1)).

fof(f2360,plain,(
    ! [X12,X10,X8,X11,X9] : k2_xboole_0(k2_enumset1(X8,X9,X10,X11),X12) = k2_xboole_0(k1_enumset1(X8,X9,X10),k2_xboole_0(k1_tarski(X11),X12)) ),
    inference(superposition,[],[f21,f22])).

fof(f22,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] : k2_enumset1(X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X0,X1,X2),k1_tarski(X3)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t58_enumset1.p',t46_enumset1)).

fof(f21,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k2_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t58_enumset1.p',t4_xboole_1)).

fof(f2497,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6))
    | ~ spl7_1 ),
    inference(avatar_component_clause,[],[f2496])).

fof(f2496,plain,
    ( spl7_1
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f210283,plain,
    ( ~ spl7_5
    | spl7_1 ),
    inference(avatar_split_clause,[],[f210275,f2496,f210281])).

fof(f210281,plain,
    ( spl7_5
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK0,sK1,sK2,sK6,sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f210275,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK0,sK1,sK2,sK6,sK3,sK4,sK5)
    | ~ spl7_1 ),
    inference(superposition,[],[f2497,f44692])).

fof(f44692,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X4,X5,X6,X0,X1,X2,X3) = k2_xboole_0(k1_enumset1(X4,X5,X6),k2_enumset1(X1,X2,X3,X0)) ),
    inference(forward_demodulation,[],[f44443,f24])).

fof(f44443,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k2_xboole_0(k1_enumset1(X4,X5,X6),k2_enumset1(X1,X2,X3,X0)) = k2_xboole_0(k2_enumset1(X4,X5,X6,X0),k1_enumset1(X1,X2,X3)) ),
    inference(superposition,[],[f2360,f2356])).

fof(f2356,plain,(
    ! [X6,X4,X7,X5] : k2_enumset1(X4,X5,X6,X7) = k2_xboole_0(k1_tarski(X7),k1_enumset1(X4,X5,X6)) ),
    inference(superposition,[],[f22,f20])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t58_enumset1.p',commutativity_k2_xboole_0)).

fof(f96684,plain,
    ( ~ spl7_3
    | spl7_1 ),
    inference(avatar_split_clause,[],[f96667,f2496,f96682])).

fof(f96682,plain,
    ( spl7_3
  <=> k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK3,sK4,sK5,sK6,sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f96667,plain,
    ( k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k5_enumset1(sK3,sK4,sK5,sK6,sK0,sK1,sK2)
    | ~ spl7_1 ),
    inference(superposition,[],[f2497,f26543])).

fof(f26543,plain,(
    ! [X12,X10,X8,X7,X13,X11,X9] : k5_enumset1(X7,X8,X9,X10,X11,X12,X13) = k2_xboole_0(k1_enumset1(X11,X12,X13),k2_enumset1(X7,X8,X9,X10)) ),
    inference(superposition,[],[f24,f20])).

fof(f2498,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f18,f2496])).

fof(f18,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5,sK6])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6))
   => k5_enumset1(sK0,sK1,sK2,sK3,sK4,sK5,sK6) != k2_xboole_0(k1_enumset1(sK0,sK1,sK2),k2_enumset1(sK3,sK4,sK5,sK6)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) != k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k1_enumset1(X0,X1,X2),k2_enumset1(X3,X4,X5,X6)) ),
    file('/export/starexec/sandbox/benchmark/enumset1__t58_enumset1.p',t58_enumset1)).
%------------------------------------------------------------------------------
