%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:15 EST 2020

% Result     : CounterSatisfiable 2.15s
% Output     : Saturation 2.15s
% Verified   : 
% Statistics : Number of formulae       :  347 ( 347 expanded)
%              Number of leaves         :  347 ( 347 expanded)
%              Depth                    :    0
%              Number of atoms          : 1627 (1627 expanded)
%              Number of equality atoms :  369 ( 369 expanded)
%              Maximal formula depth    :   14 (   9 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u2300,axiom,(
    ! [X1,X0] :
      ( k3_xboole_0(X1,X0) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) )).

tff(u2299,axiom,(
    ! [X1,X0] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) )).

tff(u2298,negated_conjecture,
    ( ~ ( k1_xboole_0 != sK0 )
    | k1_xboole_0 != sK0 )).

tff(u2297,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) )).

tff(u2296,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X0] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,X0)) )).

tff(u2295,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1] : k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(X1,sK1)) )).

tff(u2294,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X5),sK0) )).

tff(u2293,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5] : k1_xboole_0 = k3_xboole_0(k3_xboole_0(X5,sK1),sK0) )).

tff(u2292,axiom,(
    ! [X3,X2] :
      ( ~ r1_xboole_0(X3,X3)
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) )).

tff(u2291,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X0)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u2290,axiom,(
    ! [X3,X2] :
      ( ~ r1_xboole_0(X3,X2)
      | k1_xboole_0 = k3_xboole_0(X2,X3) ) )).

tff(u2289,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) )).

tff(u2288,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_xboole_0(X2,k3_xboole_0(X1,X0))
      | ~ r1_tarski(X3,X0)
      | k1_xboole_0 = k3_xboole_0(X3,X2)
      | ~ r1_tarski(X2,X1) ) )).

tff(u2287,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_xboole_0(X2,k3_xboole_0(X1,X0))
      | ~ r1_tarski(X2,X0)
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | ~ r1_tarski(X3,X1) ) )).

tff(u2286,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_xboole_0(X6,k3_xboole_0(X5,X7))
      | ~ r1_tarski(X4,X5)
      | k1_xboole_0 = k3_xboole_0(X4,X6)
      | ~ r1_tarski(X6,X7) ) )).

tff(u2285,axiom,(
    ! [X1,X3,X0,X2] :
      ( ~ r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X3)
      | ~ r1_tarski(X3,X2) ) )).

tff(u2284,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(k3_xboole_0(sK1,X8),X9))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(k3_xboole_0(sK1,X8),X9)),X6) ) )).

tff(u2283,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(X8,k3_xboole_0(sK1,X9)))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(X8,k3_xboole_0(sK1,X9))),X6) ) )).

tff(u2282,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(k3_xboole_0(sK1,X8),X9))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(k3_xboole_0(sK1,X8),X9)),X6) ) )).

tff(u2281,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(k3_xboole_0(X8,sK1),X9))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(k3_xboole_0(X8,sK1),X9)),X6) ) )).

tff(u2280,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X7),X8),k3_xboole_0(sK0,X9))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X7),X8),k3_xboole_0(sK0,X9)),X6) ) )).

tff(u2279,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(X8,k3_xboole_0(sK1,X9)))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(X8,k3_xboole_0(sK1,X9))),X6) ) )).

tff(u2278,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(X8,k3_xboole_0(X9,sK1)))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(X8,k3_xboole_0(X9,sK1))),X6) ) )).

tff(u2277,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(sK1,X8)),k3_xboole_0(sK0,X9))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(sK1,X8)),k3_xboole_0(sK0,X9)),X6) ) )).

tff(u2276,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(k3_xboole_0(X8,sK1),X9))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(k3_xboole_0(X8,sK1),X9)),X6) ) )).

tff(u2275,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X7),X8),k3_xboole_0(X9,sK0))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X7),X8),k3_xboole_0(X9,sK0)),X6) ) )).

tff(u2274,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X7,sK1),X8),k3_xboole_0(sK0,X9))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X7,sK1),X8),k3_xboole_0(sK0,X9)),X6) ) )).

tff(u2273,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(X8,k3_xboole_0(X9,sK1)))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(X8,k3_xboole_0(X9,sK1))),X6) ) )).

tff(u2272,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(sK1,X8)),k3_xboole_0(X9,sK0))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(sK1,X8)),k3_xboole_0(X9,sK0)),X6) ) )).

tff(u2271,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,sK1)),k3_xboole_0(sK0,X9))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,sK1)),k3_xboole_0(sK0,X9)),X6) ) )).

tff(u2270,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X7,sK1),X8),k3_xboole_0(X9,sK0))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X7,sK1),X8),k3_xboole_0(X9,sK0)),X6) ) )).

tff(u2269,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X6] :
        ( ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,sK1)),k3_xboole_0(X9,sK0))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,sK1)),k3_xboole_0(X9,sK0)),X6) ) )).

tff(u2268,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X1),X0)
        | ~ r1_tarski(X0,k3_xboole_0(sK1,X2)) ) )).

tff(u2267,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(X3,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,sK0),X3)
        | ~ r1_tarski(X3,k3_xboole_0(sK1,X5)) ) )).

tff(u2266,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X1),X0)
        | ~ r1_tarski(X0,k3_xboole_0(X2,sK1)) ) )).

tff(u2265,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(X3,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,sK0),X3)
        | ~ r1_tarski(X3,k3_xboole_0(X5,sK1)) ) )).

tff(u2264,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X2))
        | ~ r1_tarski(X0,k3_xboole_0(sK1,X1)) ) )).

tff(u2263,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(X3,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X5,sK0))
        | ~ r1_tarski(X3,k3_xboole_0(sK1,X4)) ) )).

tff(u2262,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(X0,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X2))
        | ~ r1_tarski(X0,k3_xboole_0(X1,sK1)) ) )).

tff(u2261,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(X3,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X5,sK0))
        | ~ r1_tarski(X3,k3_xboole_0(X4,sK1)) ) )).

tff(u2260,axiom,(
    ! [X9,X11,X8,X10] :
      ( ~ r1_xboole_0(k3_xboole_0(X10,X11),X9)
      | k1_xboole_0 = k3_xboole_0(X8,X9)
      | ~ r1_tarski(X9,X11)
      | ~ r1_tarski(X8,X10) ) )).

tff(u2259,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_xboole_0(k3_xboole_0(X6,X7),X5)
      | k1_xboole_0 = k3_xboole_0(X4,X5)
      | ~ r1_tarski(X4,X7)
      | ~ r1_tarski(X5,X6) ) )).

tff(u2258,axiom,(
    ! [X9,X7,X8,X6] :
      ( ~ r1_xboole_0(k3_xboole_0(X9,X7),X6)
      | ~ r1_tarski(X8,X9)
      | k1_xboole_0 = k3_xboole_0(X6,X8)
      | ~ r1_tarski(X6,X7) ) )).

tff(u2257,axiom,(
    ! [X5,X7,X4,X6] :
      ( ~ r1_xboole_0(k3_xboole_0(X6,X7),X4)
      | k1_xboole_0 = k3_xboole_0(X4,X5)
      | ~ r1_tarski(X5,X7)
      | ~ r1_tarski(X4,X6) ) )).

tff(u2256,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(sK0,X2),k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X2))
        | ~ r1_tarski(X0,k3_xboole_0(X1,sK1)) ) )).

tff(u2255,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(sK0,X2),k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X2))
        | ~ r1_tarski(X0,k3_xboole_0(sK1,X1)) ) )).

tff(u2254,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1)
        | ~ r1_tarski(X1,k3_xboole_0(X2,sK1)) ) )).

tff(u2253,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1)
        | ~ r1_tarski(X1,k3_xboole_0(sK1,X2)) ) )).

tff(u2252,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k3_xboole_0(X5,sK0),k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X5,sK0))
        | ~ r1_tarski(X3,k3_xboole_0(X4,sK1)) ) )).

tff(u2251,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k3_xboole_0(X5,sK0),k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X5,sK0))
        | ~ r1_tarski(X3,k3_xboole_0(sK1,X4)) ) )).

tff(u2250,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k3_xboole_0(X3,sK0),k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4)
        | ~ r1_tarski(X4,k3_xboole_0(X5,sK1)) ) )).

tff(u2249,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k3_xboole_0(X3,sK0),k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4)
        | ~ r1_tarski(X4,k3_xboole_0(sK1,X5)) ) )).

tff(u2248,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X16,X13,X15,X12,X14] :
        ( ~ r1_xboole_0(k3_xboole_0(X13,X14),k1_xboole_0)
        | ~ r1_tarski(X15,sK0)
        | k1_xboole_0 = k3_xboole_0(X15,X16)
        | ~ r1_tarski(X16,k3_xboole_0(sK1,X12))
        | ~ r1_tarski(X15,X14)
        | ~ r1_tarski(X16,X13) ) )).

tff(u2247,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X18,X20,X17,X19,X21] :
        ( ~ r1_xboole_0(k3_xboole_0(X18,X19),k1_xboole_0)
        | ~ r1_tarski(X20,sK0)
        | k1_xboole_0 = k3_xboole_0(X20,X21)
        | ~ r1_tarski(X21,k3_xboole_0(X17,sK1))
        | ~ r1_tarski(X20,X19)
        | ~ r1_tarski(X21,X18) ) )).

tff(u2246,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X22,X25,X23,X24,X26] :
        ( ~ r1_xboole_0(k3_xboole_0(X23,X24),k1_xboole_0)
        | ~ r1_tarski(X25,k3_xboole_0(sK1,X22))
        | k1_xboole_0 = k3_xboole_0(X25,X26)
        | ~ r1_tarski(X26,sK0)
        | ~ r1_tarski(X25,X24)
        | ~ r1_tarski(X26,X23) ) )).

tff(u2245,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X27,X29,X31,X28,X30] :
        ( ~ r1_xboole_0(k3_xboole_0(X28,X29),k1_xboole_0)
        | ~ r1_tarski(X30,k3_xboole_0(X27,sK1))
        | k1_xboole_0 = k3_xboole_0(X30,X31)
        | ~ r1_tarski(X31,sK0)
        | ~ r1_tarski(X30,X29)
        | ~ r1_tarski(X31,X28) ) )).

tff(u2244,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2,X4] :
        ( ~ r1_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0)
        | ~ r1_tarski(X2,sK0)
        | k1_xboole_0 = k3_xboole_0(X2,X3)
        | ~ r1_tarski(X3,k3_xboole_0(sK1,X4))
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X3,X0) ) )).

tff(u2243,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2,X4] :
        ( ~ r1_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0)
        | ~ r1_tarski(X2,sK0)
        | k1_xboole_0 = k3_xboole_0(X2,X3)
        | ~ r1_tarski(X3,k3_xboole_0(X4,sK1))
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X3,X0) ) )).

tff(u2242,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2,X4] :
        ( ~ r1_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0)
        | ~ r1_tarski(X2,k3_xboole_0(sK1,X3))
        | k1_xboole_0 = k3_xboole_0(X2,X4)
        | ~ r1_tarski(X4,sK0)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X4,X0) ) )).

tff(u2241,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2,X4] :
        ( ~ r1_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0)
        | ~ r1_tarski(X2,k3_xboole_0(X3,sK1))
        | k1_xboole_0 = k3_xboole_0(X2,X4)
        | ~ r1_tarski(X4,sK0)
        | ~ r1_tarski(X2,X1)
        | ~ r1_tarski(X4,X0) ) )).

tff(u2240,axiom,(
    ! [X16,X18,X15,X17,X19,X14] :
      ( ~ r1_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X15,X18))
      | ~ r1_tarski(X14,X15)
      | k1_xboole_0 = k3_xboole_0(X19,X14)
      | ~ r1_tarski(X19,X18)
      | ~ r1_tarski(X14,X17)
      | ~ r1_tarski(X19,X16) ) )).

tff(u2239,axiom,(
    ! [X9,X11,X13,X8,X10,X12] :
      ( ~ r1_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X9,X12))
      | ~ r1_tarski(X8,X9)
      | k1_xboole_0 = k3_xboole_0(X13,X8)
      | ~ r1_tarski(X13,X12)
      | ~ r1_tarski(X13,X11)
      | ~ r1_tarski(X8,X10) ) )).

tff(u2238,axiom,(
    ! [X16,X18,X15,X17,X19,X14] :
      ( ~ r1_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X15,X18))
      | ~ r1_tarski(X14,X15)
      | k1_xboole_0 = k3_xboole_0(X14,X19)
      | ~ r1_tarski(X19,X18)
      | ~ r1_tarski(X19,X17)
      | ~ r1_tarski(X14,X16) ) )).

tff(u2237,axiom,(
    ! [X9,X11,X13,X8,X10,X12] :
      ( ~ r1_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X9,X12))
      | ~ r1_tarski(X8,X9)
      | k1_xboole_0 = k3_xboole_0(X8,X13)
      | ~ r1_tarski(X13,X12)
      | ~ r1_tarski(X8,X11)
      | ~ r1_tarski(X13,X10) ) )).

tff(u2236,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X0] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK1,sK2),X1)) ) )).

tff(u2235,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X0] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(sK1,sK2))) ) )).

tff(u2234,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X1),k3_xboole_0(sK0,X0)) ) )).

tff(u2233,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK0,X0)) ) )).

tff(u2232,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X3),k3_xboole_0(k3_xboole_0(sK1,X4),X5)) ) )).

tff(u2231,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X3),k3_xboole_0(X4,k3_xboole_0(sK1,X5))) ) )).

tff(u2230,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X3),k3_xboole_0(k3_xboole_0(X4,sK1),X5)) ) )).

tff(u2229,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),X1),k3_xboole_0(sK0,X2)) ) )).

tff(u2228,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X3),k3_xboole_0(X4,k3_xboole_0(X5,sK1))) ) )).

tff(u2227,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK1,X1)),k3_xboole_0(sK0,X2)) ) )).

tff(u2226,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),X1),k3_xboole_0(sK0,X2)) ) )).

tff(u2225,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),k3_xboole_0(sK0,X2)) ) )).

tff(u2224,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
        | ~ r1_tarski(X1,k3_xboole_0(sK1,X2))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ) )).

tff(u2223,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0))
        | ~ r1_tarski(X1,k3_xboole_0(X2,sK1))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1) ) )).

tff(u2222,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1))
        | ~ r1_tarski(X0,k3_xboole_0(sK1,X2))
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ) )).

tff(u2221,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1))
        | ~ r1_tarski(X0,k3_xboole_0(X2,sK1))
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X1)) ) )).

tff(u2220,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,sK0),k3_xboole_0(k3_xboole_0(sK1,sK2),X3)) ) )).

tff(u2219,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,sK0),k3_xboole_0(X3,k3_xboole_0(sK1,sK2))) ) )).

tff(u2218,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X3),k3_xboole_0(X2,sK0)) ) )).

tff(u2217,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK1,sK2)),k3_xboole_0(X2,sK0)) ) )).

tff(u2216,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(k3_xboole_0(sK1,X4),X5)) ) )).

tff(u2215,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(X4,k3_xboole_0(sK1,X5))) ) )).

tff(u2214,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(k3_xboole_0(X4,sK1),X5)) ) )).

tff(u2213,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),X1),k3_xboole_0(X2,sK0)) ) )).

tff(u2212,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(X4,k3_xboole_0(X5,sK1))) ) )).

tff(u2211,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK1,X1)),k3_xboole_0(X2,sK0)) ) )).

tff(u2210,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),X1),k3_xboole_0(X2,sK0)) ) )).

tff(u2209,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),k3_xboole_0(X2,sK0)) ) )).

tff(u2208,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0))
        | ~ r1_tarski(X4,k3_xboole_0(sK1,X5))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4) ) )).

tff(u2207,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0))
        | ~ r1_tarski(X4,k3_xboole_0(X5,sK1))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4) ) )).

tff(u2206,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X4,sK0))
        | ~ r1_tarski(X3,k3_xboole_0(sK1,X5))
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,sK0)) ) )).

tff(u2205,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X4,sK0))
        | ~ r1_tarski(X3,k3_xboole_0(X5,sK1))
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,sK0)) ) )).

tff(u2204,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X8] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X8,k3_xboole_0(sK1,sK2)))
        | ~ r1_tarski(X9,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X8,k3_xboole_0(sK1,sK2)),X9) ) )).

tff(u2203,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X9,X8] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X8,k3_xboole_0(sK1,sK2)))
        | k1_xboole_0 = k3_xboole_0(X9,k3_xboole_0(X8,k3_xboole_0(sK1,sK2)))
        | ~ r1_tarski(X9,sK0) ) )).

tff(u2202,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,k3_xboole_0(sK1,X4)))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK1,X4)),k3_xboole_0(X5,sK0)) ) )).

tff(u2201,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,k3_xboole_0(sK1,X4)))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK1,X4)),k3_xboole_0(sK0,X5)) ) )).

tff(u2200,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,k3_xboole_0(sK1,X2)))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(sK1,X2))) ) )).

tff(u2199,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,k3_xboole_0(sK1,X2)))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(sK1,X2))) ) )).

tff(u2198,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,k3_xboole_0(X4,sK1)))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X4,sK1)),k3_xboole_0(X5,sK0)) ) )).

tff(u2197,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,k3_xboole_0(X4,sK1)))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X4,sK1)),k3_xboole_0(sK0,X5)) ) )).

tff(u2196,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,k3_xboole_0(X2,sK1)))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(X2,sK1))) ) )).

tff(u2195,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,k3_xboole_0(X2,sK1)))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(X2,sK1))) ) )).

tff(u2194,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))
        | k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(X0,X1))
        | ~ r1_tarski(X2,sK0)
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,sK1) ) )).

tff(u2193,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,X4))
        | k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(X3,X4))
        | ~ r1_tarski(X5,sK0)
        | ~ r1_tarski(X4,sK2)
        | ~ r1_tarski(X3,sK1) ) )).

tff(u2192,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1))
        | ~ r1_tarski(X2,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),X2)
        | ~ r1_tarski(X0,sK2)
        | ~ r1_tarski(X1,sK1) ) )).

tff(u2191,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,X4))
        | ~ r1_tarski(X5,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,X4),X5)
        | ~ r1_tarski(X4,sK2)
        | ~ r1_tarski(X3,sK1) ) )).

tff(u2190,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X20,X22,X21,X23] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X21,X22))
        | ~ r1_tarski(X20,X21)
        | k1_xboole_0 = k3_xboole_0(X20,X23)
        | ~ r1_tarski(X23,X22)
        | ~ r1_tarski(X23,sK0)
        | ~ r1_tarski(X20,k3_xboole_0(sK1,sK2)) ) )).

tff(u2189,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X25,X27,X24,X26] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X25,X26))
        | ~ r1_tarski(X24,X25)
        | k1_xboole_0 = k3_xboole_0(X24,X27)
        | ~ r1_tarski(X27,X26)
        | ~ r1_tarski(X27,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X24,sK0) ) )).

tff(u2188,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X32,X29,X31,X28,X30] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X29,X30))
        | ~ r1_tarski(k3_xboole_0(sK0,X28),X29)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X28),k3_xboole_0(k3_xboole_0(sK1,X31),X32))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X31),X32),X30) ) )).

tff(u2187,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X34,X36,X33,X35,X37] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X34,X35))
        | ~ r1_tarski(k3_xboole_0(sK0,X33),X34)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X33),k3_xboole_0(k3_xboole_0(X36,sK1),X37))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X36,sK1),X37),X35) ) )).

tff(u2186,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X40,X42,X38,X41,X39] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X39,X40))
        | ~ r1_tarski(k3_xboole_0(sK0,X38),X39)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X38),k3_xboole_0(X41,k3_xboole_0(sK1,X42)))
        | ~ r1_tarski(k3_xboole_0(X41,k3_xboole_0(sK1,X42)),X40) ) )).

tff(u2185,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X44,X46,X43,X45,X47] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X44,X45))
        | ~ r1_tarski(k3_xboole_0(sK0,X43),X44)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X43),k3_xboole_0(X46,k3_xboole_0(X47,sK1)))
        | ~ r1_tarski(k3_xboole_0(X46,k3_xboole_0(X47,sK1)),X45) ) )).

tff(u2184,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X49,X51,X48,X50,X52] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X49,X50))
        | ~ r1_tarski(k3_xboole_0(X48,sK0),X49)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X48,sK0),k3_xboole_0(k3_xboole_0(sK1,X51),X52))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X51),X52),X50) ) )).

tff(u2183,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X53,X55,X56,X54,X57] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X54,X55))
        | ~ r1_tarski(k3_xboole_0(X53,sK0),X54)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X53,sK0),k3_xboole_0(k3_xboole_0(X56,sK1),X57))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X56,sK1),X57),X55) ) )).

tff(u2182,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X58,X60,X62,X59,X61] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X59,X60))
        | ~ r1_tarski(k3_xboole_0(X58,sK0),X59)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X58,sK0),k3_xboole_0(X61,k3_xboole_0(sK1,X62)))
        | ~ r1_tarski(k3_xboole_0(X61,k3_xboole_0(sK1,X62)),X60) ) )).

tff(u2181,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X63,X65,X67,X64,X66] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X64,X65))
        | ~ r1_tarski(k3_xboole_0(X63,sK0),X64)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X63,sK0),k3_xboole_0(X66,k3_xboole_0(X67,sK1)))
        | ~ r1_tarski(k3_xboole_0(X66,k3_xboole_0(X67,sK1)),X65) ) )).

tff(u2180,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X69,X71,X72,X68,X70] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X70,X71))
        | ~ r1_tarski(k3_xboole_0(X68,k3_xboole_0(sK1,X69)),X70)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X68,k3_xboole_0(sK1,X69)),k3_xboole_0(sK0,X72))
        | ~ r1_tarski(k3_xboole_0(sK0,X72),X71) ) )).

tff(u2179,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X73,X75,X77,X74,X76] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X75,X76))
        | ~ r1_tarski(k3_xboole_0(X73,k3_xboole_0(sK1,X74)),X75)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X73,k3_xboole_0(sK1,X74)),k3_xboole_0(X77,sK0))
        | ~ r1_tarski(k3_xboole_0(X77,sK0),X76) ) )).

tff(u2178,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X82,X79,X81,X78,X80] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X80,X81))
        | ~ r1_tarski(k3_xboole_0(X78,k3_xboole_0(X79,sK1)),X80)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X78,k3_xboole_0(X79,sK1)),k3_xboole_0(sK0,X82))
        | ~ r1_tarski(k3_xboole_0(sK0,X82),X81) ) )).

tff(u2177,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X84,X86,X83,X85,X87] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X85,X86))
        | ~ r1_tarski(k3_xboole_0(X83,k3_xboole_0(X84,sK1)),X85)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X83,k3_xboole_0(X84,sK1)),k3_xboole_0(X87,sK0))
        | ~ r1_tarski(k3_xboole_0(X87,sK0),X86) ) )).

tff(u2176,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X89,X91,X88,X90,X92] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X90,X91))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X88),X89),X90)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X88),X89),k3_xboole_0(sK0,X92))
        | ~ r1_tarski(k3_xboole_0(sK0,X92),X91) ) )).

tff(u2175,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X96,X93,X95,X97,X94] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X95,X96))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X93),X94),X95)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X93),X94),k3_xboole_0(X97,sK0))
        | ~ r1_tarski(k3_xboole_0(X97,sK0),X96) ) )).

tff(u2174,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X98,X100,X102,X99,X101] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X100,X101))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X98,sK1),X99),X100)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X98,sK1),X99),k3_xboole_0(sK0,X102))
        | ~ r1_tarski(k3_xboole_0(sK0,X102),X101) ) )).

tff(u2173,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X104,X106,X105,X107,X103] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X105,X106))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X103,sK1),X104),X105)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X103,sK1),X104),k3_xboole_0(X107,sK0))
        | ~ r1_tarski(k3_xboole_0(X107,sK0),X106) ) )).

tff(u2172,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X20,X22,X21,X23] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X21,X22))
        | ~ r1_tarski(X20,X21)
        | k1_xboole_0 = k3_xboole_0(X23,X20)
        | ~ r1_tarski(X23,X22)
        | ~ r1_tarski(X20,sK0)
        | ~ r1_tarski(X23,k3_xboole_0(sK1,sK2)) ) )).

tff(u2171,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X25,X27,X24,X26] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X25,X26))
        | ~ r1_tarski(X24,X25)
        | k1_xboole_0 = k3_xboole_0(X27,X24)
        | ~ r1_tarski(X27,X26)
        | ~ r1_tarski(X24,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X27,sK0) ) )).

tff(u2170,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X32,X29,X31,X28,X30] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X30,X31))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X28),X29),X30)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X32),k3_xboole_0(k3_xboole_0(sK1,X28),X29))
        | ~ r1_tarski(k3_xboole_0(sK0,X32),X31) ) )).

tff(u2169,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X34,X36,X33,X35,X37] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X35,X36))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X33,sK1),X34),X35)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X37),k3_xboole_0(k3_xboole_0(X33,sK1),X34))
        | ~ r1_tarski(k3_xboole_0(sK0,X37),X36) ) )).

tff(u2168,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X40,X42,X38,X41,X39] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X40,X41))
        | ~ r1_tarski(k3_xboole_0(X38,k3_xboole_0(sK1,X39)),X40)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X42),k3_xboole_0(X38,k3_xboole_0(sK1,X39)))
        | ~ r1_tarski(k3_xboole_0(sK0,X42),X41) ) )).

tff(u2167,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X44,X46,X43,X45,X47] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X45,X46))
        | ~ r1_tarski(k3_xboole_0(X43,k3_xboole_0(X44,sK1)),X45)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X47),k3_xboole_0(X43,k3_xboole_0(X44,sK1)))
        | ~ r1_tarski(k3_xboole_0(sK0,X47),X46) ) )).

tff(u2166,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X49,X51,X48,X50,X52] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X50,X51))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X48),X49),X50)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X52,sK0),k3_xboole_0(k3_xboole_0(sK1,X48),X49))
        | ~ r1_tarski(k3_xboole_0(X52,sK0),X51) ) )).

tff(u2165,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X53,X55,X56,X54,X57] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X55,X56))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X53,sK1),X54),X55)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X57,sK0),k3_xboole_0(k3_xboole_0(X53,sK1),X54))
        | ~ r1_tarski(k3_xboole_0(X57,sK0),X56) ) )).

tff(u2164,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X58,X60,X62,X59,X61] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X60,X61))
        | ~ r1_tarski(k3_xboole_0(X58,k3_xboole_0(sK1,X59)),X60)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X62,sK0),k3_xboole_0(X58,k3_xboole_0(sK1,X59)))
        | ~ r1_tarski(k3_xboole_0(X62,sK0),X61) ) )).

tff(u2163,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X63,X65,X67,X64,X66] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X65,X66))
        | ~ r1_tarski(k3_xboole_0(X63,k3_xboole_0(X64,sK1)),X65)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X67,sK0),k3_xboole_0(X63,k3_xboole_0(X64,sK1)))
        | ~ r1_tarski(k3_xboole_0(X67,sK0),X66) ) )).

tff(u2162,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X69,X71,X72,X68,X70] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X69,X70))
        | ~ r1_tarski(k3_xboole_0(sK0,X68),X69)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X71,k3_xboole_0(sK1,X72)),k3_xboole_0(sK0,X68))
        | ~ r1_tarski(k3_xboole_0(X71,k3_xboole_0(sK1,X72)),X70) ) )).

tff(u2161,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X73,X75,X77,X74,X76] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X74,X75))
        | ~ r1_tarski(k3_xboole_0(X73,sK0),X74)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X76,k3_xboole_0(sK1,X77)),k3_xboole_0(X73,sK0))
        | ~ r1_tarski(k3_xboole_0(X76,k3_xboole_0(sK1,X77)),X75) ) )).

tff(u2160,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X82,X79,X81,X78,X80] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X79,X80))
        | ~ r1_tarski(k3_xboole_0(sK0,X78),X79)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X81,k3_xboole_0(X82,sK1)),k3_xboole_0(sK0,X78))
        | ~ r1_tarski(k3_xboole_0(X81,k3_xboole_0(X82,sK1)),X80) ) )).

tff(u2159,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X84,X86,X83,X85,X87] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X84,X85))
        | ~ r1_tarski(k3_xboole_0(X83,sK0),X84)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X86,k3_xboole_0(X87,sK1)),k3_xboole_0(X83,sK0))
        | ~ r1_tarski(k3_xboole_0(X86,k3_xboole_0(X87,sK1)),X85) ) )).

tff(u2158,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X89,X91,X88,X90,X92] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X89,X90))
        | ~ r1_tarski(k3_xboole_0(sK0,X88),X89)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X91),X92),k3_xboole_0(sK0,X88))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X91),X92),X90) ) )).

tff(u2157,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X96,X93,X95,X97,X94] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X94,X95))
        | ~ r1_tarski(k3_xboole_0(X93,sK0),X94)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X96),X97),k3_xboole_0(X93,sK0))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X96),X97),X95) ) )).

tff(u2156,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X98,X100,X102,X99,X101] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X99,X100))
        | ~ r1_tarski(k3_xboole_0(sK0,X98),X99)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X101,sK1),X102),k3_xboole_0(sK0,X98))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X101,sK1),X102),X100) ) )).

tff(u2155,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X104,X106,X105,X107,X103] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X104,X105))
        | ~ r1_tarski(k3_xboole_0(X103,sK0),X104)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X106,sK1),X107),k3_xboole_0(X103,sK0))
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X106,sK1),X107),X105) ) )).

tff(u2154,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X16,X13,X15,X12,X14] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X13,X14))
        | ~ r1_tarski(X15,X13)
        | k1_xboole_0 = k3_xboole_0(X15,X16)
        | ~ r1_tarski(X16,X14)
        | ~ r1_tarski(X15,k3_xboole_0(sK1,X12))
        | ~ r1_tarski(X16,sK0) ) )).

tff(u2153,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X18,X20,X17,X19,X21] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X18,X19))
        | ~ r1_tarski(X20,X18)
        | k1_xboole_0 = k3_xboole_0(X20,X21)
        | ~ r1_tarski(X21,X19)
        | ~ r1_tarski(X20,k3_xboole_0(X17,sK1))
        | ~ r1_tarski(X21,sK0) ) )).

tff(u2152,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X22,X25,X23,X24,X26] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X23,X24))
        | ~ r1_tarski(X25,X23)
        | k1_xboole_0 = k3_xboole_0(X25,X26)
        | ~ r1_tarski(X26,X24)
        | ~ r1_tarski(X25,sK0)
        | ~ r1_tarski(X26,k3_xboole_0(sK1,X22)) ) )).

tff(u2151,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X27,X29,X31,X28,X30] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X28,X29))
        | ~ r1_tarski(X30,X28)
        | k1_xboole_0 = k3_xboole_0(X30,X31)
        | ~ r1_tarski(X31,X29)
        | ~ r1_tarski(X30,sK0)
        | ~ r1_tarski(X31,k3_xboole_0(X27,sK1)) ) )).

tff(u2150,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = k3_xboole_0(X2,X3)
        | ~ r1_tarski(X3,X1)
        | ~ r1_tarski(X2,k3_xboole_0(sK1,X4))
        | ~ r1_tarski(X3,sK0) ) )).

tff(u2149,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = k3_xboole_0(X2,X3)
        | ~ r1_tarski(X3,X1)
        | ~ r1_tarski(X2,k3_xboole_0(X4,sK1))
        | ~ r1_tarski(X3,sK0) ) )).

tff(u2148,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = k3_xboole_0(X2,X3)
        | ~ r1_tarski(X3,X1)
        | ~ r1_tarski(X2,sK0)
        | ~ r1_tarski(X3,k3_xboole_0(sK1,X4)) ) )).

tff(u2147,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0))
        | ~ r1_tarski(X2,X0)
        | k1_xboole_0 = k3_xboole_0(X2,X3)
        | ~ r1_tarski(X3,X1)
        | ~ r1_tarski(X2,sK0)
        | ~ r1_tarski(X3,k3_xboole_0(X4,sK1)) ) )).

tff(u2146,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X7,X6] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),X6))
        | ~ r1_tarski(X7,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X6),X7) ) )).

tff(u2145,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X7,X6] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),X6))
        | k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(sK1,sK2),X6))
        | ~ r1_tarski(X7,sK0) ) )).

tff(u2144,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X3),X4))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X3),X4),k3_xboole_0(X5,sK0)) ) )).

tff(u2143,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X3),X4))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X3),X4),k3_xboole_0(sK0,X5)) ) )).

tff(u2142,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X1),X2))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(sK1,X1),X2)) ) )).

tff(u2141,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X1),X2))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK1,X1),X2)) ) )).

tff(u2140,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X3,sK1),X4))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,sK1),X4),k3_xboole_0(X5,sK0)) ) )).

tff(u2139,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X3,sK1),X4))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,sK1),X4),k3_xboole_0(sK0,X5)) ) )).

tff(u2138,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,sK1),X2))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X1,sK1),X2)) ) )).

tff(u2137,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,sK1),X2))
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(X1,sK1),X2)) ) )).

tff(u2136,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X1))
        | ~ r1_tarski(X0,k3_xboole_0(sK1,X2)) ) )).

tff(u2135,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,X3)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,sK0))
        | ~ r1_tarski(X3,k3_xboole_0(sK1,X5)) ) )).

tff(u2134,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X1))
        | ~ r1_tarski(X0,k3_xboole_0(X2,sK1)) ) )).

tff(u2133,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,X3)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,sK0))
        | ~ r1_tarski(X3,k3_xboole_0(X5,sK1)) ) )).

tff(u2132,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,X1)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1)
        | ~ r1_tarski(X1,k3_xboole_0(sK1,X2)) ) )).

tff(u2131,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,X4)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4)
        | ~ r1_tarski(X4,k3_xboole_0(sK1,X5)) ) )).

tff(u2130,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_xboole_0(k1_xboole_0,X1)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1)
        | ~ r1_tarski(X1,k3_xboole_0(X2,sK1)) ) )).

tff(u2129,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_xboole_0(k1_xboole_0,X4)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4)
        | ~ r1_tarski(X4,k3_xboole_0(X5,sK1)) ) )).

tff(u2128,negated_conjecture,
    ( ~ ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_xboole_0) )).

tff(u2127,negated_conjecture,
    ( ~ ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,sK1) )).

tff(u2126,negated_conjecture,
    ( ~ ~ r1_xboole_0(sK2,sK2)
    | ~ r1_xboole_0(sK2,sK2) )).

tff(u2125,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X21] : r1_xboole_0(k3_xboole_0(sK1,X21),sK0) )).

tff(u2124,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X0] : r1_xboole_0(k3_xboole_0(X0,sK1),sK0) )).

tff(u2123,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X13] : r1_xboole_0(sK0,k3_xboole_0(sK1,X13)) )).

tff(u2122,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X0] : r1_xboole_0(sK0,k3_xboole_0(X0,sK1)) )).

tff(u2121,axiom,(
    ! [X1,X0,X2] :
      ( ~ r1_tarski(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | k1_xboole_0 = X0
      | ~ r1_tarski(X0,X1) ) )).

tff(u2120,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X3,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X2,sK0)
        | ~ r1_xboole_0(X4,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X3,X2)
        | ~ r1_tarski(k3_xboole_0(X3,X2),X4) ) )).

tff(u2119,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X3,X2] :
        ( ~ r1_tarski(X1,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X2,sK0)
        | ~ r1_xboole_0(X3,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X2,X1)
        | ~ r1_tarski(k3_xboole_0(X2,X1),X3) ) )).

tff(u2118,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X13,X12] :
        ( ~ r1_tarski(X12,k3_xboole_0(sK1,sK2))
        | ~ r1_xboole_0(k1_xboole_0,X13)
        | ~ r1_tarski(X13,sK0)
        | k1_xboole_0 = k3_xboole_0(X12,X13) ) )).

tff(u2117,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X8] :
        ( ~ r1_tarski(X8,k3_xboole_0(sK1,sK2))
        | ~ r1_xboole_0(k1_xboole_0,X8)
        | ~ r1_tarski(X9,sK0)
        | k1_xboole_0 = k3_xboole_0(X8,X9) ) )).

tff(u2116,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X15,X14] :
        ( ~ r1_tarski(X15,k3_xboole_0(sK1,sK2))
        | ~ r1_xboole_0(k1_xboole_0,X15)
        | k1_xboole_0 = k3_xboole_0(X14,X15)
        | ~ r1_tarski(X14,sK0) ) )).

tff(u2115,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X11,X10] :
        ( ~ r1_tarski(X11,k3_xboole_0(sK1,sK2))
        | ~ r1_xboole_0(k1_xboole_0,X10)
        | k1_xboole_0 = k3_xboole_0(X10,X11)
        | ~ r1_tarski(X10,sK0) ) )).

tff(u2114,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X3,k3_xboole_0(sK1,X4))
        | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X5,sK0)),k1_xboole_0) ) )).

tff(u2113,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,k3_xboole_0(sK1,X1))
        | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X2)),k1_xboole_0) ) )).

tff(u2112,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X3,k3_xboole_0(sK1,X4))
        | r1_tarski(k3_xboole_0(k3_xboole_0(X5,sK0),X3),k1_xboole_0) ) )).

tff(u2111,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,k3_xboole_0(sK1,X1))
        | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X2),X0),k1_xboole_0) ) )).

tff(u2110,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X1,k3_xboole_0(X0,sK1))
        | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,sK0)),k1_xboole_0) ) )).

tff(u2109,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X1,k3_xboole_0(X0,sK1))
        | r1_tarski(k3_xboole_0(X1,k3_xboole_0(sK0,X2)),k1_xboole_0) ) )).

tff(u2108,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X1,k3_xboole_0(X0,sK1))
        | r1_tarski(k3_xboole_0(k3_xboole_0(X2,sK0),X1),k1_xboole_0) ) )).

tff(u2107,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X1,k3_xboole_0(X0,sK1))
        | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X2),X1),k1_xboole_0) ) )).

tff(u2106,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X7,X6] :
        ( ~ r1_tarski(X6,sK0)
        | k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(k3_xboole_0(sK1,sK2),X7))
        | ~ r1_xboole_0(k1_xboole_0,X6) ) )).

tff(u2105,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X9,X8] :
        ( ~ r1_tarski(X8,sK0)
        | k1_xboole_0 = k3_xboole_0(X8,k3_xboole_0(X9,k3_xboole_0(sK1,sK2)))
        | ~ r1_xboole_0(k1_xboole_0,X8) ) )).

tff(u2104,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X7,X6] :
        ( ~ r1_tarski(X6,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X6)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X7),X6) ) )).

tff(u2103,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X8] :
        ( ~ r1_tarski(X8,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X8)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X9,k3_xboole_0(sK1,sK2)),X8) ) )).

tff(u2102,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X18,X17,X19] :
        ( ~ r1_tarski(X18,sK0)
        | ~ r1_tarski(X19,k3_xboole_0(sK1,X17))
        | r1_tarski(k3_xboole_0(X18,X19),k1_xboole_0) ) )).

tff(u2101,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X29,X31,X30] :
        ( ~ r1_tarski(X31,sK0)
        | ~ r1_tarski(X30,k3_xboole_0(sK1,X29))
        | r1_tarski(k3_xboole_0(X30,X31),k1_xboole_0) ) )).

tff(u2100,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X40,X38,X39] :
        ( ~ r1_tarski(X39,sK0)
        | k1_xboole_0 = k3_xboole_0(X39,X40)
        | ~ r1_tarski(X40,k3_xboole_0(sK1,X38))
        | ~ r1_xboole_0(k1_xboole_0,X39) ) )).

tff(u2099,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X46,X45,X47] :
        ( ~ r1_tarski(X47,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X46)
        | k1_xboole_0 = k3_xboole_0(X46,X47)
        | ~ r1_tarski(X46,k3_xboole_0(sK1,X45)) ) )).

tff(u2098,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X18,X17,X19] :
        ( ~ r1_tarski(X18,sK0)
        | ~ r1_tarski(X19,k3_xboole_0(X17,sK1))
        | r1_tarski(k3_xboole_0(X18,X19),k1_xboole_0) ) )).

tff(u2097,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X29,X31,X30] :
        ( ~ r1_tarski(X31,sK0)
        | ~ r1_tarski(X30,k3_xboole_0(X29,sK1))
        | r1_tarski(k3_xboole_0(X30,X31),k1_xboole_0) ) )).

tff(u2096,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X40,X38,X39] :
        ( ~ r1_tarski(X39,sK0)
        | k1_xboole_0 = k3_xboole_0(X39,X40)
        | ~ r1_tarski(X40,k3_xboole_0(X38,sK1))
        | ~ r1_xboole_0(k1_xboole_0,X39) ) )).

tff(u2095,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X46,X45,X47] :
        ( ~ r1_tarski(X47,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X46)
        | k1_xboole_0 = k3_xboole_0(X46,X47)
        | ~ r1_tarski(X46,k3_xboole_0(X45,sK1)) ) )).

tff(u2094,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X8,X10] :
        ( ~ r1_tarski(X9,sK0)
        | k1_xboole_0 = k3_xboole_0(X10,X9)
        | ~ r1_tarski(X10,k3_xboole_0(sK1,X8))
        | ~ r1_xboole_0(k1_xboole_0,X9) ) )).

tff(u2093,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X11,X13,X12] :
        ( ~ r1_tarski(X12,sK0)
        | k1_xboole_0 = k3_xboole_0(X13,X12)
        | ~ r1_tarski(X13,k3_xboole_0(X11,sK1))
        | ~ r1_xboole_0(k1_xboole_0,X12) ) )).

tff(u2092,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X16,X15,X14] :
        ( ~ r1_tarski(X16,sK0)
        | k1_xboole_0 = k3_xboole_0(X16,X15)
        | ~ r1_xboole_0(k1_xboole_0,X15)
        | ~ r1_tarski(X15,k3_xboole_0(sK1,X14)) ) )).

tff(u2091,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X18,X17,X19] :
        ( ~ r1_tarski(X19,sK0)
        | k1_xboole_0 = k3_xboole_0(X19,X18)
        | ~ r1_xboole_0(k1_xboole_0,X18)
        | ~ r1_tarski(X18,k3_xboole_0(X17,sK1)) ) )).

tff(u2090,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X2,sK0)
        | k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(sK2,X3),k3_xboole_0(sK1,X4)))
        | ~ r1_xboole_0(k1_xboole_0,X2) ) )).

tff(u2089,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X5,X7,X6] :
        ( ~ r1_tarski(X5,sK0)
        | k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X6,sK2),k3_xboole_0(sK1,X7)))
        | ~ r1_xboole_0(k1_xboole_0,X5) ) )).

tff(u2088,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X2,sK0)
        | k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(sK2,X3),k3_xboole_0(X4,sK1)))
        | ~ r1_xboole_0(k1_xboole_0,X2) ) )).

tff(u2087,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X5,X7,X6] :
        ( ~ r1_tarski(X5,sK0)
        | k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X6,sK2),k3_xboole_0(X7,sK1)))
        | ~ r1_xboole_0(k1_xboole_0,X5) ) )).

tff(u2086,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(sK2,X2))) ) )).

tff(u2085,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X3,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X3)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,sK1),k3_xboole_0(sK2,X5))) ) )).

tff(u2084,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,sK2))) ) )).

tff(u2083,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X3,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X3)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,sK1),k3_xboole_0(X5,sK2))) ) )).

tff(u2082,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X4,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,X2),k3_xboole_0(sK1,X3)),X4)
        | ~ r1_xboole_0(k1_xboole_0,X4) ) )).

tff(u2081,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X6] :
        ( ~ r1_tarski(X7,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X5,sK2),k3_xboole_0(sK1,X6)),X7)
        | ~ r1_xboole_0(k1_xboole_0,X7) ) )).

tff(u2080,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X4,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,X2),k3_xboole_0(X3,sK1)),X4)
        | ~ r1_xboole_0(k1_xboole_0,X4) ) )).

tff(u2079,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X6] :
        ( ~ r1_tarski(X7,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X5,sK2),k3_xboole_0(X6,sK1)),X7)
        | ~ r1_xboole_0(k1_xboole_0,X7) ) )).

tff(u2078,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X2)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK2,X1)),X2) ) )).

tff(u2077,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X5,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X5)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,sK1),k3_xboole_0(sK2,X4)),X5) ) )).

tff(u2076,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X2)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X1,sK2)),X2) ) )).

tff(u2075,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X5,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X5)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,sK1),k3_xboole_0(X4,sK2)),X5) ) )).

tff(u2074,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X9,X8,X10] :
        ( ~ r1_tarski(X8,sK0)
        | ~ r1_xboole_0(X9,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X8,k3_xboole_0(k3_xboole_0(sK1,sK2),X10))
        | ~ r1_tarski(k3_xboole_0(X8,k3_xboole_0(k3_xboole_0(sK1,sK2),X10)),X9) ) )).

tff(u2073,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X11,X13,X12] :
        ( ~ r1_tarski(X11,sK0)
        | ~ r1_xboole_0(X12,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X11,k3_xboole_0(X13,k3_xboole_0(sK1,sK2)))
        | ~ r1_tarski(k3_xboole_0(X11,k3_xboole_0(X13,k3_xboole_0(sK1,sK2))),X12) ) )).

tff(u2072,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X8,X10] :
        ( ~ r1_tarski(X8,sK0)
        | ~ r1_xboole_0(X9,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X10),X8)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X10),X8),X9) ) )).

tff(u2071,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X11,X13,X12] :
        ( ~ r1_tarski(X11,sK0)
        | ~ r1_xboole_0(X12,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X13,k3_xboole_0(sK1,sK2)),X11)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X13,k3_xboole_0(sK1,sK2)),X11),X12) ) )).

tff(u2070,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X8,X10] :
        ( ~ r1_tarski(X9,sK0)
        | ~ r1_xboole_0(X9,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X9,X10)
        | ~ r1_tarski(X10,k3_xboole_0(sK1,X8)) ) )).

tff(u2069,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X11,X13,X12] :
        ( ~ r1_tarski(X12,sK0)
        | ~ r1_xboole_0(X12,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X12,X13)
        | ~ r1_tarski(X13,k3_xboole_0(X11,sK1)) ) )).

tff(u2068,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X16,X15,X14] :
        ( ~ r1_tarski(X16,sK0)
        | ~ r1_tarski(X15,k3_xboole_0(sK1,X14))
        | k1_xboole_0 = k3_xboole_0(X15,X16)
        | ~ r1_xboole_0(X15,k1_xboole_0) ) )).

tff(u2067,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X18,X17,X19] :
        ( ~ r1_tarski(X19,sK0)
        | ~ r1_tarski(X18,k3_xboole_0(X17,sK1))
        | k1_xboole_0 = k3_xboole_0(X18,X19)
        | ~ r1_xboole_0(X18,k1_xboole_0) ) )).

tff(u2066,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X8,X10] :
        ( ~ r1_tarski(X10,sK0)
        | ~ r1_xboole_0(X9,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X10,X9)
        | ~ r1_tarski(X9,k3_xboole_0(sK1,X8)) ) )).

tff(u2065,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X11,X13,X12] :
        ( ~ r1_tarski(X13,sK0)
        | ~ r1_xboole_0(X12,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X13,X12)
        | ~ r1_tarski(X12,k3_xboole_0(X11,sK1)) ) )).

tff(u2064,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X16,X15,X14] :
        ( ~ r1_tarski(X15,sK0)
        | ~ r1_tarski(X16,k3_xboole_0(sK1,X14))
        | k1_xboole_0 = k3_xboole_0(X16,X15)
        | ~ r1_xboole_0(X15,k1_xboole_0) ) )).

tff(u2063,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X18,X17,X19] :
        ( ~ r1_tarski(X18,sK0)
        | ~ r1_tarski(X19,k3_xboole_0(X17,sK1))
        | k1_xboole_0 = k3_xboole_0(X19,X18)
        | ~ r1_xboole_0(X18,k1_xboole_0) ) )).

tff(u2062,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X3,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),X3)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),X3),X0)
        | ~ r1_tarski(X1,sK2)
        | ~ r1_xboole_0(X0,k1_xboole_0) ) )).

tff(u2061,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X7,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X5,k3_xboole_0(X6,sK1)),X7)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X5,k3_xboole_0(X6,sK1)),X7),X4)
        | ~ r1_tarski(X5,sK2)
        | ~ r1_xboole_0(X4,k1_xboole_0) ) )).

tff(u2060,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,sK0),X2)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK0),X2),X0)
        | ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ r1_tarski(X1,sK1) ) )).

tff(u2059,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4,X6] :
        ( ~ r1_tarski(X6,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(sK2,X5)),X6)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(sK2,X5)),X6),X3)
        | ~ r1_xboole_0(X3,k1_xboole_0)
        | ~ r1_tarski(X4,sK1) ) )).

tff(u2058,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X7,X8,X10] :
        ( ~ r1_tarski(X10,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X8,k3_xboole_0(X9,sK2)),X10)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X8,k3_xboole_0(X9,sK2)),X10),X7)
        | ~ r1_xboole_0(X7,k1_xboole_0)
        | ~ r1_tarski(X8,sK1) ) )).

tff(u2057,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X5,X4,X6] :
        ( ~ r1_tarski(X3,sK0)
        | ~ r1_tarski(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(sK2,X4),k3_xboole_0(sK1,X5))),X6)
        | ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(sK2,X4),k3_xboole_0(sK1,X5))) ) )).

tff(u2056,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X9,X7,X8,X10] :
        ( ~ r1_tarski(X7,sK0)
        | ~ r1_tarski(k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(X8,sK2),k3_xboole_0(sK1,X9))),X10)
        | ~ r1_xboole_0(X10,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(X8,sK2),k3_xboole_0(sK1,X9))) ) )).

tff(u2055,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X5,X4,X6] :
        ( ~ r1_tarski(X3,sK0)
        | ~ r1_tarski(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(sK2,X4),k3_xboole_0(X5,sK1))),X6)
        | ~ r1_xboole_0(X6,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(sK2,X4),k3_xboole_0(X5,sK1))) ) )).

tff(u2054,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X9,X7,X8,X10] :
        ( ~ r1_tarski(X7,sK0)
        | ~ r1_tarski(k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(X8,sK2),k3_xboole_0(X9,sK1))),X10)
        | ~ r1_xboole_0(X10,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(X8,sK2),k3_xboole_0(X9,sK1))) ) )).

tff(u2053,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(sK2,X2))),X3)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(sK2,X2)))
        | ~ r1_xboole_0(X3,k1_xboole_0) ) )).

tff(u2052,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X4,sK0)
        | ~ r1_tarski(k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X5,sK1),k3_xboole_0(sK2,X6))),X7)
        | k1_xboole_0 = k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X5,sK1),k3_xboole_0(sK2,X6)))
        | ~ r1_xboole_0(X7,k1_xboole_0) ) )).

tff(u2051,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,sK2))),X3)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,sK2)))
        | ~ r1_xboole_0(X3,k1_xboole_0) ) )).

tff(u2050,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X4,sK0)
        | ~ r1_tarski(k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X5,sK1),k3_xboole_0(X6,sK2))),X7)
        | k1_xboole_0 = k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X5,sK1),k3_xboole_0(X6,sK2)))
        | ~ r1_xboole_0(X7,k1_xboole_0) ) )).

tff(u2049,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,sK1)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X1,X2))
        | ~ r1_tarski(X0,sK0)
        | ~ r1_tarski(X1,sK2)
        | ~ r1_xboole_0(k1_xboole_0,X0) ) )).

tff(u2048,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,X2),X0)
        | ~ r1_tarski(X1,sK2)
        | ~ r1_xboole_0(k1_xboole_0,X0) ) )).

tff(u2047,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X0] :
        ( ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = k3_xboole_0(sK0,X0) ) )).

tff(u2046,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(X1,X3)
        | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,X2)),k1_xboole_0) ) )).

tff(u2045,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X5,sK1)
        | ~ r1_tarski(X6,X7)
        | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X4),k3_xboole_0(X5,X6)),k1_xboole_0) ) )).

tff(u2044,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(X1,X3)
        | r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,X2)),k1_xboole_0) ) )).

tff(u2043,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X5,sK1)
        | ~ r1_tarski(X6,X7)
        | r1_tarski(k3_xboole_0(k3_xboole_0(X4,sK0),k3_xboole_0(X5,X6)),k1_xboole_0) ) )).

tff(u2042,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(X0,X3)
        | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(sK0,X2)),k1_xboole_0) ) )).

tff(u2041,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(X5,X7)
        | r1_tarski(k3_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(sK0,X6)),k1_xboole_0) ) )).

tff(u2040,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(X0,X3)
        | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)),k1_xboole_0) ) )).

tff(u2039,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(X5,X7)
        | r1_tarski(k3_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X6,sK0)),k1_xboole_0) ) )).

tff(u2038,negated_conjecture,
    ( ~ ! [X2] :
          ( ~ r1_tarski(X2,sK1)
          | k1_xboole_0 = k3_xboole_0(X2,sK0) )
    | ! [X2] :
        ( ~ r1_tarski(X2,sK1)
        | k1_xboole_0 = k3_xboole_0(X2,sK0) ) )).

tff(u2037,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X0] :
        ( ~ r1_tarski(X1,sK1)
        | ~ r1_tarski(X0,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X1,sK0)) ) )).

tff(u2036,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X3,sK1)
        | ~ r1_tarski(X2,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X2)
        | k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(X3,k3_xboole_0(sK2,X4))) ) )).

tff(u2035,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X5,X7,X6] :
        ( ~ r1_tarski(X6,sK1)
        | ~ r1_tarski(X5,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X5)
        | k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(X6,k3_xboole_0(X7,sK2))) ) )).

tff(u2034,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0] :
        ( ~ r1_tarski(X1,sK1)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,sK0),X0)
        | ~ r1_xboole_0(k1_xboole_0,X0)
        | ~ r1_tarski(X0,sK0) ) )).

tff(u2033,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X2,X4] :
        ( ~ r1_tarski(X3,sK1)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK2,X4)),X2)
        | ~ r1_xboole_0(k1_xboole_0,X2)
        | ~ r1_tarski(X2,sK0) ) )).

tff(u2032,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X6] :
        ( ~ r1_tarski(X6,sK1)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,k3_xboole_0(X7,sK2)),X5)
        | ~ r1_xboole_0(k1_xboole_0,X5)
        | ~ r1_tarski(X5,sK0) ) )).

tff(u2031,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X3,sK1)
        | ~ r1_xboole_0(X1,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X2,X3))
        | ~ r1_tarski(k3_xboole_0(X0,k3_xboole_0(X2,X3)),X1)
        | ~ r1_tarski(X2,sK2)
        | ~ r1_tarski(X0,sK0) ) )).

tff(u2030,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X3,sK1)
        | ~ r1_xboole_0(X1,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,X3),X0)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X2,X3),X0),X1)
        | ~ r1_tarski(X2,sK2)
        | ~ r1_tarski(X0,sK0) ) )).

tff(u2029,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X2,sK1)
        | k1_xboole_0 = k3_xboole_0(X1,k3_xboole_0(X2,sK0))
        | ~ r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,sK0)),X0)
        | ~ r1_tarski(X1,sK0)
        | ~ r1_xboole_0(X0,k1_xboole_0) ) )).

tff(u2028,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X5,X4,X6] :
        ( ~ r1_tarski(X5,sK1)
        | k1_xboole_0 = k3_xboole_0(X4,k3_xboole_0(X5,k3_xboole_0(sK2,X6)))
        | ~ r1_tarski(k3_xboole_0(X4,k3_xboole_0(X5,k3_xboole_0(sK2,X6))),X3)
        | ~ r1_tarski(X4,sK0)
        | ~ r1_xboole_0(X3,k1_xboole_0) ) )).

tff(u2027,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X9,X7,X8,X10] :
        ( ~ r1_tarski(X9,sK1)
        | k1_xboole_0 = k3_xboole_0(X8,k3_xboole_0(X9,k3_xboole_0(X10,sK2)))
        | ~ r1_tarski(k3_xboole_0(X8,k3_xboole_0(X9,k3_xboole_0(X10,sK2))),X7)
        | ~ r1_tarski(X8,sK0)
        | ~ r1_xboole_0(X7,k1_xboole_0) ) )).

tff(u2026,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,X1)),X2)
        | ~ r1_xboole_0(X2,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,X1)) ) )).

tff(u2025,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X3,sK1)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(X4,sK0)),X5)
        | ~ r1_xboole_0(X5,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(X4,sK0)) ) )).

tff(u2024,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k3_xboole_0(sK0,X2)),X3)
        | ~ r1_xboole_0(X3,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k3_xboole_0(sK0,X2)) ) )).

tff(u2023,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(sK2,X5)),k3_xboole_0(X6,sK0)),X7)
        | ~ r1_xboole_0(X7,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(sK2,X5)),k3_xboole_0(X6,sK0)) ) )).

tff(u2022,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK2)),k3_xboole_0(sK0,X2)),X3)
        | ~ r1_xboole_0(X3,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK2)),k3_xboole_0(sK0,X2)) ) )).

tff(u2021,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X4,sK1)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X5,sK2)),k3_xboole_0(X6,sK0)),X7)
        | ~ r1_xboole_0(X7,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X5,sK2)),k3_xboole_0(X6,sK0)) ) )).

tff(u2020,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X5,sK2)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,X5))
        | ~ r1_tarski(X3,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X3)
        | ~ r1_tarski(X4,sK1) ) )).

tff(u2019,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X5,sK2)
        | ~ r1_tarski(X3,sK0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,X5),X3)
        | ~ r1_xboole_0(k1_xboole_0,X3)
        | ~ r1_tarski(X4,sK1) ) )).

tff(u2018,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X1,sK2)
        | ~ r1_tarski(X0,sK0)
        | k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,X2)))
        | ~ r1_xboole_0(k1_xboole_0,X0) ) )).

tff(u2017,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X4,sK2)
        | ~ r1_tarski(X3,sK0)
        | k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,k3_xboole_0(X5,sK1)))
        | ~ r1_xboole_0(k1_xboole_0,X3) ) )).

tff(u2016,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( ~ r1_tarski(X1,sK2)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),X0)
        | ~ r1_tarski(X0,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X0) ) )).

tff(u2015,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X5,X4] :
        ( ~ r1_tarski(X4,sK2)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X5,sK1)),X3)
        | ~ r1_tarski(X3,sK0)
        | ~ r1_xboole_0(k1_xboole_0,X3) ) )).

tff(u2014,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X7,sK2)
        | ~ r1_xboole_0(X5,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(X4,k3_xboole_0(X6,X7))
        | ~ r1_tarski(k3_xboole_0(X4,k3_xboole_0(X6,X7)),X5)
        | ~ r1_tarski(X4,sK0)
        | ~ r1_tarski(X6,sK1) ) )).

tff(u2013,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X7,sK2)
        | ~ r1_xboole_0(X5,k1_xboole_0)
        | k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,X7),X4)
        | ~ r1_tarski(k3_xboole_0(k3_xboole_0(X6,X7),X4),X5)
        | ~ r1_tarski(X4,sK0)
        | ~ r1_tarski(X6,sK1) ) )).

tff(u2012,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X1,X3,X0,X2] :
        ( ~ r1_tarski(X2,sK2)
        | k1_xboole_0 = k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(sK1,X3)))
        | ~ r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(sK1,X3))),X0)
        | ~ r1_xboole_0(X0,k1_xboole_0)
        | ~ r1_tarski(X1,sK0) ) )).

tff(u2011,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X5,X7,X4,X6] :
        ( ~ r1_tarski(X6,sK2)
        | k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(X6,k3_xboole_0(X7,sK1)))
        | ~ r1_tarski(k3_xboole_0(X5,k3_xboole_0(X6,k3_xboole_0(X7,sK1))),X4)
        | ~ r1_xboole_0(X4,k1_xboole_0)
        | ~ r1_tarski(X5,sK0) ) )).

tff(u2010,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X11,X10] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X10)
        | ~ r1_tarski(sK0,X11)
        | r1_tarski(k1_xboole_0,k3_xboole_0(X10,X11)) ) )).

tff(u2009,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X9,X8] :
        ( ~ r1_tarski(k3_xboole_0(sK1,sK2),X9)
        | r1_tarski(k1_xboole_0,k3_xboole_0(X8,X9))
        | ~ r1_tarski(sK0,X8) ) )).

tff(u2008,negated_conjecture,
    ( ~ ~ r1_tarski(k3_xboole_0(sK1,sK2),sK0)
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),sK0) )).

tff(u2007,negated_conjecture,
    ( ~ ~ r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) )).

tff(u2006,axiom,(
    ! [X11,X13,X10,X12,X14] :
      ( ~ r1_tarski(k3_xboole_0(X10,X12),X14)
      | ~ r1_tarski(X12,X13)
      | ~ r1_xboole_0(X14,k3_xboole_0(X13,X11))
      | k1_xboole_0 = k3_xboole_0(X10,X12)
      | ~ r1_tarski(X10,X11) ) )).

tff(u2005,axiom,(
    ! [X1,X3,X0,X2,X4] :
      ( ~ r1_tarski(k3_xboole_0(X2,X0),X4)
      | ~ r1_tarski(X2,X3)
      | ~ r1_xboole_0(X4,k3_xboole_0(X3,X1))
      | k1_xboole_0 = k3_xboole_0(X2,X0)
      | ~ r1_tarski(X0,X1) ) )).

tff(u2004,axiom,(
    ! [X5,X4,X6] :
      ( ~ r1_tarski(k3_xboole_0(X6,X5),X4)
      | k1_xboole_0 = k3_xboole_0(X6,X5)
      | ~ r1_xboole_0(X4,X5) ) )).

tff(u2003,axiom,(
    ! [X1,X3,X2] :
      ( ~ r1_tarski(k3_xboole_0(X2,X3),X1)
      | k1_xboole_0 = k3_xboole_0(X2,X3)
      | ~ r1_xboole_0(X1,X2) ) )).

tff(u2002,negated_conjecture,
    ( ~ ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0) )).

tff(u2001,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X27,X26,X28] :
        ( ~ r1_tarski(sK0,X28)
        | r1_tarski(k1_xboole_0,k3_xboole_0(X27,X28))
        | ~ r1_tarski(k3_xboole_0(X26,sK1),X27) ) )).

tff(u2000,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X16,X15,X14] :
        ( ~ r1_tarski(sK0,X15)
        | ~ r1_tarski(k3_xboole_0(X14,sK1),X16)
        | r1_tarski(k1_xboole_0,k3_xboole_0(X15,X16)) ) )).

tff(u1999,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X27,X26,X28] :
        ( ~ r1_tarski(sK0,X28)
        | r1_tarski(k1_xboole_0,k3_xboole_0(X27,X28))
        | ~ r1_tarski(k3_xboole_0(sK1,X26),X27) ) )).

tff(u1998,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X16,X15,X14] :
        ( ~ r1_tarski(sK0,X15)
        | ~ r1_tarski(k3_xboole_0(sK1,X14),X16)
        | r1_tarski(k1_xboole_0,k3_xboole_0(X15,X16)) ) )).

tff(u1997,negated_conjecture,
    ( ~ ! [X0] :
          ( ~ r1_tarski(sK0,X0)
          | ~ r1_xboole_0(X0,sK2) )
    | ! [X0] :
        ( ~ r1_tarski(sK0,X0)
        | ~ r1_xboole_0(X0,sK2) ) )).

tff(u1996,negated_conjecture,
    ( ~ ~ r1_tarski(sK0,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK0,k3_xboole_0(sK1,sK2)) )).

tff(u1995,negated_conjecture,
    ( ~ ~ r1_tarski(sK0,sK0)
    | ~ r1_tarski(sK0,sK0) )).

tff(u1994,negated_conjecture,
    ( ~ ~ r1_tarski(sK0,sK1)
    | ~ r1_tarski(sK0,sK1) )).

tff(u1993,negated_conjecture,
    ( ~ ~ r1_tarski(sK1,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK1,k3_xboole_0(sK1,sK2)) )).

tff(u1992,negated_conjecture,
    ( ~ ~ r1_tarski(sK1,sK0)
    | ~ r1_tarski(sK1,sK0) )).

tff(u1991,negated_conjecture,
    ( ~ ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,sK1) )).

tff(u1990,negated_conjecture,
    ( ~ ~ r1_tarski(sK1,sK2)
    | ~ r1_tarski(sK1,sK2) )).

tff(u1989,negated_conjecture,
    ( ~ ~ r1_tarski(sK2,k3_xboole_0(sK1,sK2))
    | ~ r1_tarski(sK2,k3_xboole_0(sK1,sK2)) )).

tff(u1988,negated_conjecture,
    ( ~ ~ r1_tarski(sK2,sK0)
    | ~ r1_tarski(sK2,sK0) )).

tff(u1987,negated_conjecture,
    ( ~ ~ r1_tarski(sK2,sK1)
    | ~ r1_tarski(sK2,sK1) )).

tff(u1986,negated_conjecture,
    ( ~ ~ r1_tarski(sK2,sK2)
    | ~ r1_tarski(sK2,sK2) )).

tff(u1985,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | r1_tarski(sK0,sK2) )).

tff(u1984,axiom,(
    ! [X1,X0] : r1_tarski(k3_xboole_0(X0,X1),X0) )).

tff(u1983,axiom,(
    ! [X1,X0] : r1_tarski(k3_xboole_0(X1,X0),X0) )).

tff(u1982,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_tarski(k3_xboole_0(X1,X0),k3_xboole_0(X2,X3))
      | ~ r1_tarski(X1,X3)
      | ~ r1_tarski(X0,X2) ) )).

tff(u1981,axiom,(
    ! [X1,X3,X0,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) )).

tff(u1980,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X11,X10] :
        ( r1_tarski(k3_xboole_0(X10,X11),k1_xboole_0)
        | ~ r1_tarski(X11,sK0)
        | ~ r1_tarski(X10,k3_xboole_0(sK1,sK2)) ) )).

tff(u1979,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X9,X8] :
        ( r1_tarski(k3_xboole_0(X8,X9),k1_xboole_0)
        | ~ r1_tarski(X9,k3_xboole_0(sK1,sK2))
        | ~ r1_tarski(X8,sK0) ) )).

tff(u1978,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X9,X8,X10] : r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X8),k3_xboole_0(k3_xboole_0(sK1,X9),X10)),k1_xboole_0) )).

tff(u1977,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(k3_xboole_0(X0,sK1),X2)),k1_xboole_0) )).

tff(u1976,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X11,X13,X12] : r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X11),k3_xboole_0(X12,k3_xboole_0(sK1,X13))),k1_xboole_0) )).

tff(u1975,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(X2,k3_xboole_0(X0,sK1))),k1_xboole_0) )).

tff(u1974,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X7,X8,X6] : r1_tarski(k3_xboole_0(k3_xboole_0(X6,sK0),k3_xboole_0(k3_xboole_0(sK1,X7),X8)),k1_xboole_0) )).

tff(u1973,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(k3_xboole_0(X0,sK1),X2)),k1_xboole_0) )).

tff(u1972,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X7,X8,X6] : r1_tarski(k3_xboole_0(k3_xboole_0(X6,sK0),k3_xboole_0(X7,k3_xboole_0(sK1,X8))),k1_xboole_0) )).

tff(u1971,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(X2,k3_xboole_0(X0,sK1))),k1_xboole_0) )).

tff(u1970,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),k3_xboole_0(sK0,X0)),k1_xboole_0) )).

tff(u1969,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),k3_xboole_0(X0,sK0)),k1_xboole_0) )).

tff(u1968,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,sK1)),k3_xboole_0(sK0,X0)),k1_xboole_0) )).

tff(u1967,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,sK1)),k3_xboole_0(X0,sK0)),k1_xboole_0) )).

tff(u1966,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X1),X2),k3_xboole_0(sK0,X0)),k1_xboole_0) )).

tff(u1965,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X1),X2),k3_xboole_0(X0,sK0)),k1_xboole_0) )).

tff(u1964,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,sK1),X2),k3_xboole_0(sK0,X0)),k1_xboole_0) )).

tff(u1963,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] : r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,sK1),X2),k3_xboole_0(X0,sK0)),k1_xboole_0) )).

tff(u1962,negated_conjecture,
    ( ~ r1_tarski(k1_xboole_0,sK0)
    | r1_tarski(k1_xboole_0,sK0) )).

tff(u1961,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X5,X4] :
        ( r1_tarski(k1_xboole_0,k3_xboole_0(X5,k3_xboole_0(X4,X3)))
        | ~ r1_tarski(sK2,X4)
        | ~ r1_tarski(sK1,X3)
        | ~ r1_tarski(sK0,X5) ) )).

tff(u1960,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(sK0,k3_xboole_0(sK1,sK2))
    | ! [X3,X2,X4] :
        ( r1_tarski(k1_xboole_0,k3_xboole_0(X2,k3_xboole_0(X3,X4)))
        | ~ r1_tarski(sK0,X2)
        | ~ r1_tarski(sK2,X4)
        | ~ r1_tarski(sK1,X3) ) )).

tff(u1959,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X0] : r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK1)) )).

tff(u1958,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X0] : r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK2)) )).

tff(u1957,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X1,X0,X2] :
        ( r1_tarski(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,X0),X2))
        | ~ r1_tarski(sK2,X1)
        | ~ r1_tarski(sK0,X2)
        | ~ r1_tarski(sK1,X0) ) )).

tff(u1956,negated_conjecture,
    ( k1_xboole_0 != k3_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X3,X2,X4] :
        ( r1_tarski(k1_xboole_0,k3_xboole_0(k3_xboole_0(X3,X4),X2))
        | ~ r1_tarski(sK0,X2)
        | ~ r1_tarski(sK2,X4)
        | ~ r1_tarski(sK1,X3) ) )).

tff(u1955,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X20] : r1_tarski(k1_xboole_0,k3_xboole_0(sK1,X20)) )).

tff(u1954,negated_conjecture,
    ( ~ r1_tarski(sK0,sK2)
    | ~ r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)
    | ! [X0] : r1_tarski(k1_xboole_0,k3_xboole_0(sK2,X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:01:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (25190)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_79 on theBenchmark
% 0.22/0.43  % (25197)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_211 on theBenchmark
% 0.22/0.43  % (25198)ott+2_20_add=off:afp=10000:afq=2.0:anc=none:bs=unit_only:fde=unused:irw=on:lma=on:nm=4:nwc=1:sas=z3:sac=on:urr=ec_only:uhcvi=on_420 on theBenchmark
% 0.22/0.44  % (25188)lrs-11_8_afr=on:afp=100000:afq=2.0:anc=none:bd=off:cond=on:gs=on:lma=on:nm=2:newcnf=on:nwc=3:stl=30:sac=on:sp=occurrence_6 on theBenchmark
% 0.22/0.46  % (25195)lrs+11_3:2_add=large:afr=on:afp=10000:afq=1.2:amm=off:anc=none:bs=unit_only:cond=on:gs=on:gsaa=full_model:gsem=off:irw=on:lwlo=on:nm=32:nwc=1.2:sas=z3:stl=90:sac=on_214 on theBenchmark
% 0.22/0.46  % (25191)lrs+1004_5:4_aac=none:add=large:afp=100000:afq=1.4:anc=all_dependent:bd=off:cond=fast:gsp=input_only:gs=on:gsem=off:lma=on:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sp=occurrence:updr=off:uhcvi=on_99 on theBenchmark
% 0.22/0.47  % (25192)lrs-11_24_av=off:bd=off:bs=on:fsr=off:gs=on:gsem=off:lma=on:nm=4:nwc=1.7:stl=90:sp=occurrence:updr=off_61 on theBenchmark
% 0.22/0.48  % (25193)ott+11_50_add=large:afr=on:afp=40000:afq=1.1:amm=sco:anc=all:bd=off:cond=fast:gs=on:gsem=on:irw=on:lma=on:nm=0:nwc=1:sp=occurrence:updr=off:uhcvi=on_102 on theBenchmark
% 0.22/0.48  % (25199)ott+10_1024_afp=40000:afq=2.0:amm=off:anc=all:bd=preordered:bs=unit_only:fde=unused:irw=on:nm=16:nwc=1:sp=reverse_arity:uhcvi=on_823 on theBenchmark
% 0.22/0.48  % (25189)lrs+1011_5:1_acc=on:amm=off:anc=all_dependent:bd=off:ccuc=small_ones:fde=unused:gs=on:gsaa=full_model:gsem=off:lcm=predicate:lwlo=on:nm=6:newcnf=on:nwc=2.5:stl=30:sp=occurrence:updr=off_3 on theBenchmark
% 0.22/0.48  % (25196)ott+4_1024_afr=on:afp=4000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:cond=fast:gsp=input_only:gs=on:gsaa=from_current:nm=16:nwc=1.1:nicw=on:sas=z3:sp=occurrence:updr=off_1389 on theBenchmark
% 0.22/0.49  % (25197)Refutation not found, incomplete strategy% (25197)------------------------------
% 0.22/0.49  % (25197)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (25197)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (25197)Memory used [KB]: 6012
% 0.22/0.49  % (25197)Time elapsed: 0.065 s
% 0.22/0.49  % (25197)------------------------------
% 0.22/0.49  % (25197)------------------------------
% 0.22/0.49  % (25201)lrs+10_5:1_add=large:afp=1000:afq=1.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=fast:fsr=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=2:nwc=1:stl=210:uhcvi=on_1759 on theBenchmark
% 1.39/0.55  % (25191)Refutation not found, incomplete strategy% (25191)------------------------------
% 1.39/0.55  % (25191)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.39/0.55  % (25191)Termination reason: Refutation not found, incomplete strategy
% 1.39/0.55  
% 1.39/0.55  % (25191)Memory used [KB]: 11385
% 1.39/0.55  % (25191)Time elapsed: 0.134 s
% 1.39/0.55  % (25191)------------------------------
% 1.39/0.55  % (25191)------------------------------
% 2.15/0.65  % SZS status CounterSatisfiable for theBenchmark
% 2.15/0.65  % (25196)# SZS output start Saturation.
% 2.15/0.65  tff(u2300,axiom,
% 2.15/0.65      (![X1, X0] : (((k3_xboole_0(X1,X0) != k1_xboole_0) | r1_xboole_0(X0,X1))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2299,axiom,
% 2.15/0.65      (![X1, X0] : (((k3_xboole_0(X0,X1) != k1_xboole_0) | r1_xboole_0(X0,X1))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2298,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 != sK0)) | (k1_xboole_0 != sK0))).
% 2.15/0.65  
% 2.15/0.65  tff(u2297,axiom,
% 2.15/0.65      (![X1, X0] : ((k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2296,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X0] : ((k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,X0))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2295,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1] : ((k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(X1,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2294,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X5] : ((k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,X5),sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2293,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X5] : ((k1_xboole_0 = k3_xboole_0(k3_xboole_0(X5,sK1),sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2292,axiom,
% 2.15/0.65      (![X3, X2] : ((~r1_xboole_0(X3,X3) | (k1_xboole_0 = k3_xboole_0(X2,X3)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2291,axiom,
% 2.15/0.65      (![X1, X0] : ((~r1_xboole_0(X0,X0) | (k3_xboole_0(X0,X1) = k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2290,axiom,
% 2.15/0.65      (![X3, X2] : ((~r1_xboole_0(X3,X2) | (k1_xboole_0 = k3_xboole_0(X2,X3)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2289,axiom,
% 2.15/0.65      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k3_xboole_0(X0,X1) = k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2288,axiom,
% 2.15/0.65      (![X1, X3, X0, X2] : ((~r1_xboole_0(X2,k3_xboole_0(X1,X0)) | ~r1_tarski(X3,X0) | (k1_xboole_0 = k3_xboole_0(X3,X2)) | ~r1_tarski(X2,X1))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2287,axiom,
% 2.15/0.65      (![X1, X3, X0, X2] : ((~r1_xboole_0(X2,k3_xboole_0(X1,X0)) | ~r1_tarski(X2,X0) | (k1_xboole_0 = k3_xboole_0(X2,X3)) | ~r1_tarski(X3,X1))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2286,axiom,
% 2.15/0.65      (![X5, X7, X4, X6] : ((~r1_xboole_0(X6,k3_xboole_0(X5,X7)) | ~r1_tarski(X4,X5) | (k1_xboole_0 = k3_xboole_0(X4,X6)) | ~r1_tarski(X6,X7))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2285,axiom,
% 2.15/0.65      (![X1, X3, X0, X2] : ((~r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X1) | (k1_xboole_0 = k3_xboole_0(X0,X3)) | ~r1_tarski(X3,X2))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2284,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(k3_xboole_0(sK1,X8),X9))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(k3_xboole_0(sK1,X8),X9)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2283,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(X8,k3_xboole_0(sK1,X9)))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(X8,k3_xboole_0(sK1,X9))),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2282,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(k3_xboole_0(sK1,X8),X9))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(k3_xboole_0(sK1,X8),X9)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2281,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(k3_xboole_0(X8,sK1),X9))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(k3_xboole_0(X8,sK1),X9)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2280,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X7),X8),k3_xboole_0(sK0,X9))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X7),X8),k3_xboole_0(sK0,X9)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2279,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(X8,k3_xboole_0(sK1,X9)))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(X8,k3_xboole_0(sK1,X9))),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2278,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(X8,k3_xboole_0(X9,sK1)))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X7),k3_xboole_0(X8,k3_xboole_0(X9,sK1))),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2277,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(sK1,X8)),k3_xboole_0(sK0,X9))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(sK1,X8)),k3_xboole_0(sK0,X9)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2276,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(k3_xboole_0(X8,sK1),X9))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(k3_xboole_0(X8,sK1),X9)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2275,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X7),X8),k3_xboole_0(X9,sK0))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X7),X8),k3_xboole_0(X9,sK0)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2274,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X7,sK1),X8),k3_xboole_0(sK0,X9))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X7,sK1),X8),k3_xboole_0(sK0,X9)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2273,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(X8,k3_xboole_0(X9,sK1)))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X7,sK0),k3_xboole_0(X8,k3_xboole_0(X9,sK1))),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2272,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(sK1,X8)),k3_xboole_0(X9,sK0))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(sK1,X8)),k3_xboole_0(X9,sK0)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2271,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,sK1)),k3_xboole_0(sK0,X9))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,sK1)),k3_xboole_0(sK0,X9)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2270,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X7,sK1),X8),k3_xboole_0(X9,sK0))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X7,sK1),X8),k3_xboole_0(X9,sK0)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2269,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X7, X8, X6] : ((~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,sK1)),k3_xboole_0(X9,sK0))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X7,k3_xboole_0(X8,sK1)),k3_xboole_0(X9,sK0)),X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2268,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(X0,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X1),X0)) | ~r1_tarski(X0,k3_xboole_0(sK1,X2))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2267,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(X3,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,sK0),X3)) | ~r1_tarski(X3,k3_xboole_0(sK1,X5))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2266,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(X0,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X1),X0)) | ~r1_tarski(X0,k3_xboole_0(X2,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2265,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(X3,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,sK0),X3)) | ~r1_tarski(X3,k3_xboole_0(X5,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2264,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(X0,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X2))) | ~r1_tarski(X0,k3_xboole_0(sK1,X1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2263,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(X3,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X5,sK0))) | ~r1_tarski(X3,k3_xboole_0(sK1,X4))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2262,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(X0,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X2))) | ~r1_tarski(X0,k3_xboole_0(X1,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2261,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(X3,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X5,sK0))) | ~r1_tarski(X3,k3_xboole_0(X4,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2260,axiom,
% 2.15/0.65      (![X9, X11, X8, X10] : ((~r1_xboole_0(k3_xboole_0(X10,X11),X9) | (k1_xboole_0 = k3_xboole_0(X8,X9)) | ~r1_tarski(X9,X11) | ~r1_tarski(X8,X10))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2259,axiom,
% 2.15/0.65      (![X5, X7, X4, X6] : ((~r1_xboole_0(k3_xboole_0(X6,X7),X5) | (k1_xboole_0 = k3_xboole_0(X4,X5)) | ~r1_tarski(X4,X7) | ~r1_tarski(X5,X6))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2258,axiom,
% 2.15/0.65      (![X9, X7, X8, X6] : ((~r1_xboole_0(k3_xboole_0(X9,X7),X6) | ~r1_tarski(X8,X9) | (k1_xboole_0 = k3_xboole_0(X6,X8)) | ~r1_tarski(X6,X7))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2257,axiom,
% 2.15/0.65      (![X5, X7, X4, X6] : ((~r1_xboole_0(k3_xboole_0(X6,X7),X4) | (k1_xboole_0 = k3_xboole_0(X4,X5)) | ~r1_tarski(X5,X7) | ~r1_tarski(X4,X6))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2256,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k3_xboole_0(sK0,X2),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X2))) | ~r1_tarski(X0,k3_xboole_0(X1,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2255,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k3_xboole_0(sK0,X2),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X2))) | ~r1_tarski(X0,k3_xboole_0(sK1,X1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2254,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1)) | ~r1_tarski(X1,k3_xboole_0(X2,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2253,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k3_xboole_0(sK0,X0),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1)) | ~r1_tarski(X1,k3_xboole_0(sK1,X2))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2252,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k3_xboole_0(X5,sK0),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X5,sK0))) | ~r1_tarski(X3,k3_xboole_0(X4,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2251,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k3_xboole_0(X5,sK0),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X5,sK0))) | ~r1_tarski(X3,k3_xboole_0(sK1,X4))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2250,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k3_xboole_0(X3,sK0),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4)) | ~r1_tarski(X4,k3_xboole_0(X5,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2249,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k3_xboole_0(X3,sK0),k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4)) | ~r1_tarski(X4,k3_xboole_0(sK1,X5))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2248,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X16, X13, X15, X12, X14] : ((~r1_xboole_0(k3_xboole_0(X13,X14),k1_xboole_0) | ~r1_tarski(X15,sK0) | (k1_xboole_0 = k3_xboole_0(X15,X16)) | ~r1_tarski(X16,k3_xboole_0(sK1,X12)) | ~r1_tarski(X15,X14) | ~r1_tarski(X16,X13)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2247,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X18, X20, X17, X19, X21] : ((~r1_xboole_0(k3_xboole_0(X18,X19),k1_xboole_0) | ~r1_tarski(X20,sK0) | (k1_xboole_0 = k3_xboole_0(X20,X21)) | ~r1_tarski(X21,k3_xboole_0(X17,sK1)) | ~r1_tarski(X20,X19) | ~r1_tarski(X21,X18)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2246,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X22, X25, X23, X24, X26] : ((~r1_xboole_0(k3_xboole_0(X23,X24),k1_xboole_0) | ~r1_tarski(X25,k3_xboole_0(sK1,X22)) | (k1_xboole_0 = k3_xboole_0(X25,X26)) | ~r1_tarski(X26,sK0) | ~r1_tarski(X25,X24) | ~r1_tarski(X26,X23)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2245,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X27, X29, X31, X28, X30] : ((~r1_xboole_0(k3_xboole_0(X28,X29),k1_xboole_0) | ~r1_tarski(X30,k3_xboole_0(X27,sK1)) | (k1_xboole_0 = k3_xboole_0(X30,X31)) | ~r1_tarski(X31,sK0) | ~r1_tarski(X30,X29) | ~r1_tarski(X31,X28)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2244,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2, X4] : ((~r1_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0) | ~r1_tarski(X2,sK0) | (k1_xboole_0 = k3_xboole_0(X2,X3)) | ~r1_tarski(X3,k3_xboole_0(sK1,X4)) | ~r1_tarski(X2,X1) | ~r1_tarski(X3,X0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2243,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2, X4] : ((~r1_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0) | ~r1_tarski(X2,sK0) | (k1_xboole_0 = k3_xboole_0(X2,X3)) | ~r1_tarski(X3,k3_xboole_0(X4,sK1)) | ~r1_tarski(X2,X1) | ~r1_tarski(X3,X0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2242,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2, X4] : ((~r1_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0) | ~r1_tarski(X2,k3_xboole_0(sK1,X3)) | (k1_xboole_0 = k3_xboole_0(X2,X4)) | ~r1_tarski(X4,sK0) | ~r1_tarski(X2,X1) | ~r1_tarski(X4,X0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2241,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2, X4] : ((~r1_xboole_0(k3_xboole_0(X1,X0),k1_xboole_0) | ~r1_tarski(X2,k3_xboole_0(X3,sK1)) | (k1_xboole_0 = k3_xboole_0(X2,X4)) | ~r1_tarski(X4,sK0) | ~r1_tarski(X2,X1) | ~r1_tarski(X4,X0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2240,axiom,
% 2.15/0.65      (![X16, X18, X15, X17, X19, X14] : ((~r1_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X15,X18)) | ~r1_tarski(X14,X15) | (k1_xboole_0 = k3_xboole_0(X19,X14)) | ~r1_tarski(X19,X18) | ~r1_tarski(X14,X17) | ~r1_tarski(X19,X16))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2239,axiom,
% 2.15/0.65      (![X9, X11, X13, X8, X10, X12] : ((~r1_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X9,X12)) | ~r1_tarski(X8,X9) | (k1_xboole_0 = k3_xboole_0(X13,X8)) | ~r1_tarski(X13,X12) | ~r1_tarski(X13,X11) | ~r1_tarski(X8,X10))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2238,axiom,
% 2.15/0.65      (![X16, X18, X15, X17, X19, X14] : ((~r1_xboole_0(k3_xboole_0(X16,X17),k3_xboole_0(X15,X18)) | ~r1_tarski(X14,X15) | (k1_xboole_0 = k3_xboole_0(X14,X19)) | ~r1_tarski(X19,X18) | ~r1_tarski(X19,X17) | ~r1_tarski(X14,X16))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2237,axiom,
% 2.15/0.65      (![X9, X11, X13, X8, X10, X12] : ((~r1_xboole_0(k3_xboole_0(X10,X11),k3_xboole_0(X9,X12)) | ~r1_tarski(X8,X9) | (k1_xboole_0 = k3_xboole_0(X8,X13)) | ~r1_tarski(X13,X12) | ~r1_tarski(X8,X11) | ~r1_tarski(X13,X10))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2236,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X0] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK1,sK2),X1)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2235,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X0] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(sK1,sK2))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2234,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X1),k3_xboole_0(sK0,X0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2233,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,sK2)),k3_xboole_0(sK0,X0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2232,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X3),k3_xboole_0(k3_xboole_0(sK1,X4),X5)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2231,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X3),k3_xboole_0(X4,k3_xboole_0(sK1,X5))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2230,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X3),k3_xboole_0(k3_xboole_0(X4,sK1),X5)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2229,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),X1),k3_xboole_0(sK0,X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2228,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X3)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X3),k3_xboole_0(X4,k3_xboole_0(X5,sK1))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2227,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK1,X1)),k3_xboole_0(sK0,X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2226,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),X1),k3_xboole_0(sK0,X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2225,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X2)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),k3_xboole_0(sK0,X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2224,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) | ~r1_tarski(X1,k3_xboole_0(sK1,X2)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2223,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X0)) | ~r1_tarski(X1,k3_xboole_0(X2,sK1)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2222,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1)) | ~r1_tarski(X0,k3_xboole_0(sK1,X2)) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X1)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2221,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(sK0,X1)) | ~r1_tarski(X0,k3_xboole_0(X2,sK1)) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X1)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2220,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,sK0),k3_xboole_0(k3_xboole_0(sK1,sK2),X3)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2219,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,sK0),k3_xboole_0(X3,k3_xboole_0(sK1,sK2))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2218,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X3),k3_xboole_0(X2,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2217,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK1,sK2)),k3_xboole_0(X2,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2216,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(k3_xboole_0(sK1,X4),X5)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2215,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(X4,k3_xboole_0(sK1,X5))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2214,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(k3_xboole_0(X4,sK1),X5)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2213,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),X1),k3_xboole_0(X2,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2212,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(X4,k3_xboole_0(X5,sK1))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2211,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK1,X1)),k3_xboole_0(X2,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2210,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X0,sK1),X1),k3_xboole_0(X2,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2209,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X2,sK0)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK1)),k3_xboole_0(X2,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2208,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0)) | ~r1_tarski(X4,k3_xboole_0(sK1,X5)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2207,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,sK0)) | ~r1_tarski(X4,k3_xboole_0(X5,sK1)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2206,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X4,sK0)) | ~r1_tarski(X3,k3_xboole_0(sK1,X5)) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2205,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X4,sK0)) | ~r1_tarski(X3,k3_xboole_0(X5,sK1)) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2204,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X9, X8] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X8,k3_xboole_0(sK1,sK2))) | ~r1_tarski(X9,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X8,k3_xboole_0(sK1,sK2)),X9))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2203,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X9, X8] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X8,k3_xboole_0(sK1,sK2))) | (k1_xboole_0 = k3_xboole_0(X9,k3_xboole_0(X8,k3_xboole_0(sK1,sK2)))) | ~r1_tarski(X9,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2202,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,k3_xboole_0(sK1,X4))) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK1,X4)),k3_xboole_0(X5,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2201,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,k3_xboole_0(sK1,X4))) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK1,X4)),k3_xboole_0(sK0,X5)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2200,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,k3_xboole_0(sK1,X2))) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(sK1,X2))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2199,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,k3_xboole_0(sK1,X2))) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(sK1,X2))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2198,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,k3_xboole_0(X4,sK1))) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X4,sK1)),k3_xboole_0(X5,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2197,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,k3_xboole_0(X4,sK1))) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(X4,sK1)),k3_xboole_0(sK0,X5)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2196,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,k3_xboole_0(X2,sK1))) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,k3_xboole_0(X2,sK1))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2195,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,k3_xboole_0(X2,sK1))) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,k3_xboole_0(X2,sK1))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2194,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) | (k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(X0,X1))) | ~r1_tarski(X2,sK0) | ~r1_tarski(X0,sK2) | ~r1_tarski(X1,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2193,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,X4)) | (k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(X3,X4))) | ~r1_tarski(X5,sK0) | ~r1_tarski(X4,sK2) | ~r1_tarski(X3,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2192,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X0,X1)) | ~r1_tarski(X2,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,X1),X2)) | ~r1_tarski(X0,sK2) | ~r1_tarski(X1,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2191,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X3,X4)) | ~r1_tarski(X5,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,X4),X5)) | ~r1_tarski(X4,sK2) | ~r1_tarski(X3,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2190,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X20, X22, X21, X23] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X21,X22)) | ~r1_tarski(X20,X21) | (k1_xboole_0 = k3_xboole_0(X20,X23)) | ~r1_tarski(X23,X22) | ~r1_tarski(X23,sK0) | ~r1_tarski(X20,k3_xboole_0(sK1,sK2))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2189,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X25, X27, X24, X26] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X25,X26)) | ~r1_tarski(X24,X25) | (k1_xboole_0 = k3_xboole_0(X24,X27)) | ~r1_tarski(X27,X26) | ~r1_tarski(X27,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X24,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2188,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X32, X29, X31, X28, X30] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X29,X30)) | ~r1_tarski(k3_xboole_0(sK0,X28),X29) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X28),k3_xboole_0(k3_xboole_0(sK1,X31),X32))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X31),X32),X30)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2187,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X34, X36, X33, X35, X37] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X34,X35)) | ~r1_tarski(k3_xboole_0(sK0,X33),X34) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X33),k3_xboole_0(k3_xboole_0(X36,sK1),X37))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X36,sK1),X37),X35)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2186,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X40, X42, X38, X41, X39] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X39,X40)) | ~r1_tarski(k3_xboole_0(sK0,X38),X39) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X38),k3_xboole_0(X41,k3_xboole_0(sK1,X42)))) | ~r1_tarski(k3_xboole_0(X41,k3_xboole_0(sK1,X42)),X40)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2185,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X44, X46, X43, X45, X47] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X44,X45)) | ~r1_tarski(k3_xboole_0(sK0,X43),X44) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X43),k3_xboole_0(X46,k3_xboole_0(X47,sK1)))) | ~r1_tarski(k3_xboole_0(X46,k3_xboole_0(X47,sK1)),X45)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2184,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X49, X51, X48, X50, X52] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X49,X50)) | ~r1_tarski(k3_xboole_0(X48,sK0),X49) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X48,sK0),k3_xboole_0(k3_xboole_0(sK1,X51),X52))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X51),X52),X50)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2183,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X53, X55, X56, X54, X57] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X54,X55)) | ~r1_tarski(k3_xboole_0(X53,sK0),X54) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X53,sK0),k3_xboole_0(k3_xboole_0(X56,sK1),X57))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X56,sK1),X57),X55)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2182,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X58, X60, X62, X59, X61] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X59,X60)) | ~r1_tarski(k3_xboole_0(X58,sK0),X59) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X58,sK0),k3_xboole_0(X61,k3_xboole_0(sK1,X62)))) | ~r1_tarski(k3_xboole_0(X61,k3_xboole_0(sK1,X62)),X60)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2181,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X63, X65, X67, X64, X66] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X64,X65)) | ~r1_tarski(k3_xboole_0(X63,sK0),X64) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X63,sK0),k3_xboole_0(X66,k3_xboole_0(X67,sK1)))) | ~r1_tarski(k3_xboole_0(X66,k3_xboole_0(X67,sK1)),X65)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2180,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X69, X71, X72, X68, X70] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X70,X71)) | ~r1_tarski(k3_xboole_0(X68,k3_xboole_0(sK1,X69)),X70) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X68,k3_xboole_0(sK1,X69)),k3_xboole_0(sK0,X72))) | ~r1_tarski(k3_xboole_0(sK0,X72),X71)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2179,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X73, X75, X77, X74, X76] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X75,X76)) | ~r1_tarski(k3_xboole_0(X73,k3_xboole_0(sK1,X74)),X75) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X73,k3_xboole_0(sK1,X74)),k3_xboole_0(X77,sK0))) | ~r1_tarski(k3_xboole_0(X77,sK0),X76)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2178,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X82, X79, X81, X78, X80] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X80,X81)) | ~r1_tarski(k3_xboole_0(X78,k3_xboole_0(X79,sK1)),X80) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X78,k3_xboole_0(X79,sK1)),k3_xboole_0(sK0,X82))) | ~r1_tarski(k3_xboole_0(sK0,X82),X81)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2177,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X84, X86, X83, X85, X87] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X85,X86)) | ~r1_tarski(k3_xboole_0(X83,k3_xboole_0(X84,sK1)),X85) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X83,k3_xboole_0(X84,sK1)),k3_xboole_0(X87,sK0))) | ~r1_tarski(k3_xboole_0(X87,sK0),X86)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2176,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X89, X91, X88, X90, X92] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X90,X91)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X88),X89),X90) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X88),X89),k3_xboole_0(sK0,X92))) | ~r1_tarski(k3_xboole_0(sK0,X92),X91)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2175,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X96, X93, X95, X97, X94] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X95,X96)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X93),X94),X95) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X93),X94),k3_xboole_0(X97,sK0))) | ~r1_tarski(k3_xboole_0(X97,sK0),X96)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2174,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X98, X100, X102, X99, X101] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X100,X101)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X98,sK1),X99),X100) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X98,sK1),X99),k3_xboole_0(sK0,X102))) | ~r1_tarski(k3_xboole_0(sK0,X102),X101)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2173,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X104, X106, X105, X107, X103] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X105,X106)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X103,sK1),X104),X105) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X103,sK1),X104),k3_xboole_0(X107,sK0))) | ~r1_tarski(k3_xboole_0(X107,sK0),X106)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2172,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X20, X22, X21, X23] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X21,X22)) | ~r1_tarski(X20,X21) | (k1_xboole_0 = k3_xboole_0(X23,X20)) | ~r1_tarski(X23,X22) | ~r1_tarski(X20,sK0) | ~r1_tarski(X23,k3_xboole_0(sK1,sK2))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2171,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X25, X27, X24, X26] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X25,X26)) | ~r1_tarski(X24,X25) | (k1_xboole_0 = k3_xboole_0(X27,X24)) | ~r1_tarski(X27,X26) | ~r1_tarski(X24,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X27,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2170,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X32, X29, X31, X28, X30] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X30,X31)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X28),X29),X30) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X32),k3_xboole_0(k3_xboole_0(sK1,X28),X29))) | ~r1_tarski(k3_xboole_0(sK0,X32),X31)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2169,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X34, X36, X33, X35, X37] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X35,X36)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X33,sK1),X34),X35) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X37),k3_xboole_0(k3_xboole_0(X33,sK1),X34))) | ~r1_tarski(k3_xboole_0(sK0,X37),X36)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2168,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X40, X42, X38, X41, X39] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X40,X41)) | ~r1_tarski(k3_xboole_0(X38,k3_xboole_0(sK1,X39)),X40) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X42),k3_xboole_0(X38,k3_xboole_0(sK1,X39)))) | ~r1_tarski(k3_xboole_0(sK0,X42),X41)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2167,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X44, X46, X43, X45, X47] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X45,X46)) | ~r1_tarski(k3_xboole_0(X43,k3_xboole_0(X44,sK1)),X45) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X47),k3_xboole_0(X43,k3_xboole_0(X44,sK1)))) | ~r1_tarski(k3_xboole_0(sK0,X47),X46)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2166,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X49, X51, X48, X50, X52] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X50,X51)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X48),X49),X50) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X52,sK0),k3_xboole_0(k3_xboole_0(sK1,X48),X49))) | ~r1_tarski(k3_xboole_0(X52,sK0),X51)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2165,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X53, X55, X56, X54, X57] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X55,X56)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X53,sK1),X54),X55) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X57,sK0),k3_xboole_0(k3_xboole_0(X53,sK1),X54))) | ~r1_tarski(k3_xboole_0(X57,sK0),X56)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2164,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X58, X60, X62, X59, X61] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X60,X61)) | ~r1_tarski(k3_xboole_0(X58,k3_xboole_0(sK1,X59)),X60) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X62,sK0),k3_xboole_0(X58,k3_xboole_0(sK1,X59)))) | ~r1_tarski(k3_xboole_0(X62,sK0),X61)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2163,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X63, X65, X67, X64, X66] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X65,X66)) | ~r1_tarski(k3_xboole_0(X63,k3_xboole_0(X64,sK1)),X65) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X67,sK0),k3_xboole_0(X63,k3_xboole_0(X64,sK1)))) | ~r1_tarski(k3_xboole_0(X67,sK0),X66)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2162,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X69, X71, X72, X68, X70] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X69,X70)) | ~r1_tarski(k3_xboole_0(sK0,X68),X69) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X71,k3_xboole_0(sK1,X72)),k3_xboole_0(sK0,X68))) | ~r1_tarski(k3_xboole_0(X71,k3_xboole_0(sK1,X72)),X70)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2161,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X73, X75, X77, X74, X76] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X74,X75)) | ~r1_tarski(k3_xboole_0(X73,sK0),X74) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X76,k3_xboole_0(sK1,X77)),k3_xboole_0(X73,sK0))) | ~r1_tarski(k3_xboole_0(X76,k3_xboole_0(sK1,X77)),X75)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2160,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X82, X79, X81, X78, X80] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X79,X80)) | ~r1_tarski(k3_xboole_0(sK0,X78),X79) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X81,k3_xboole_0(X82,sK1)),k3_xboole_0(sK0,X78))) | ~r1_tarski(k3_xboole_0(X81,k3_xboole_0(X82,sK1)),X80)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2159,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X84, X86, X83, X85, X87] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X84,X85)) | ~r1_tarski(k3_xboole_0(X83,sK0),X84) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X86,k3_xboole_0(X87,sK1)),k3_xboole_0(X83,sK0))) | ~r1_tarski(k3_xboole_0(X86,k3_xboole_0(X87,sK1)),X85)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2158,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X89, X91, X88, X90, X92] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X89,X90)) | ~r1_tarski(k3_xboole_0(sK0,X88),X89) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X91),X92),k3_xboole_0(sK0,X88))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X91),X92),X90)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2157,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X96, X93, X95, X97, X94] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X94,X95)) | ~r1_tarski(k3_xboole_0(X93,sK0),X94) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X96),X97),k3_xboole_0(X93,sK0))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(sK1,X96),X97),X95)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2156,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X98, X100, X102, X99, X101] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X99,X100)) | ~r1_tarski(k3_xboole_0(sK0,X98),X99) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X101,sK1),X102),k3_xboole_0(sK0,X98))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X101,sK1),X102),X100)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2155,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X104, X106, X105, X107, X103] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X104,X105)) | ~r1_tarski(k3_xboole_0(X103,sK0),X104) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X106,sK1),X107),k3_xboole_0(X103,sK0))) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X106,sK1),X107),X105)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2154,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X16, X13, X15, X12, X14] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X13,X14)) | ~r1_tarski(X15,X13) | (k1_xboole_0 = k3_xboole_0(X15,X16)) | ~r1_tarski(X16,X14) | ~r1_tarski(X15,k3_xboole_0(sK1,X12)) | ~r1_tarski(X16,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2153,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X18, X20, X17, X19, X21] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X18,X19)) | ~r1_tarski(X20,X18) | (k1_xboole_0 = k3_xboole_0(X20,X21)) | ~r1_tarski(X21,X19) | ~r1_tarski(X20,k3_xboole_0(X17,sK1)) | ~r1_tarski(X21,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2152,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X22, X25, X23, X24, X26] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X23,X24)) | ~r1_tarski(X25,X23) | (k1_xboole_0 = k3_xboole_0(X25,X26)) | ~r1_tarski(X26,X24) | ~r1_tarski(X25,sK0) | ~r1_tarski(X26,k3_xboole_0(sK1,X22))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2151,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X27, X29, X31, X28, X30] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X28,X29)) | ~r1_tarski(X30,X28) | (k1_xboole_0 = k3_xboole_0(X30,X31)) | ~r1_tarski(X31,X29) | ~r1_tarski(X30,sK0) | ~r1_tarski(X31,k3_xboole_0(X27,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2150,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) | ~r1_tarski(X2,X0) | (k1_xboole_0 = k3_xboole_0(X2,X3)) | ~r1_tarski(X3,X1) | ~r1_tarski(X2,k3_xboole_0(sK1,X4)) | ~r1_tarski(X3,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2149,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) | ~r1_tarski(X2,X0) | (k1_xboole_0 = k3_xboole_0(X2,X3)) | ~r1_tarski(X3,X1) | ~r1_tarski(X2,k3_xboole_0(X4,sK1)) | ~r1_tarski(X3,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2148,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) | ~r1_tarski(X2,X0) | (k1_xboole_0 = k3_xboole_0(X2,X3)) | ~r1_tarski(X3,X1) | ~r1_tarski(X2,sK0) | ~r1_tarski(X3,k3_xboole_0(sK1,X4))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2147,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(X1,X0)) | ~r1_tarski(X2,X0) | (k1_xboole_0 = k3_xboole_0(X2,X3)) | ~r1_tarski(X3,X1) | ~r1_tarski(X2,sK0) | ~r1_tarski(X3,k3_xboole_0(X4,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2146,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X7, X6] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),X6)) | ~r1_tarski(X7,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X6),X7))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2145,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X7, X6] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,sK2),X6)) | (k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(sK1,sK2),X6))) | ~r1_tarski(X7,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2144,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X3),X4)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X3),X4),k3_xboole_0(X5,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2143,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X3),X4)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X3),X4),k3_xboole_0(sK0,X5)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2142,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X1),X2)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(sK1,X1),X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2141,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(sK1,X1),X2)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(sK1,X1),X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2140,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X3,sK1),X4)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,sK1),X4),k3_xboole_0(X5,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2139,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X3,sK1),X4)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,sK1),X4),k3_xboole_0(sK0,X5)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2138,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,sK1),X2)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(k3_xboole_0(X1,sK1),X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2137,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,sK1),X2)) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(k3_xboole_0(X1,sK1),X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2136,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,X0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X1))) | ~r1_tarski(X0,k3_xboole_0(sK1,X2))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2135,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,X3) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,sK0))) | ~r1_tarski(X3,k3_xboole_0(sK1,X5))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2134,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,X0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(sK0,X1))) | ~r1_tarski(X0,k3_xboole_0(X2,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2133,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,X3) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,sK0))) | ~r1_tarski(X3,k3_xboole_0(X5,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2132,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,X1) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1)) | ~r1_tarski(X1,k3_xboole_0(sK1,X2))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2131,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,X4) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4)) | ~r1_tarski(X4,k3_xboole_0(sK1,X5))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2130,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_xboole_0(k1_xboole_0,X1) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK0,X0),X1)) | ~r1_tarski(X1,k3_xboole_0(X2,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2129,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_xboole_0(k1_xboole_0,X4) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),X4)) | ~r1_tarski(X4,k3_xboole_0(X5,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2128,negated_conjecture,
% 2.15/0.65      ((~~r1_xboole_0(k1_xboole_0,k1_xboole_0)) | ~r1_xboole_0(k1_xboole_0,k1_xboole_0))).
% 2.15/0.65  
% 2.15/0.65  tff(u2127,negated_conjecture,
% 2.15/0.65      ((~~r1_xboole_0(sK0,sK1)) | ~r1_xboole_0(sK0,sK1))).
% 2.15/0.65  
% 2.15/0.65  tff(u2126,negated_conjecture,
% 2.15/0.65      ((~~r1_xboole_0(sK2,sK2)) | ~r1_xboole_0(sK2,sK2))).
% 2.15/0.65  
% 2.15/0.65  tff(u2125,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X21] : (r1_xboole_0(k3_xboole_0(sK1,X21),sK0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2124,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X0] : (r1_xboole_0(k3_xboole_0(X0,sK1),sK0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2123,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X13] : (r1_xboole_0(sK0,k3_xboole_0(sK1,X13)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2122,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X0] : (r1_xboole_0(sK0,k3_xboole_0(X0,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2121,axiom,
% 2.15/0.65      (![X1, X0, X2] : ((~r1_tarski(X0,X2) | ~r1_xboole_0(X1,X2) | (k1_xboole_0 = X0) | ~r1_tarski(X0,X1))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2120,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X2, X4] : ((~r1_tarski(X3,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X2,sK0) | ~r1_xboole_0(X4,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X3,X2)) | ~r1_tarski(k3_xboole_0(X3,X2),X4)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2119,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X3, X2] : ((~r1_tarski(X1,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X2,sK0) | ~r1_xboole_0(X3,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X2,X1)) | ~r1_tarski(k3_xboole_0(X2,X1),X3)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2118,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X13, X12] : ((~r1_tarski(X12,k3_xboole_0(sK1,sK2)) | ~r1_xboole_0(k1_xboole_0,X13) | ~r1_tarski(X13,sK0) | (k1_xboole_0 = k3_xboole_0(X12,X13))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2117,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X9, X8] : ((~r1_tarski(X8,k3_xboole_0(sK1,sK2)) | ~r1_xboole_0(k1_xboole_0,X8) | ~r1_tarski(X9,sK0) | (k1_xboole_0 = k3_xboole_0(X8,X9))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2116,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X15, X14] : ((~r1_tarski(X15,k3_xboole_0(sK1,sK2)) | ~r1_xboole_0(k1_xboole_0,X15) | (k1_xboole_0 = k3_xboole_0(X14,X15)) | ~r1_tarski(X14,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2115,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X11, X10] : ((~r1_tarski(X11,k3_xboole_0(sK1,sK2)) | ~r1_xboole_0(k1_xboole_0,X10) | (k1_xboole_0 = k3_xboole_0(X10,X11)) | ~r1_tarski(X10,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2114,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_tarski(X3,k3_xboole_0(sK1,X4)) | r1_tarski(k3_xboole_0(X3,k3_xboole_0(X5,sK0)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2113,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_tarski(X0,k3_xboole_0(sK1,X1)) | r1_tarski(k3_xboole_0(X0,k3_xboole_0(sK0,X2)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2112,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X3, X5, X4] : ((~r1_tarski(X3,k3_xboole_0(sK1,X4)) | r1_tarski(k3_xboole_0(k3_xboole_0(X5,sK0),X3),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2111,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_tarski(X0,k3_xboole_0(sK1,X1)) | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X2),X0),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2110,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_tarski(X1,k3_xboole_0(X0,sK1)) | r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,sK0)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2109,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_tarski(X1,k3_xboole_0(X0,sK1)) | r1_tarski(k3_xboole_0(X1,k3_xboole_0(sK0,X2)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2108,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_tarski(X1,k3_xboole_0(X0,sK1)) | r1_tarski(k3_xboole_0(k3_xboole_0(X2,sK0),X1),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2107,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : ((~r1_tarski(X1,k3_xboole_0(X0,sK1)) | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X2),X1),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2106,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X7, X6] : ((~r1_tarski(X6,sK0) | (k1_xboole_0 = k3_xboole_0(X6,k3_xboole_0(k3_xboole_0(sK1,sK2),X7))) | ~r1_xboole_0(k1_xboole_0,X6)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2105,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X9, X8] : ((~r1_tarski(X8,sK0) | (k1_xboole_0 = k3_xboole_0(X8,k3_xboole_0(X9,k3_xboole_0(sK1,sK2)))) | ~r1_xboole_0(k1_xboole_0,X8)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2104,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X7, X6] : ((~r1_tarski(X6,sK0) | ~r1_xboole_0(k1_xboole_0,X6) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X7),X6))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2103,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X9, X8] : ((~r1_tarski(X8,sK0) | ~r1_xboole_0(k1_xboole_0,X8) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X9,k3_xboole_0(sK1,sK2)),X8))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2102,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X18, X17, X19] : ((~r1_tarski(X18,sK0) | ~r1_tarski(X19,k3_xboole_0(sK1,X17)) | r1_tarski(k3_xboole_0(X18,X19),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2101,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X29, X31, X30] : ((~r1_tarski(X31,sK0) | ~r1_tarski(X30,k3_xboole_0(sK1,X29)) | r1_tarski(k3_xboole_0(X30,X31),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2100,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X40, X38, X39] : ((~r1_tarski(X39,sK0) | (k1_xboole_0 = k3_xboole_0(X39,X40)) | ~r1_tarski(X40,k3_xboole_0(sK1,X38)) | ~r1_xboole_0(k1_xboole_0,X39)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2099,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X46, X45, X47] : ((~r1_tarski(X47,sK0) | ~r1_xboole_0(k1_xboole_0,X46) | (k1_xboole_0 = k3_xboole_0(X46,X47)) | ~r1_tarski(X46,k3_xboole_0(sK1,X45))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2098,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X18, X17, X19] : ((~r1_tarski(X18,sK0) | ~r1_tarski(X19,k3_xboole_0(X17,sK1)) | r1_tarski(k3_xboole_0(X18,X19),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2097,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X29, X31, X30] : ((~r1_tarski(X31,sK0) | ~r1_tarski(X30,k3_xboole_0(X29,sK1)) | r1_tarski(k3_xboole_0(X30,X31),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2096,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X40, X38, X39] : ((~r1_tarski(X39,sK0) | (k1_xboole_0 = k3_xboole_0(X39,X40)) | ~r1_tarski(X40,k3_xboole_0(X38,sK1)) | ~r1_xboole_0(k1_xboole_0,X39)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2095,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X46, X45, X47] : ((~r1_tarski(X47,sK0) | ~r1_xboole_0(k1_xboole_0,X46) | (k1_xboole_0 = k3_xboole_0(X46,X47)) | ~r1_tarski(X46,k3_xboole_0(X45,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2094,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X8, X10] : ((~r1_tarski(X9,sK0) | (k1_xboole_0 = k3_xboole_0(X10,X9)) | ~r1_tarski(X10,k3_xboole_0(sK1,X8)) | ~r1_xboole_0(k1_xboole_0,X9)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2093,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X11, X13, X12] : ((~r1_tarski(X12,sK0) | (k1_xboole_0 = k3_xboole_0(X13,X12)) | ~r1_tarski(X13,k3_xboole_0(X11,sK1)) | ~r1_xboole_0(k1_xboole_0,X12)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2092,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X16, X15, X14] : ((~r1_tarski(X16,sK0) | (k1_xboole_0 = k3_xboole_0(X16,X15)) | ~r1_xboole_0(k1_xboole_0,X15) | ~r1_tarski(X15,k3_xboole_0(sK1,X14))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2091,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X18, X17, X19] : ((~r1_tarski(X19,sK0) | (k1_xboole_0 = k3_xboole_0(X19,X18)) | ~r1_xboole_0(k1_xboole_0,X18) | ~r1_tarski(X18,k3_xboole_0(X17,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2090,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X2, X4] : ((~r1_tarski(X2,sK0) | (k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(sK2,X3),k3_xboole_0(sK1,X4)))) | ~r1_xboole_0(k1_xboole_0,X2)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2089,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X5, X7, X6] : ((~r1_tarski(X5,sK0) | (k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X6,sK2),k3_xboole_0(sK1,X7)))) | ~r1_xboole_0(k1_xboole_0,X5)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2088,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X2, X4] : ((~r1_tarski(X2,sK0) | (k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(k3_xboole_0(sK2,X3),k3_xboole_0(X4,sK1)))) | ~r1_xboole_0(k1_xboole_0,X2)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2087,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X5, X7, X6] : ((~r1_tarski(X5,sK0) | (k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(k3_xboole_0(X6,sK2),k3_xboole_0(X7,sK1)))) | ~r1_xboole_0(k1_xboole_0,X5)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2086,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X0, X2] : ((~r1_tarski(X0,sK0) | ~r1_xboole_0(k1_xboole_0,X0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(sK2,X2))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2085,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X5, X4] : ((~r1_tarski(X3,sK0) | ~r1_xboole_0(k1_xboole_0,X3) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,sK1),k3_xboole_0(sK2,X5))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2084,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X0, X2] : ((~r1_tarski(X0,sK0) | ~r1_xboole_0(k1_xboole_0,X0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,sK2))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2083,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X5, X4] : ((~r1_tarski(X3,sK0) | ~r1_xboole_0(k1_xboole_0,X3) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(X4,sK1),k3_xboole_0(X5,sK2))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2082,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X2, X4] : ((~r1_tarski(X4,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,X2),k3_xboole_0(sK1,X3)),X4)) | ~r1_xboole_0(k1_xboole_0,X4)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2081,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X5, X7, X6] : ((~r1_tarski(X7,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X5,sK2),k3_xboole_0(sK1,X6)),X7)) | ~r1_xboole_0(k1_xboole_0,X7)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2080,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X2, X4] : ((~r1_tarski(X4,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK2,X2),k3_xboole_0(X3,sK1)),X4)) | ~r1_xboole_0(k1_xboole_0,X4)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2079,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X5, X7, X6] : ((~r1_tarski(X7,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X5,sK2),k3_xboole_0(X6,sK1)),X7)) | ~r1_xboole_0(k1_xboole_0,X7)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2078,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0, X2] : ((~r1_tarski(X2,sK0) | ~r1_xboole_0(k1_xboole_0,X2) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(sK2,X1)),X2))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2077,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X5, X4] : ((~r1_tarski(X5,sK0) | ~r1_xboole_0(k1_xboole_0,X5) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,sK1),k3_xboole_0(sK2,X4)),X5))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2076,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0, X2] : ((~r1_tarski(X2,sK0) | ~r1_xboole_0(k1_xboole_0,X2) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X0),k3_xboole_0(X1,sK2)),X2))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2075,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X5, X4] : ((~r1_tarski(X5,sK0) | ~r1_xboole_0(k1_xboole_0,X5) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(X3,sK1),k3_xboole_0(X4,sK2)),X5))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2074,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X9, X8, X10] : ((~r1_tarski(X8,sK0) | ~r1_xboole_0(X9,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X8,k3_xboole_0(k3_xboole_0(sK1,sK2),X10))) | ~r1_tarski(k3_xboole_0(X8,k3_xboole_0(k3_xboole_0(sK1,sK2),X10)),X9)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2073,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X11, X13, X12] : ((~r1_tarski(X11,sK0) | ~r1_xboole_0(X12,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X11,k3_xboole_0(X13,k3_xboole_0(sK1,sK2)))) | ~r1_tarski(k3_xboole_0(X11,k3_xboole_0(X13,k3_xboole_0(sK1,sK2))),X12)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2072,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X9, X8, X10] : ((~r1_tarski(X8,sK0) | ~r1_xboole_0(X9,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X10),X8)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,sK2),X10),X8),X9)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2071,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X11, X13, X12] : ((~r1_tarski(X11,sK0) | ~r1_xboole_0(X12,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X13,k3_xboole_0(sK1,sK2)),X11)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X13,k3_xboole_0(sK1,sK2)),X11),X12)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2070,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X8, X10] : ((~r1_tarski(X9,sK0) | ~r1_xboole_0(X9,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X9,X10)) | ~r1_tarski(X10,k3_xboole_0(sK1,X8))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2069,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X11, X13, X12] : ((~r1_tarski(X12,sK0) | ~r1_xboole_0(X12,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X12,X13)) | ~r1_tarski(X13,k3_xboole_0(X11,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2068,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X16, X15, X14] : ((~r1_tarski(X16,sK0) | ~r1_tarski(X15,k3_xboole_0(sK1,X14)) | (k1_xboole_0 = k3_xboole_0(X15,X16)) | ~r1_xboole_0(X15,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2067,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X18, X17, X19] : ((~r1_tarski(X19,sK0) | ~r1_tarski(X18,k3_xboole_0(X17,sK1)) | (k1_xboole_0 = k3_xboole_0(X18,X19)) | ~r1_xboole_0(X18,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2066,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X8, X10] : ((~r1_tarski(X10,sK0) | ~r1_xboole_0(X9,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X10,X9)) | ~r1_tarski(X9,k3_xboole_0(sK1,X8))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2065,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X11, X13, X12] : ((~r1_tarski(X13,sK0) | ~r1_xboole_0(X12,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X13,X12)) | ~r1_tarski(X12,k3_xboole_0(X11,sK1))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2064,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X16, X15, X14] : ((~r1_tarski(X15,sK0) | ~r1_tarski(X16,k3_xboole_0(sK1,X14)) | (k1_xboole_0 = k3_xboole_0(X16,X15)) | ~r1_xboole_0(X15,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2063,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X18, X17, X19] : ((~r1_tarski(X18,sK0) | ~r1_tarski(X19,k3_xboole_0(X17,sK1)) | (k1_xboole_0 = k3_xboole_0(X19,X18)) | ~r1_xboole_0(X18,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2062,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X3, X0, X2] : ((~r1_tarski(X3,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),X3)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),X3),X0) | ~r1_tarski(X1,sK2) | ~r1_xboole_0(X0,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2061,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X5, X7, X4, X6] : ((~r1_tarski(X7,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X5,k3_xboole_0(X6,sK1)),X7)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X5,k3_xboole_0(X6,sK1)),X7),X4) | ~r1_tarski(X5,sK2) | ~r1_xboole_0(X4,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2060,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0, X2] : ((~r1_tarski(X2,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,sK0),X2)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK0),X2),X0) | ~r1_xboole_0(X0,k1_xboole_0) | ~r1_tarski(X1,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2059,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X5, X4, X6] : ((~r1_tarski(X6,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(sK2,X5)),X6)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(sK2,X5)),X6),X3) | ~r1_xboole_0(X3,k1_xboole_0) | ~r1_tarski(X4,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2058,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X9, X7, X8, X10] : ((~r1_tarski(X10,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X8,k3_xboole_0(X9,sK2)),X10)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X8,k3_xboole_0(X9,sK2)),X10),X7) | ~r1_xboole_0(X7,k1_xboole_0) | ~r1_tarski(X8,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2057,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X5, X4, X6] : ((~r1_tarski(X3,sK0) | ~r1_tarski(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(sK2,X4),k3_xboole_0(sK1,X5))),X6) | ~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(sK2,X4),k3_xboole_0(sK1,X5))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2056,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X9, X7, X8, X10] : ((~r1_tarski(X7,sK0) | ~r1_tarski(k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(X8,sK2),k3_xboole_0(sK1,X9))),X10) | ~r1_xboole_0(X10,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(X8,sK2),k3_xboole_0(sK1,X9))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2055,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X5, X4, X6] : ((~r1_tarski(X3,sK0) | ~r1_tarski(k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(sK2,X4),k3_xboole_0(X5,sK1))),X6) | ~r1_xboole_0(X6,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(k3_xboole_0(sK2,X4),k3_xboole_0(X5,sK1))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2054,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X9, X7, X8, X10] : ((~r1_tarski(X7,sK0) | ~r1_tarski(k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(X8,sK2),k3_xboole_0(X9,sK1))),X10) | ~r1_xboole_0(X10,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X7,k3_xboole_0(k3_xboole_0(X8,sK2),k3_xboole_0(X9,sK1))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2053,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X3, X0, X2] : ((~r1_tarski(X0,sK0) | ~r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(sK2,X2))),X3) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(sK2,X2)))) | ~r1_xboole_0(X3,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2052,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X5, X7, X4, X6] : ((~r1_tarski(X4,sK0) | ~r1_tarski(k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X5,sK1),k3_xboole_0(sK2,X6))),X7) | (k1_xboole_0 = k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X5,sK1),k3_xboole_0(sK2,X6)))) | ~r1_xboole_0(X7,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2051,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X3, X0, X2] : ((~r1_tarski(X0,sK0) | ~r1_tarski(k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,sK2))),X3) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(k3_xboole_0(sK1,X1),k3_xboole_0(X2,sK2)))) | ~r1_xboole_0(X3,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2050,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X5, X7, X4, X6] : ((~r1_tarski(X4,sK0) | ~r1_tarski(k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X5,sK1),k3_xboole_0(X6,sK2))),X7) | (k1_xboole_0 = k3_xboole_0(X4,k3_xboole_0(k3_xboole_0(X5,sK1),k3_xboole_0(X6,sK2)))) | ~r1_xboole_0(X7,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2049,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X0, X2] : ((~r1_tarski(X2,sK1) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X1,X2))) | ~r1_tarski(X0,sK0) | ~r1_tarski(X1,sK2) | ~r1_xboole_0(k1_xboole_0,X0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2048,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0, X2] : ((~r1_tarski(X2,sK1) | ~r1_tarski(X0,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,X2),X0)) | ~r1_tarski(X1,sK2) | ~r1_xboole_0(k1_xboole_0,X0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2047,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X0] : ((~r1_tarski(X0,sK1) | (k1_xboole_0 = k3_xboole_0(sK0,X0))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2046,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2] : ((~r1_tarski(X2,sK1) | ~r1_tarski(X1,X3) | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X0),k3_xboole_0(X1,X2)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2045,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X5, X7, X4, X6] : ((~r1_tarski(X5,sK1) | ~r1_tarski(X6,X7) | r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X4),k3_xboole_0(X5,X6)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2044,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2] : ((~r1_tarski(X2,sK1) | ~r1_tarski(X1,X3) | r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(X1,X2)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2043,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X5, X7, X4, X6] : ((~r1_tarski(X5,sK1) | ~r1_tarski(X6,X7) | r1_tarski(k3_xboole_0(k3_xboole_0(X4,sK0),k3_xboole_0(X5,X6)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2042,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2] : ((~r1_tarski(X1,sK1) | ~r1_tarski(X0,X3) | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(sK0,X2)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2041,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X5, X7, X4, X6] : ((~r1_tarski(X4,sK1) | ~r1_tarski(X5,X7) | r1_tarski(k3_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(sK0,X6)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2040,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X3, X0, X2] : ((~r1_tarski(X1,sK1) | ~r1_tarski(X0,X3) | r1_tarski(k3_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,sK0)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2039,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X5, X7, X4, X6] : ((~r1_tarski(X4,sK1) | ~r1_tarski(X5,X7) | r1_tarski(k3_xboole_0(k3_xboole_0(X4,X5),k3_xboole_0(X6,sK0)),k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2038,negated_conjecture,
% 2.15/0.65      ((~(![X2] : ((~r1_tarski(X2,sK1) | (k1_xboole_0 = k3_xboole_0(X2,sK0)))))) | (![X2] : ((~r1_tarski(X2,sK1) | (k1_xboole_0 = k3_xboole_0(X2,sK0))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2037,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X0] : ((~r1_tarski(X1,sK1) | ~r1_tarski(X0,sK0) | ~r1_xboole_0(k1_xboole_0,X0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X1,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2036,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X2, X4] : ((~r1_tarski(X3,sK1) | ~r1_tarski(X2,sK0) | ~r1_xboole_0(k1_xboole_0,X2) | (k1_xboole_0 = k3_xboole_0(X2,k3_xboole_0(X3,k3_xboole_0(sK2,X4))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2035,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X5, X7, X6] : ((~r1_tarski(X6,sK1) | ~r1_tarski(X5,sK0) | ~r1_xboole_0(k1_xboole_0,X5) | (k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(X6,k3_xboole_0(X7,sK2))))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2034,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0] : ((~r1_tarski(X1,sK1) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,sK0),X0)) | ~r1_xboole_0(k1_xboole_0,X0) | ~r1_tarski(X0,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2033,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X2, X4] : ((~r1_tarski(X3,sK1) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,k3_xboole_0(sK2,X4)),X2)) | ~r1_xboole_0(k1_xboole_0,X2) | ~r1_tarski(X2,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2032,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X5, X7, X6] : ((~r1_tarski(X6,sK1) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,k3_xboole_0(X7,sK2)),X5)) | ~r1_xboole_0(k1_xboole_0,X5) | ~r1_tarski(X5,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2031,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X3, X0, X2] : ((~r1_tarski(X3,sK1) | ~r1_xboole_0(X1,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X2,X3))) | ~r1_tarski(k3_xboole_0(X0,k3_xboole_0(X2,X3)),X1) | ~r1_tarski(X2,sK2) | ~r1_tarski(X0,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2030,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X3, X0, X2] : ((~r1_tarski(X3,sK1) | ~r1_xboole_0(X1,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X2,X3),X0)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X2,X3),X0),X1) | ~r1_tarski(X2,sK2) | ~r1_tarski(X0,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2029,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X0, X2] : ((~r1_tarski(X2,sK1) | (k1_xboole_0 = k3_xboole_0(X1,k3_xboole_0(X2,sK0))) | ~r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,sK0)),X0) | ~r1_tarski(X1,sK0) | ~r1_xboole_0(X0,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2028,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X5, X4, X6] : ((~r1_tarski(X5,sK1) | (k1_xboole_0 = k3_xboole_0(X4,k3_xboole_0(X5,k3_xboole_0(sK2,X6)))) | ~r1_tarski(k3_xboole_0(X4,k3_xboole_0(X5,k3_xboole_0(sK2,X6))),X3) | ~r1_tarski(X4,sK0) | ~r1_xboole_0(X3,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2027,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X9, X7, X8, X10] : ((~r1_tarski(X9,sK1) | (k1_xboole_0 = k3_xboole_0(X8,k3_xboole_0(X9,k3_xboole_0(X10,sK2)))) | ~r1_tarski(k3_xboole_0(X8,k3_xboole_0(X9,k3_xboole_0(X10,sK2))),X7) | ~r1_tarski(X8,sK0) | ~r1_xboole_0(X7,k1_xboole_0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2026,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0, X2] : ((~r1_tarski(X0,sK1) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,X1)),X2) | ~r1_xboole_0(X2,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,sK0),k3_xboole_0(sK0,X1)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2025,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X5, X4] : ((~r1_tarski(X3,sK1) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(X4,sK0)),X5) | ~r1_xboole_0(X5,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X3,sK0),k3_xboole_0(X4,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2024,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X3, X0, X2] : ((~r1_tarski(X0,sK1) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k3_xboole_0(sK0,X2)),X3) | ~r1_xboole_0(X3,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(sK2,X1)),k3_xboole_0(sK0,X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2023,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X5, X7, X4, X6] : ((~r1_tarski(X4,sK1) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(sK2,X5)),k3_xboole_0(X6,sK0)),X7) | ~r1_xboole_0(X7,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(sK2,X5)),k3_xboole_0(X6,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2022,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X3, X0, X2] : ((~r1_tarski(X0,sK1) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK2)),k3_xboole_0(sK0,X2)),X3) | ~r1_xboole_0(X3,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X0,k3_xboole_0(X1,sK2)),k3_xboole_0(sK0,X2)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2021,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X5, X7, X4, X6] : ((~r1_tarski(X4,sK1) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X5,sK2)),k3_xboole_0(X6,sK0)),X7) | ~r1_xboole_0(X7,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X5,sK2)),k3_xboole_0(X6,sK0)))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2020,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X5, X4] : ((~r1_tarski(X5,sK2) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,X5))) | ~r1_tarski(X3,sK0) | ~r1_xboole_0(k1_xboole_0,X3) | ~r1_tarski(X4,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2019,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X5, X4] : ((~r1_tarski(X5,sK2) | ~r1_tarski(X3,sK0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,X5),X3)) | ~r1_xboole_0(k1_xboole_0,X3) | ~r1_tarski(X4,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2018,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X0, X2] : ((~r1_tarski(X1,sK2) | ~r1_tarski(X0,sK0) | (k1_xboole_0 = k3_xboole_0(X0,k3_xboole_0(X1,k3_xboole_0(sK1,X2)))) | ~r1_xboole_0(k1_xboole_0,X0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2017,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X5, X4] : ((~r1_tarski(X4,sK2) | ~r1_tarski(X3,sK0) | (k1_xboole_0 = k3_xboole_0(X3,k3_xboole_0(X4,k3_xboole_0(X5,sK1)))) | ~r1_xboole_0(k1_xboole_0,X3)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2016,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0, X2] : ((~r1_tarski(X1,sK2) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),X0)) | ~r1_tarski(X0,sK0) | ~r1_xboole_0(k1_xboole_0,X0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2015,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X5, X4] : ((~r1_tarski(X4,sK2) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X4,k3_xboole_0(X5,sK1)),X3)) | ~r1_tarski(X3,sK0) | ~r1_xboole_0(k1_xboole_0,X3)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2014,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X5, X7, X4, X6] : ((~r1_tarski(X7,sK2) | ~r1_xboole_0(X5,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(X4,k3_xboole_0(X6,X7))) | ~r1_tarski(k3_xboole_0(X4,k3_xboole_0(X6,X7)),X5) | ~r1_tarski(X4,sK0) | ~r1_tarski(X6,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2013,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X5, X7, X4, X6] : ((~r1_tarski(X7,sK2) | ~r1_xboole_0(X5,k1_xboole_0) | (k1_xboole_0 = k3_xboole_0(k3_xboole_0(X6,X7),X4)) | ~r1_tarski(k3_xboole_0(k3_xboole_0(X6,X7),X4),X5) | ~r1_tarski(X4,sK0) | ~r1_tarski(X6,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2012,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X1, X3, X0, X2] : ((~r1_tarski(X2,sK2) | (k1_xboole_0 = k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(sK1,X3)))) | ~r1_tarski(k3_xboole_0(X1,k3_xboole_0(X2,k3_xboole_0(sK1,X3))),X0) | ~r1_xboole_0(X0,k1_xboole_0) | ~r1_tarski(X1,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2011,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X5, X7, X4, X6] : ((~r1_tarski(X6,sK2) | (k1_xboole_0 = k3_xboole_0(X5,k3_xboole_0(X6,k3_xboole_0(X7,sK1)))) | ~r1_tarski(k3_xboole_0(X5,k3_xboole_0(X6,k3_xboole_0(X7,sK1))),X4) | ~r1_xboole_0(X4,k1_xboole_0) | ~r1_tarski(X5,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2010,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X11, X10] : ((~r1_tarski(k3_xboole_0(sK1,sK2),X10) | ~r1_tarski(sK0,X11) | r1_tarski(k1_xboole_0,k3_xboole_0(X10,X11))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2009,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X9, X8] : ((~r1_tarski(k3_xboole_0(sK1,sK2),X9) | r1_tarski(k1_xboole_0,k3_xboole_0(X8,X9)) | ~r1_tarski(sK0,X8)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2008,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(k3_xboole_0(sK1,sK2),sK0)) | ~r1_tarski(k3_xboole_0(sK1,sK2),sK0))).
% 2.15/0.65  
% 2.15/0.65  tff(u2007,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))) | ~r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)))).
% 2.15/0.65  
% 2.15/0.65  tff(u2006,axiom,
% 2.15/0.65      (![X11, X13, X10, X12, X14] : ((~r1_tarski(k3_xboole_0(X10,X12),X14) | ~r1_tarski(X12,X13) | ~r1_xboole_0(X14,k3_xboole_0(X13,X11)) | (k1_xboole_0 = k3_xboole_0(X10,X12)) | ~r1_tarski(X10,X11))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2005,axiom,
% 2.15/0.65      (![X1, X3, X0, X2, X4] : ((~r1_tarski(k3_xboole_0(X2,X0),X4) | ~r1_tarski(X2,X3) | ~r1_xboole_0(X4,k3_xboole_0(X3,X1)) | (k1_xboole_0 = k3_xboole_0(X2,X0)) | ~r1_tarski(X0,X1))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2004,axiom,
% 2.15/0.65      (![X5, X4, X6] : ((~r1_tarski(k3_xboole_0(X6,X5),X4) | (k1_xboole_0 = k3_xboole_0(X6,X5)) | ~r1_xboole_0(X4,X5))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2003,axiom,
% 2.15/0.65      (![X1, X3, X2] : ((~r1_tarski(k3_xboole_0(X2,X3),X1) | (k1_xboole_0 = k3_xboole_0(X2,X3)) | ~r1_xboole_0(X1,X2))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2002,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(k1_xboole_0,k1_xboole_0)) | ~r1_tarski(k1_xboole_0,k1_xboole_0))).
% 2.15/0.65  
% 2.15/0.65  tff(u2001,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X27, X26, X28] : ((~r1_tarski(sK0,X28) | r1_tarski(k1_xboole_0,k3_xboole_0(X27,X28)) | ~r1_tarski(k3_xboole_0(X26,sK1),X27)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u2000,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X16, X15, X14] : ((~r1_tarski(sK0,X15) | ~r1_tarski(k3_xboole_0(X14,sK1),X16) | r1_tarski(k1_xboole_0,k3_xboole_0(X15,X16))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1999,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X27, X26, X28] : ((~r1_tarski(sK0,X28) | r1_tarski(k1_xboole_0,k3_xboole_0(X27,X28)) | ~r1_tarski(k3_xboole_0(sK1,X26),X27)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1998,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X16, X15, X14] : ((~r1_tarski(sK0,X15) | ~r1_tarski(k3_xboole_0(sK1,X14),X16) | r1_tarski(k1_xboole_0,k3_xboole_0(X15,X16))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1997,negated_conjecture,
% 2.15/0.65      ((~(![X0] : ((~r1_tarski(sK0,X0) | ~r1_xboole_0(X0,sK2))))) | (![X0] : ((~r1_tarski(sK0,X0) | ~r1_xboole_0(X0,sK2)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1996,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK0,k3_xboole_0(sK1,sK2))) | ~r1_tarski(sK0,k3_xboole_0(sK1,sK2)))).
% 2.15/0.65  
% 2.15/0.65  tff(u1995,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK0,sK0)) | ~r1_tarski(sK0,sK0))).
% 2.15/0.65  
% 2.15/0.65  tff(u1994,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK0,sK1)) | ~r1_tarski(sK0,sK1))).
% 2.15/0.65  
% 2.15/0.65  tff(u1993,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK1,k3_xboole_0(sK1,sK2))) | ~r1_tarski(sK1,k3_xboole_0(sK1,sK2)))).
% 2.15/0.65  
% 2.15/0.65  tff(u1992,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK1,sK0)) | ~r1_tarski(sK1,sK0))).
% 2.15/0.65  
% 2.15/0.65  tff(u1991,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK1,sK1)) | ~r1_tarski(sK1,sK1))).
% 2.15/0.65  
% 2.15/0.65  tff(u1990,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK1,sK2)) | ~r1_tarski(sK1,sK2))).
% 2.15/0.65  
% 2.15/0.65  tff(u1989,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK2,k3_xboole_0(sK1,sK2))) | ~r1_tarski(sK2,k3_xboole_0(sK1,sK2)))).
% 2.15/0.65  
% 2.15/0.65  tff(u1988,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK2,sK0)) | ~r1_tarski(sK2,sK0))).
% 2.15/0.65  
% 2.15/0.65  tff(u1987,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK2,sK1)) | ~r1_tarski(sK2,sK1))).
% 2.15/0.65  
% 2.15/0.65  tff(u1986,negated_conjecture,
% 2.15/0.65      ((~~r1_tarski(sK2,sK2)) | ~r1_tarski(sK2,sK2))).
% 2.15/0.65  
% 2.15/0.65  tff(u1985,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | r1_tarski(sK0,sK2))).
% 2.15/0.65  
% 2.15/0.65  tff(u1984,axiom,
% 2.15/0.65      (![X1, X0] : (r1_tarski(k3_xboole_0(X0,X1),X0)))).
% 2.15/0.65  
% 2.15/0.65  tff(u1983,axiom,
% 2.15/0.65      (![X1, X0] : (r1_tarski(k3_xboole_0(X1,X0),X0)))).
% 2.15/0.65  
% 2.15/0.65  tff(u1982,axiom,
% 2.15/0.65      (![X1, X3, X0, X2] : ((r1_tarski(k3_xboole_0(X1,X0),k3_xboole_0(X2,X3)) | ~r1_tarski(X1,X3) | ~r1_tarski(X0,X2))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1981,axiom,
% 2.15/0.65      (![X1, X3, X0, X2] : ((r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1980,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X11, X10] : ((r1_tarski(k3_xboole_0(X10,X11),k1_xboole_0) | ~r1_tarski(X11,sK0) | ~r1_tarski(X10,k3_xboole_0(sK1,sK2))))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1979,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X9, X8] : ((r1_tarski(k3_xboole_0(X8,X9),k1_xboole_0) | ~r1_tarski(X9,k3_xboole_0(sK1,sK2)) | ~r1_tarski(X8,sK0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1978,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X9, X8, X10] : (r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X8),k3_xboole_0(k3_xboole_0(sK1,X9),X10)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1977,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(k3_xboole_0(X0,sK1),X2)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1976,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X11, X13, X12] : (r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X11),k3_xboole_0(X12,k3_xboole_0(sK1,X13))),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1975,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(sK0,X1),k3_xboole_0(X2,k3_xboole_0(X0,sK1))),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1974,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X7, X8, X6] : (r1_tarski(k3_xboole_0(k3_xboole_0(X6,sK0),k3_xboole_0(k3_xboole_0(sK1,X7),X8)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1973,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(k3_xboole_0(X0,sK1),X2)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1972,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X7, X8, X6] : (r1_tarski(k3_xboole_0(k3_xboole_0(X6,sK0),k3_xboole_0(X7,k3_xboole_0(sK1,X8))),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1971,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(X1,sK0),k3_xboole_0(X2,k3_xboole_0(X0,sK1))),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1970,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),k3_xboole_0(sK0,X0)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1969,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(sK1,X2)),k3_xboole_0(X0,sK0)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1968,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,sK1)),k3_xboole_0(sK0,X0)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1967,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(X1,k3_xboole_0(X2,sK1)),k3_xboole_0(X0,sK0)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1966,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X1),X2),k3_xboole_0(sK0,X0)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1965,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(sK1,X1),X2),k3_xboole_0(X0,sK0)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1964,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,sK1),X2),k3_xboole_0(sK0,X0)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1963,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X1, X0, X2] : (r1_tarski(k3_xboole_0(k3_xboole_0(k3_xboole_0(X1,sK1),X2),k3_xboole_0(X0,sK0)),k1_xboole_0))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1962,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(k1_xboole_0,sK0)) | r1_tarski(k1_xboole_0,sK0))).
% 2.15/0.65  
% 2.15/0.65  tff(u1961,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X5, X4] : ((r1_tarski(k1_xboole_0,k3_xboole_0(X5,k3_xboole_0(X4,X3))) | ~r1_tarski(sK2,X4) | ~r1_tarski(sK1,X3) | ~r1_tarski(sK0,X5)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1960,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(sK0,k3_xboole_0(sK1,sK2)))) | (![X3, X2, X4] : ((r1_tarski(k1_xboole_0,k3_xboole_0(X2,k3_xboole_0(X3,X4))) | ~r1_tarski(sK0,X2) | ~r1_tarski(sK2,X4) | ~r1_tarski(sK1,X3)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1959,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X0] : (r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK1)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1958,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X0] : (r1_tarski(k1_xboole_0,k3_xboole_0(X0,sK2)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1957,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X1, X0, X2] : ((r1_tarski(k1_xboole_0,k3_xboole_0(k3_xboole_0(X1,X0),X2)) | ~r1_tarski(sK2,X1) | ~r1_tarski(sK0,X2) | ~r1_tarski(sK1,X0)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1956,negated_conjecture,
% 2.15/0.65      ((~(k1_xboole_0 = k3_xboole_0(k3_xboole_0(sK1,sK2),sK0))) | (![X3, X2, X4] : ((r1_tarski(k1_xboole_0,k3_xboole_0(k3_xboole_0(X3,X4),X2)) | ~r1_tarski(sK0,X2) | ~r1_tarski(sK2,X4) | ~r1_tarski(sK1,X3)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1955,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X20] : (r1_tarski(k1_xboole_0,k3_xboole_0(sK1,X20)))))).
% 2.15/0.65  
% 2.15/0.65  tff(u1954,negated_conjecture,
% 2.15/0.65      ((~r1_tarski(sK0,sK2)) | (~r1_xboole_0(k3_xboole_0(sK1,sK2),sK0)) | (![X0] : (r1_tarski(k1_xboole_0,k3_xboole_0(sK2,X0)))))).
% 2.15/0.65  
% 2.15/0.65  % (25196)# SZS output end Saturation.
% 2.15/0.65  % (25196)------------------------------
% 2.15/0.65  % (25196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.65  % (25196)Termination reason: Satisfiable
% 2.15/0.65  
% 2.15/0.65  % (25196)Memory used [KB]: 7675
% 2.15/0.65  % (25196)Time elapsed: 0.177 s
% 2.15/0.65  % (25196)------------------------------
% 2.15/0.65  % (25196)------------------------------
% 2.15/0.65  % (25184)Success in time 0.286 s
%------------------------------------------------------------------------------
