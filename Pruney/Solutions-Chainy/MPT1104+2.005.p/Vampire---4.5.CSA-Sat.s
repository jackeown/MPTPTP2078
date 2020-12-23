%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:08:51 EST 2020

% Result     : CounterSatisfiable 5.51s
% Output     : Saturation 5.51s
% Verified   : 
% Statistics : Number of formulae       :  118 ( 118 expanded)
%              Number of leaves         :  118 ( 118 expanded)
%              Depth                    :    0
%              Number of atoms          :  167 ( 167 expanded)
%              Number of equality atoms :  145 ( 145 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
tff(u2447,negated_conjecture,
    ( ~ ( k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 )
    | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2 )).

tff(u2446,axiom,(
    ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) )).

tff(u2445,axiom,(
    ! [X7,X6] : k2_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X6,X7),X6),X6) )).

tff(u2444,axiom,(
    ! [X9,X8] : k2_xboole_0(X9,X8) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X9,X8),X8),X8) )).

tff(u2443,axiom,(
    ! [X7,X6] : k2_xboole_0(X6,X7) = k2_xboole_0(X6,k4_xboole_0(k2_xboole_0(X6,X7),X6)) )).

tff(u2442,axiom,(
    ! [X9,X8] : k2_xboole_0(X9,X8) = k2_xboole_0(X8,k4_xboole_0(k2_xboole_0(X9,X8),X8)) )).

tff(u2441,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 )).

tff(u2440,axiom,(
    ! [X0] : k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0) )).

tff(u2439,axiom,(
    ! [X3,X2] : k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2 )).

tff(u2438,axiom,(
    ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0 )).

tff(u2437,axiom,(
    ! [X18,X19] : k2_xboole_0(k4_xboole_0(X18,k3_xboole_0(X18,X19)),k3_xboole_0(X18,X19)) = X18 )).

tff(u2436,axiom,(
    ! [X18,X19] : k2_xboole_0(k4_xboole_0(X19,k3_xboole_0(X18,X19)),k3_xboole_0(X18,X19)) = X19 )).

tff(u2435,axiom,(
    ! [X2] : k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2 )).

tff(u2434,axiom,(
    ! [X16,X17] : k2_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),k4_xboole_0(X16,X17)) = X16 )).

tff(u2433,axiom,(
    ! [X20,X21] : k2_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = X20 )).

tff(u2432,axiom,(
    ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 )).

tff(u2431,axiom,(
    ! [X22,X23] : k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(X22,k3_xboole_0(X22,X23))) = X22 )).

tff(u2430,axiom,(
    ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0 )).

tff(u2429,axiom,(
    ! [X1,X2] : k2_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X1)),k1_xboole_0) = X1 )).

tff(u2428,axiom,(
    ! [X0] : k2_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = X0 )).

tff(u2427,axiom,(
    ! [X5,X4] : k2_xboole_0(k3_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = X4 )).

tff(u2426,axiom,(
    ! [X22,X23] : k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(X23,k3_xboole_0(X22,X23))) = X23 )).

tff(u2425,axiom,(
    ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 )).

tff(u2424,axiom,(
    ! [X4] : k2_xboole_0(k1_xboole_0,k3_xboole_0(X4,X4)) = X4 )).

tff(u2423,axiom,(
    ! [X3,X2] : k2_xboole_0(k1_xboole_0,k3_xboole_0(X2,k2_xboole_0(X3,X2))) = X2 )).

tff(u2422,axiom,(
    ! [X4] : k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0)) = X4 )).

tff(u2421,negated_conjecture,
    ( k2_xboole_0(sK1,u1_struct_0(sK0)) != k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))
    | k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)) )).

tff(u2420,negated_conjecture,
    ( k2_xboole_0(sK2,u1_struct_0(sK0)) != k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))
    | k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)) )).

tff(u2419,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0) )).

tff(u2418,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k4_xboole_0(X0,X1))) )).

tff(u2417,axiom,(
    ! [X25,X24] : k4_xboole_0(X24,k3_xboole_0(X24,X25)) = k4_xboole_0(X24,X25) )).

tff(u2416,axiom,(
    ! [X25,X24] : k4_xboole_0(X25,k3_xboole_0(X24,X25)) = k4_xboole_0(X25,X24) )).

tff(u2415,axiom,(
    ! [X5,X6] : k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5) )).

tff(u2414,axiom,(
    ! [X3,X4] : k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)) )).

tff(u2413,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )).

tff(u2412,axiom,(
    ! [X7,X6] : k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X7,X6)) )).

tff(u2411,axiom,(
    ! [X1,X0] : k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1) )).

tff(u2410,axiom,(
    ! [X1] : k4_xboole_0(X1,k1_xboole_0) = X1 )).

tff(u2409,axiom,(
    ! [X5] : k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0) )).

tff(u2408,axiom,(
    ! [X22,X23] : k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k5_xboole_0(X22,k4_xboole_0(X22,X23)) )).

tff(u2407,axiom,(
    ! [X7,X6] : k4_xboole_0(k2_xboole_0(X6,X7),X6) = k5_xboole_0(k2_xboole_0(X6,X7),X6) )).

tff(u2406,axiom,(
    ! [X9,X8] : k4_xboole_0(k2_xboole_0(X9,X8),X8) = k5_xboole_0(k2_xboole_0(X9,X8),X8) )).

tff(u2405,axiom,(
    ! [X1] : k3_xboole_0(X1,X1) = X1 )).

tff(u2404,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2 )).

tff(u2403,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 )).

tff(u2402,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k1_xboole_0) )).

tff(u2401,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0) )).

tff(u2400,axiom,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k2_xboole_0(k3_xboole_0(X6,k3_xboole_0(X5,X6)),k1_xboole_0) )).

tff(u2399,axiom,(
    ! [X5,X6] : k3_xboole_0(X5,X6) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X5,k3_xboole_0(X5,X6))) )).

tff(u2398,axiom,(
    ! [X3,X4] : k3_xboole_0(X3,X4) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X4,k3_xboole_0(X3,X4))) )).

tff(u2397,axiom,(
    ! [X3,X2] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) )).

tff(u2396,axiom,(
    ! [X7,X8] : k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),X7) )).

tff(u2395,axiom,(
    ! [X3,X4] : k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)) )).

tff(u2394,axiom,(
    ! [X7,X6] : k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6)) )).

tff(u2393,axiom,(
    ! [X18,X17] : k3_xboole_0(X18,X17) = k3_xboole_0(k3_xboole_0(X18,X17),X17) )).

tff(u2392,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) )).

tff(u2391,axiom,(
    ! [X1,X0] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) )).

tff(u2390,axiom,(
    ! [X13,X12] : k3_xboole_0(k2_xboole_0(X12,X13),X12) = X12 )).

tff(u2389,axiom,(
    ! [X15,X14] : k3_xboole_0(k2_xboole_0(X15,X14),X14) = X14 )).

tff(u2388,axiom,(
    ! [X9] : k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,X9),k1_xboole_0) )).

tff(u2387,axiom,(
    ! [X0] : k1_xboole_0 = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0) )).

tff(u2386,axiom,(
    ! [X7] : k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)) )).

tff(u2385,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) )).

tff(u2384,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)) )).

tff(u2383,axiom,(
    ! [X4] : k1_xboole_0 = k4_xboole_0(X4,X4) )).

tff(u2382,axiom,(
    ! [X5,X6] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5) )).

tff(u2381,axiom,(
    ! [X1,X0] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0) )).

tff(u2380,axiom,(
    ! [X3,X2] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X2),X2) )).

tff(u2379,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) )).

tff(u2378,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK1,k2_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)) )).

tff(u2377,negated_conjecture,
    ( k1_xboole_0 != k4_xboole_0(sK2,k2_struct_0(sK0))
    | k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)) )).

tff(u2376,axiom,(
    ! [X2] : k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2) )).

tff(u2375,axiom,(
    ! [X1] : k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0) )).

tff(u2374,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(sK1,sK1)
    | k1_xboole_0 = k5_xboole_0(sK1,sK1) )).

tff(u2373,negated_conjecture,
    ( k1_xboole_0 != k5_xboole_0(sK2,sK2)
    | k1_xboole_0 = k5_xboole_0(sK2,sK2) )).

tff(u2372,axiom,(
    ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3) )).

tff(u2371,axiom,(
    ! [X1,X0] : k2_tarski(X0,X1) = k2_tarski(X1,X0) )).

tff(u2370,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 )).

tff(u2369,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK1) != k2_xboole_0(sK1,sK1)
    | k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1) )).

tff(u2368,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),sK2,sK2) != k2_xboole_0(sK2,sK2)
    | k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2) )).

tff(u2367,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) != k2_xboole_0(sK2,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)) )).

tff(u2366,negated_conjecture,
    ( k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) != k2_xboole_0(sK1,u1_struct_0(sK0))
    | k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)) )).

tff(u2365,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0) )).

tff(u2364,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] : k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0) )).

tff(u2363,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK1,sK2)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2) )).

tff(u2362,negated_conjecture,
    ( k2_struct_0(sK0) != k4_subset_1(u1_struct_0(sK0),sK2,sK1)
    | k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1) )).

tff(u2361,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(sK1,sK2)
    | k2_struct_0(sK0) = k2_xboole_0(sK1,sK2) )).

tff(u2360,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(sK1,k3_xboole_0(k2_struct_0(sK0),sK2))
    | k2_struct_0(sK0) = k2_xboole_0(sK1,k3_xboole_0(k2_struct_0(sK0),sK2)) )).

tff(u2359,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(sK2,sK1)
    | k2_struct_0(sK0) = k2_xboole_0(sK2,sK1) )).

tff(u2358,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(sK2,k3_xboole_0(k2_struct_0(sK0),sK1))
    | k2_struct_0(sK0) = k2_xboole_0(sK2,k3_xboole_0(k2_struct_0(sK0),sK1)) )).

tff(u2357,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(k3_xboole_0(k2_struct_0(sK0),sK2),sK1)
    | k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(k2_struct_0(sK0),sK2),sK1) )).

tff(u2356,negated_conjecture,
    ( k2_struct_0(sK0) != k2_xboole_0(k3_xboole_0(k2_struct_0(sK0),sK1),sK2)
    | k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(k2_struct_0(sK0),sK1),sK2) )).

tff(u2355,negated_conjecture,
    ( sK1 != k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),k1_xboole_0)
    | sK1 = k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),k1_xboole_0) )).

tff(u2354,negated_conjecture,
    ( sK1 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_struct_0(sK0)))
    | sK1 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_struct_0(sK0))) )).

tff(u2353,negated_conjecture,
    ( sK1 != k4_xboole_0(k2_xboole_0(sK1,sK2),sK2)
    | sK1 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK2) )).

tff(u2352,negated_conjecture,
    ( sK1 != k4_xboole_0(k2_struct_0(sK0),sK2)
    | sK1 = k4_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u2351,negated_conjecture,
    ( sK1 != k3_xboole_0(sK1,k2_struct_0(sK0))
    | sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)) )).

tff(u2350,negated_conjecture,
    ( sK1 != k3_xboole_0(k2_struct_0(sK0),sK1)
    | sK1 = k3_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u2349,negated_conjecture,
    ( sK1 != k5_xboole_0(k2_struct_0(sK0),sK2)
    | sK1 = k5_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u2348,negated_conjecture,
    ( sK2 != k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k1_xboole_0)
    | sK2 = k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k1_xboole_0) )).

tff(u2347,negated_conjecture,
    ( sK2 != k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_struct_0(sK0)))
    | sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_struct_0(sK0))) )).

tff(u2346,negated_conjecture,
    ( sK2 != k4_xboole_0(k2_xboole_0(sK1,sK2),sK1)
    | sK2 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK1) )).

tff(u2345,negated_conjecture,
    ( sK2 != k4_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k4_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u2344,negated_conjecture,
    ( sK2 != k3_xboole_0(sK2,k2_struct_0(sK0))
    | sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)) )).

tff(u2343,negated_conjecture,
    ( sK2 != k3_xboole_0(k2_struct_0(sK0),sK2)
    | sK2 = k3_xboole_0(k2_struct_0(sK0),sK2) )).

tff(u2342,negated_conjecture,
    ( sK2 != k5_xboole_0(k2_struct_0(sK0),sK1)
    | sK2 = k5_xboole_0(k2_struct_0(sK0),sK1) )).

tff(u2341,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0 ) )).

tff(u2340,axiom,(
    ! [X1,X0] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) )).

tff(u2339,negated_conjecture,
    ( ~ r1_xboole_0(sK1,sK2)
    | r1_xboole_0(sK1,sK2) )).

tff(u2338,negated_conjecture,
    ( ~ r1_xboole_0(sK2,sK1)
    | r1_xboole_0(sK2,sK1) )).

tff(u2337,axiom,(
    ! [X1,X0] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X0) = k4_subset_1(X0,X1,X0) ) )).

tff(u2336,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) )).

tff(u2335,axiom,(
    ! [X1,X0,X2] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) )).

tff(u2334,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1) ) )).

tff(u2333,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2) ) )).

tff(u2332,negated_conjecture,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u2331,negated_conjecture,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) )).

tff(u2330,axiom,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) )).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n008.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 11:14:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (32724)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.51  % (32732)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.52  % (32710)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (32710)Refutation not found, incomplete strategy% (32710)------------------------------
% 0.21/0.52  % (32710)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (32710)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (32710)Memory used [KB]: 1791
% 0.21/0.52  % (32710)Time elapsed: 0.099 s
% 0.21/0.52  % (32710)------------------------------
% 0.21/0.52  % (32710)------------------------------
% 0.21/0.52  % (32716)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (32715)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 1.22/0.53  % (32714)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.22/0.53  % (32732)Refutation not found, incomplete strategy% (32732)------------------------------
% 1.22/0.53  % (32732)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (32712)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.22/0.53  % (32714)Refutation not found, incomplete strategy% (32714)------------------------------
% 1.22/0.53  % (32714)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (32714)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (32714)Memory used [KB]: 6268
% 1.22/0.53  % (32714)Time elapsed: 0.108 s
% 1.22/0.53  % (32714)------------------------------
% 1.22/0.53  % (32714)------------------------------
% 1.22/0.53  % (32732)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (32732)Memory used [KB]: 10874
% 1.22/0.53  % (32732)Time elapsed: 0.059 s
% 1.22/0.53  % (32732)------------------------------
% 1.22/0.53  % (32732)------------------------------
% 1.22/0.53  % (32718)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.22/0.53  % (32731)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.22/0.53  % (32711)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.22/0.54  % (32713)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.22/0.54  % (32733)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.22/0.54  % (32739)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.22/0.54  % (32719)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.22/0.54  % (32736)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.22/0.55  % (32723)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.22/0.55  % (32737)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.22/0.55  % (32717)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.22/0.55  % (32738)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.22/0.55  % (32735)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.22/0.55  % (32728)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.22/0.55  % (32726)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.45/0.55  % (32725)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.55  % (32722)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.45/0.55  % (32725)Refutation not found, incomplete strategy% (32725)------------------------------
% 1.45/0.55  % (32725)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (32725)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.55  
% 1.45/0.55  % (32725)Memory used [KB]: 6140
% 1.45/0.55  % (32725)Time elapsed: 0.002 s
% 1.45/0.55  % (32725)------------------------------
% 1.45/0.55  % (32725)------------------------------
% 1.45/0.55  % (32730)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.45/0.55  % (32718)Refutation not found, incomplete strategy% (32718)------------------------------
% 1.45/0.55  % (32718)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (32727)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.45/0.56  % (32731)Refutation not found, incomplete strategy% (32731)------------------------------
% 1.45/0.56  % (32731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (32729)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.45/0.56  % (32734)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.45/0.56  % (32718)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (32718)Memory used [KB]: 10874
% 1.45/0.56  % (32718)Time elapsed: 0.123 s
% 1.45/0.56  % (32718)------------------------------
% 1.45/0.56  % (32718)------------------------------
% 1.45/0.56  % (32733)Refutation not found, incomplete strategy% (32733)------------------------------
% 1.45/0.56  % (32733)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.56  % (32733)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.56  
% 1.45/0.56  % (32733)Memory used [KB]: 1918
% 1.45/0.56  % (32733)Time elapsed: 0.126 s
% 1.45/0.56  % (32733)------------------------------
% 1.45/0.56  % (32733)------------------------------
% 1.45/0.57  % (32720)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.45/0.57  % (32721)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.45/0.57  % (32731)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (32731)Memory used [KB]: 1918
% 1.45/0.57  % (32731)Time elapsed: 0.146 s
% 1.45/0.57  % (32731)------------------------------
% 1.45/0.57  % (32731)------------------------------
% 1.45/0.57  % (32719)Refutation not found, incomplete strategy% (32719)------------------------------
% 1.45/0.57  % (32719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (32719)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (32719)Memory used [KB]: 10746
% 1.45/0.57  % (32719)Time elapsed: 0.143 s
% 1.45/0.57  % (32719)------------------------------
% 1.45/0.57  % (32719)------------------------------
% 1.45/0.57  % (32720)Refutation not found, incomplete strategy% (32720)------------------------------
% 1.45/0.57  % (32720)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (32720)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (32720)Memory used [KB]: 10746
% 1.45/0.57  % (32720)Time elapsed: 0.151 s
% 1.45/0.57  % (32720)------------------------------
% 1.45/0.57  % (32720)------------------------------
% 1.45/0.57  % (32727)Refutation not found, incomplete strategy% (32727)------------------------------
% 1.45/0.57  % (32727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (32727)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (32727)Memory used [KB]: 10618
% 1.45/0.57  % (32727)Time elapsed: 0.146 s
% 1.45/0.57  % (32727)------------------------------
% 1.45/0.57  % (32727)------------------------------
% 1.45/0.57  % (32721)Refutation not found, incomplete strategy% (32721)------------------------------
% 1.45/0.57  % (32721)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (32721)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (32721)Memory used [KB]: 10746
% 1.45/0.57  % (32721)Time elapsed: 0.151 s
% 1.45/0.57  % (32721)------------------------------
% 1.45/0.57  % (32721)------------------------------
% 1.45/0.57  % (32736)Refutation not found, incomplete strategy% (32736)------------------------------
% 1.45/0.57  % (32736)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (32736)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (32736)Memory used [KB]: 11001
% 1.45/0.57  % (32736)Time elapsed: 0.160 s
% 1.45/0.57  % (32736)------------------------------
% 1.45/0.57  % (32736)------------------------------
% 1.45/0.57  % (32712)Refutation not found, incomplete strategy% (32712)------------------------------
% 1.45/0.57  % (32712)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.57  % (32712)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.57  
% 1.45/0.57  % (32712)Memory used [KB]: 11001
% 1.45/0.57  % (32712)Time elapsed: 0.134 s
% 1.45/0.57  % (32712)------------------------------
% 1.45/0.57  % (32712)------------------------------
% 1.45/0.58  % (32730)Refutation not found, incomplete strategy% (32730)------------------------------
% 1.45/0.58  % (32730)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.58  % (32730)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.58  
% 1.45/0.58  % (32730)Memory used [KB]: 10874
% 1.45/0.58  % (32730)Time elapsed: 0.143 s
% 1.45/0.58  % (32730)------------------------------
% 1.45/0.58  % (32730)------------------------------
% 1.45/0.60  % (32717)Refutation not found, incomplete strategy% (32717)------------------------------
% 1.45/0.60  % (32717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.60  % (32717)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.60  
% 1.45/0.60  % (32717)Memory used [KB]: 6780
% 1.45/0.60  % (32717)Time elapsed: 0.168 s
% 1.45/0.60  % (32717)------------------------------
% 1.45/0.60  % (32717)------------------------------
% 1.45/0.60  % (32735)Refutation not found, incomplete strategy% (32735)------------------------------
% 1.45/0.60  % (32735)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.60  % (32735)Termination reason: Refutation not found, incomplete strategy
% 1.45/0.60  
% 1.45/0.60  % (32735)Memory used [KB]: 6908
% 1.45/0.60  % (32735)Time elapsed: 0.162 s
% 1.45/0.60  % (32735)------------------------------
% 1.45/0.60  % (32735)------------------------------
% 1.45/0.64  % (300)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 1.95/0.65  % (300)Refutation not found, incomplete strategy% (300)------------------------------
% 1.95/0.65  % (300)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.95/0.65  % (300)Termination reason: Refutation not found, incomplete strategy
% 1.95/0.65  
% 1.95/0.65  % (300)Memory used [KB]: 6268
% 1.95/0.65  % (300)Time elapsed: 0.084 s
% 1.95/0.65  % (300)------------------------------
% 1.95/0.65  % (300)------------------------------
% 1.95/0.66  % (301)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 1.95/0.66  % (313)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 2.15/0.69  % (315)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 2.15/0.69  % (32711)Refutation not found, incomplete strategy% (32711)------------------------------
% 2.15/0.69  % (32711)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.69  % (324)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 2.15/0.70  % (321)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 2.15/0.70  % (32711)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.70  
% 2.15/0.70  % (32711)Memory used [KB]: 6268
% 2.15/0.70  % (32711)Time elapsed: 0.261 s
% 2.15/0.70  % (32711)------------------------------
% 2.15/0.70  % (32711)------------------------------
% 2.15/0.70  % (317)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 2.15/0.70  % (322)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 2.15/0.70  % (327)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 2.15/0.70  % (318)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 2.15/0.70  % (325)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 2.15/0.71  % (332)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 2.15/0.71  % (333)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 2.15/0.71  % (330)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 2.15/0.72  % (324)Refutation not found, incomplete strategy% (324)------------------------------
% 2.15/0.72  % (324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.73  % (333)Refutation not found, incomplete strategy% (333)------------------------------
% 2.15/0.73  % (333)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.15/0.73  % (333)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.73  
% 2.15/0.73  % (333)Memory used [KB]: 1791
% 2.15/0.73  % (333)Time elapsed: 0.107 s
% 2.15/0.73  % (333)------------------------------
% 2.15/0.73  % (333)------------------------------
% 2.15/0.73  % (344)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 2.15/0.73  % (324)Termination reason: Refutation not found, incomplete strategy
% 2.15/0.73  
% 2.15/0.73  % (324)Memory used [KB]: 1918
% 2.15/0.73  % (324)Time elapsed: 0.086 s
% 2.15/0.73  % (324)------------------------------
% 2.15/0.73  % (324)------------------------------
% 2.44/0.75  % (327)Refutation not found, incomplete strategy% (327)------------------------------
% 2.44/0.75  % (327)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.44/0.75  % (327)Termination reason: Refutation not found, incomplete strategy
% 2.44/0.75  
% 2.44/0.75  % (327)Memory used [KB]: 6652
% 2.44/0.75  % (327)Time elapsed: 0.140 s
% 2.44/0.75  % (327)------------------------------
% 2.44/0.75  % (327)------------------------------
% 2.44/0.75  % (343)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 2.44/0.75  % (321)Refutation not found, incomplete strategy% (321)------------------------------
% 2.44/0.75  % (321)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.57/0.76  % (373)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 2.57/0.77  % (321)Termination reason: Refutation not found, incomplete strategy
% 2.57/0.77  
% 2.57/0.77  % (321)Memory used [KB]: 2430
% 2.57/0.77  % (321)Time elapsed: 0.148 s
% 2.57/0.77  % (321)------------------------------
% 2.57/0.77  % (321)------------------------------
% 2.81/0.82  % (405)ott+11_2:1_add=large:afp=40000:afq=2.0:amm=sco:anc=none:br=off:cond=on:irw=on:nwc=1:sd=2:ss=axioms:st=2.0:sos=all:urr=on:updr=off_111 on theBenchmark
% 2.81/0.82  % (301)Refutation not found, incomplete strategy% (301)------------------------------
% 2.81/0.82  % (301)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.83  % (301)Termination reason: Refutation not found, incomplete strategy
% 2.81/0.83  
% 2.81/0.83  % (301)Memory used [KB]: 6268
% 2.81/0.83  % (301)Time elapsed: 0.258 s
% 2.81/0.83  % (301)------------------------------
% 2.81/0.83  % (301)------------------------------
% 2.81/0.84  % (405)Refutation not found, incomplete strategy% (405)------------------------------
% 2.81/0.84  % (405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.84  % (405)Termination reason: Refutation not found, incomplete strategy
% 2.81/0.84  
% 2.81/0.84  % (405)Memory used [KB]: 6268
% 2.81/0.84  % (405)Time elapsed: 0.108 s
% 2.81/0.84  % (405)------------------------------
% 2.81/0.84  % (405)------------------------------
% 2.81/0.85  % (32715)Time limit reached!
% 2.81/0.85  % (32715)------------------------------
% 2.81/0.85  % (32715)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.81/0.85  % (32715)Termination reason: Time limit
% 2.81/0.85  
% 2.81/0.85  % (32715)Memory used [KB]: 9338
% 2.81/0.85  % (32715)Time elapsed: 0.426 s
% 2.81/0.85  % (32715)------------------------------
% 2.81/0.85  % (32715)------------------------------
% 3.05/0.86  % (425)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_1 on theBenchmark
% 3.05/0.87  % (332)Refutation not found, incomplete strategy% (332)------------------------------
% 3.05/0.87  % (332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.87  % (332)Termination reason: Refutation not found, incomplete strategy
% 3.05/0.87  
% 3.05/0.87  % (332)Memory used [KB]: 1791
% 3.05/0.87  % (332)Time elapsed: 0.271 s
% 3.05/0.87  % (332)------------------------------
% 3.05/0.87  % (332)------------------------------
% 3.05/0.87  % (431)ott+1_128_add=large:afr=on:amm=sco:anc=none:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lcm=reverse:lma=on:nm=64:nwc=1.1:nicw=on:sas=z3:sac=on:sp=reverse_arity_44 on theBenchmark
% 3.05/0.87  % (423)lrs+2_4_awrs=decay:awrsf=1:afr=on:afp=10000:afq=1.0:amm=off:anc=none:bd=off:cond=on:fde=none:gs=on:lcm=predicate:nm=2:nwc=4:sas=z3:stl=30:s2a=on:sp=occurrence:urr=on:uhcvi=on_9 on theBenchmark
% 3.05/0.89  % (439)lrs+10_3:1_av=off:bsr=on:cond=on:er=known:gs=on:lcm=reverse:nm=32:nwc=4:stl=30:sp=occurrence:urr=on:updr=off_73 on theBenchmark
% 3.05/0.93  % (32722)Time limit reached!
% 3.05/0.93  % (32722)------------------------------
% 3.05/0.93  % (32722)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.93  % (32722)Termination reason: Time limit
% 3.05/0.93  
% 3.05/0.93  % (32722)Memory used [KB]: 9338
% 3.05/0.93  % (32722)Time elapsed: 0.515 s
% 3.05/0.93  % (32722)------------------------------
% 3.05/0.93  % (32722)------------------------------
% 3.41/0.96  % (460)ott+10_8:1_av=off:bd=preordered:bsr=on:cond=fast:fsr=off:gs=on:gsem=off:lcm=predicate:nm=0:nwc=1.2:sp=reverse_arity:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.41/0.96  % (453)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_117 on theBenchmark
% 3.41/0.97  % (449)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_275 on theBenchmark
% 3.53/0.99  % (317)Time limit reached!
% 3.53/0.99  % (317)------------------------------
% 3.53/0.99  % (317)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.99  % (315)Time limit reached!
% 3.53/0.99  % (315)------------------------------
% 3.53/0.99  % (315)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/0.99  % (315)Termination reason: Time limit
% 3.53/0.99  
% 3.53/0.99  % (315)Memory used [KB]: 7547
% 3.53/0.99  % (315)Time elapsed: 0.404 s
% 3.53/0.99  % (315)------------------------------
% 3.53/0.99  % (315)------------------------------
% 3.53/1.01  % (317)Termination reason: Time limit
% 3.53/1.01  % (317)Termination phase: Saturation
% 3.53/1.01  
% 3.53/1.01  % (317)Memory used [KB]: 13048
% 3.53/1.01  % (317)Time elapsed: 0.400 s
% 3.53/1.01  % (317)------------------------------
% 3.53/1.01  % (317)------------------------------
% 3.53/1.01  % (32726)Time limit reached!
% 3.53/1.01  % (32726)------------------------------
% 3.53/1.01  % (32726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/1.01  % (32726)Termination reason: Time limit
% 3.53/1.01  % (32726)Termination phase: Saturation
% 3.53/1.01  
% 3.53/1.01  % (32726)Memory used [KB]: 14583
% 3.53/1.01  % (32726)Time elapsed: 0.600 s
% 3.53/1.01  % (32726)------------------------------
% 3.53/1.01  % (32726)------------------------------
% 3.53/1.03  % (32738)Time limit reached!
% 3.53/1.03  % (32738)------------------------------
% 3.53/1.03  % (32738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.53/1.03  % (32738)Termination reason: Time limit
% 3.53/1.03  
% 3.53/1.03  % (32738)Memory used [KB]: 9338
% 3.53/1.03  % (32738)Time elapsed: 0.608 s
% 3.53/1.03  % (32738)------------------------------
% 3.53/1.03  % (32738)------------------------------
% 3.53/1.03  % (475)dis+3_24_av=off:bd=off:bs=unit_only:fsr=off:fde=unused:gs=on:irw=on:lma=on:nm=0:nwc=1.1:sos=on:uhcvi=on_180 on theBenchmark
% 3.53/1.04  % (475)Refutation not found, incomplete strategy% (475)------------------------------
% 3.53/1.04  % (475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.94/1.04  % (502)lrs+1011_10_av=off:bce=on:cond=on:fsr=off:fde=unused:gs=on:nm=2:nwc=1.1:stl=30:sd=4:ss=axioms:s2a=on:st=1.5:sos=on:sp=frequency:urr=on:updr=off:uhcvi=on_1 on theBenchmark
% 3.94/1.05  % (475)Termination reason: Refutation not found, incomplete strategy
% 3.94/1.05  
% 3.94/1.05  % (475)Memory used [KB]: 6396
% 3.94/1.05  % (475)Time elapsed: 0.108 s
% 3.94/1.05  % (475)------------------------------
% 3.94/1.05  % (475)------------------------------
% 5.51/1.07  % (502)Refutation not found, incomplete strategy% (502)------------------------------
% 5.51/1.07  % (502)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.51/1.07  % (502)Termination reason: Refutation not found, incomplete strategy
% 5.51/1.07  
% 5.51/1.07  % (502)Memory used [KB]: 6268
% 5.51/1.07  % (502)Time elapsed: 0.114 s
% 5.51/1.07  % (502)------------------------------
% 5.51/1.07  % (502)------------------------------
% 5.51/1.08  % SZS status CounterSatisfiable for theBenchmark
% 5.51/1.09  % (535)ott+1_5_afp=40000:afq=1.0:anc=all:fde=none:gs=on:irw=on:lma=on:nm=32:nwc=2:sos=all:sac=on:sp=occurrence:urr=ec_only:uhcvi=on_34 on theBenchmark
% 5.51/1.10  % (373)Time limit reached!
% 5.51/1.10  % (373)------------------------------
% 5.51/1.10  % (373)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.51/1.10  % (373)Termination reason: Time limit
% 5.51/1.10  
% 5.51/1.10  % (373)Memory used [KB]: 5884
% 5.51/1.10  % (373)Time elapsed: 0.408 s
% 5.51/1.10  % (373)------------------------------
% 5.51/1.10  % (373)------------------------------
% 5.51/1.10  % (535)Refutation not found, incomplete strategy% (535)------------------------------
% 5.51/1.10  % (535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.51/1.10  % (535)Termination reason: Refutation not found, incomplete strategy
% 5.51/1.10  
% 5.51/1.10  % (535)Memory used [KB]: 11001
% 5.51/1.10  % (535)Time elapsed: 0.088 s
% 5.51/1.10  % (535)------------------------------
% 5.51/1.10  % (535)------------------------------
% 5.51/1.11  % (423)# SZS output start Saturation.
% 5.51/1.11  tff(u2447,negated_conjecture,
% 5.51/1.11      ((~(k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2)) | (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1) != sK2))).
% 5.51/1.11  
% 5.51/1.11  tff(u2446,axiom,
% 5.51/1.11      (![X1, X0] : ((k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2445,axiom,
% 5.51/1.11      (![X7, X6] : ((k2_xboole_0(X6,X7) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X6,X7),X6),X6))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2444,axiom,
% 5.51/1.11      (![X9, X8] : ((k2_xboole_0(X9,X8) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X9,X8),X8),X8))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2443,axiom,
% 5.51/1.11      (![X7, X6] : ((k2_xboole_0(X6,X7) = k2_xboole_0(X6,k4_xboole_0(k2_xboole_0(X6,X7),X6)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2442,axiom,
% 5.51/1.11      (![X9, X8] : ((k2_xboole_0(X9,X8) = k2_xboole_0(X8,k4_xboole_0(k2_xboole_0(X9,X8),X8)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2441,axiom,
% 5.51/1.11      (![X0] : ((k2_xboole_0(X0,k1_xboole_0) = X0)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2440,axiom,
% 5.51/1.11      (![X0] : ((k2_xboole_0(X0,X0) = k4_subset_1(X0,X0,X0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2439,axiom,
% 5.51/1.11      (![X3, X2] : ((k2_xboole_0(k4_xboole_0(X2,X3),k3_xboole_0(X2,X3)) = X2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2438,axiom,
% 5.51/1.11      (![X1, X0] : ((k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) = X0)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2437,axiom,
% 5.51/1.11      (![X18, X19] : ((k2_xboole_0(k4_xboole_0(X18,k3_xboole_0(X18,X19)),k3_xboole_0(X18,X19)) = X18)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2436,axiom,
% 5.51/1.11      (![X18, X19] : ((k2_xboole_0(k4_xboole_0(X19,k3_xboole_0(X18,X19)),k3_xboole_0(X18,X19)) = X19)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2435,axiom,
% 5.51/1.11      (![X2] : ((k2_xboole_0(k4_xboole_0(X2,k1_xboole_0),k1_xboole_0) = X2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2434,axiom,
% 5.51/1.11      (![X16, X17] : ((k2_xboole_0(k4_xboole_0(X16,k4_xboole_0(X16,X17)),k4_xboole_0(X16,X17)) = X16)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2433,axiom,
% 5.51/1.11      (![X20, X21] : ((k2_xboole_0(k4_xboole_0(X20,X21),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = X20)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2432,axiom,
% 5.51/1.11      (![X1, X0] : ((k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2431,axiom,
% 5.51/1.11      (![X22, X23] : ((k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(X22,k3_xboole_0(X22,X23))) = X22)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2430,axiom,
% 5.51/1.11      (![X1, X0] : ((k2_xboole_0(k3_xboole_0(X0,k2_xboole_0(X0,X1)),k1_xboole_0) = X0)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2429,axiom,
% 5.51/1.11      (![X1, X2] : ((k2_xboole_0(k3_xboole_0(X1,k2_xboole_0(X2,X1)),k1_xboole_0) = X1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2428,axiom,
% 5.51/1.11      (![X0] : ((k2_xboole_0(k3_xboole_0(X0,X0),k1_xboole_0) = X0)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2427,axiom,
% 5.51/1.11      (![X5, X4] : ((k2_xboole_0(k3_xboole_0(X5,X4),k4_xboole_0(X4,X5)) = X4)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2426,axiom,
% 5.51/1.11      (![X22, X23] : ((k2_xboole_0(k3_xboole_0(X22,X23),k4_xboole_0(X23,k3_xboole_0(X22,X23))) = X23)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2425,axiom,
% 5.51/1.11      (![X1] : ((k2_xboole_0(k1_xboole_0,X1) = X1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2424,axiom,
% 5.51/1.11      (![X4] : ((k2_xboole_0(k1_xboole_0,k3_xboole_0(X4,X4)) = X4)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2423,axiom,
% 5.51/1.11      (![X3, X2] : ((k2_xboole_0(k1_xboole_0,k3_xboole_0(X2,k2_xboole_0(X3,X2))) = X2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2422,axiom,
% 5.51/1.11      (![X4] : ((k2_xboole_0(k1_xboole_0,k4_xboole_0(X4,k1_xboole_0)) = X4)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2421,negated_conjecture,
% 5.51/1.11      ((~(k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0)))) | (k2_xboole_0(sK1,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK1,u1_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2420,negated_conjecture,
% 5.51/1.11      ((~(k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0)))) | (k2_xboole_0(sK2,u1_struct_0(sK0)) = k4_subset_1(u1_struct_0(sK0),sK2,u1_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2419,axiom,
% 5.51/1.11      (![X1, X0] : ((k4_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k4_xboole_0(X0,X1)),k1_xboole_0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2418,axiom,
% 5.51/1.11      (![X1, X0] : ((k4_xboole_0(X0,X1) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X0,k4_xboole_0(X0,X1))))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2417,axiom,
% 5.51/1.11      (![X25, X24] : ((k4_xboole_0(X24,k3_xboole_0(X24,X25)) = k4_xboole_0(X24,X25))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2416,axiom,
% 5.51/1.11      (![X25, X24] : ((k4_xboole_0(X25,k3_xboole_0(X24,X25)) = k4_xboole_0(X25,X24))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2415,axiom,
% 5.51/1.11      (![X5, X6] : ((k4_xboole_0(X5,X6) = k3_xboole_0(k4_xboole_0(X5,X6),X5))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2414,axiom,
% 5.51/1.11      (![X3, X4] : ((k4_xboole_0(X3,X4) = k3_xboole_0(X3,k4_xboole_0(X3,X4)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2413,axiom,
% 5.51/1.11      (![X1, X0] : ((k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2412,axiom,
% 5.51/1.11      (![X7, X6] : ((k4_xboole_0(X6,X7) = k5_xboole_0(X6,k3_xboole_0(X7,X6)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2411,axiom,
% 5.51/1.11      (![X1, X0] : ((k4_xboole_0(X0,X1) = k7_subset_1(X0,X0,X1))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2410,axiom,
% 5.51/1.11      (![X1] : ((k4_xboole_0(X1,k1_xboole_0) = X1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2409,axiom,
% 5.51/1.11      (![X5] : ((k4_xboole_0(X5,k1_xboole_0) = k5_xboole_0(X5,k1_xboole_0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2408,axiom,
% 5.51/1.11      (![X22, X23] : ((k4_xboole_0(X22,k4_xboole_0(X22,X23)) = k5_xboole_0(X22,k4_xboole_0(X22,X23)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2407,axiom,
% 5.51/1.11      (![X7, X6] : ((k4_xboole_0(k2_xboole_0(X6,X7),X6) = k5_xboole_0(k2_xboole_0(X6,X7),X6))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2406,axiom,
% 5.51/1.11      (![X9, X8] : ((k4_xboole_0(k2_xboole_0(X9,X8),X8) = k5_xboole_0(k2_xboole_0(X9,X8),X8))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2405,axiom,
% 5.51/1.11      (![X1] : ((k3_xboole_0(X1,X1) = X1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2404,axiom,
% 5.51/1.11      (![X3, X2] : ((k3_xboole_0(X2,k2_xboole_0(X2,X3)) = X2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2403,axiom,
% 5.51/1.11      (![X1, X0] : ((k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2402,axiom,
% 5.51/1.11      (![X1, X0] : ((k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(k3_xboole_0(X0,X1),X0),k1_xboole_0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2401,axiom,
% 5.51/1.11      (![X1, X0] : ((k3_xboole_0(X0,X1) = k2_xboole_0(k3_xboole_0(X0,k3_xboole_0(X0,X1)),k1_xboole_0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2400,axiom,
% 5.51/1.11      (![X5, X6] : ((k3_xboole_0(X5,X6) = k2_xboole_0(k3_xboole_0(X6,k3_xboole_0(X5,X6)),k1_xboole_0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2399,axiom,
% 5.51/1.11      (![X5, X6] : ((k3_xboole_0(X5,X6) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X5,k3_xboole_0(X5,X6))))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2398,axiom,
% 5.51/1.11      (![X3, X4] : ((k3_xboole_0(X3,X4) = k2_xboole_0(k1_xboole_0,k3_xboole_0(X4,k3_xboole_0(X3,X4))))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2397,axiom,
% 5.51/1.11      (![X3, X2] : ((k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2396,axiom,
% 5.51/1.11      (![X7, X8] : ((k3_xboole_0(X7,X8) = k3_xboole_0(k3_xboole_0(X7,X8),X7))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2395,axiom,
% 5.51/1.11      (![X3, X4] : ((k3_xboole_0(X3,X4) = k3_xboole_0(X3,k3_xboole_0(X3,X4)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2394,axiom,
% 5.51/1.11      (![X7, X6] : ((k3_xboole_0(X7,X6) = k3_xboole_0(X6,k3_xboole_0(X7,X6)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2393,axiom,
% 5.51/1.11      (![X18, X17] : ((k3_xboole_0(X18,X17) = k3_xboole_0(k3_xboole_0(X18,X17),X17))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2392,axiom,
% 5.51/1.11      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2391,axiom,
% 5.51/1.11      (![X1, X0] : ((k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2390,axiom,
% 5.51/1.11      (![X13, X12] : ((k3_xboole_0(k2_xboole_0(X12,X13),X12) = X12)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2389,axiom,
% 5.51/1.11      (![X15, X14] : ((k3_xboole_0(k2_xboole_0(X15,X14),X14) = X14)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2388,axiom,
% 5.51/1.11      (![X9] : ((k1_xboole_0 = k2_xboole_0(k3_xboole_0(k1_xboole_0,X9),k1_xboole_0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2387,axiom,
% 5.51/1.11      (![X0] : ((k1_xboole_0 = k2_xboole_0(k3_xboole_0(X0,k1_xboole_0),k1_xboole_0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2386,axiom,
% 5.51/1.11      (![X7] : ((k1_xboole_0 = k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,X7)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2385,axiom,
% 5.51/1.11      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2384,axiom,
% 5.51/1.11      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X1,X0)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2383,axiom,
% 5.51/1.11      (![X4] : ((k1_xboole_0 = k4_xboole_0(X4,X4))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2382,axiom,
% 5.51/1.11      (![X5, X6] : ((k1_xboole_0 = k4_xboole_0(k4_xboole_0(X5,X6),X5))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2381,axiom,
% 5.51/1.11      (![X1, X0] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X0,X1),X0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2380,axiom,
% 5.51/1.11      (![X3, X2] : ((k1_xboole_0 = k4_xboole_0(k3_xboole_0(X3,X2),X2))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2379,axiom,
% 5.51/1.11      (![X0] : ((k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2378,negated_conjecture,
% 5.51/1.11      ((~(k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK1,k2_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2377,negated_conjecture,
% 5.51/1.11      ((~(k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0)))) | (k1_xboole_0 = k4_xboole_0(sK2,k2_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2376,axiom,
% 5.51/1.11      (![X2] : ((k1_xboole_0 = k3_xboole_0(k1_xboole_0,X2))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2375,axiom,
% 5.51/1.11      (![X1] : ((k1_xboole_0 = k3_xboole_0(X1,k1_xboole_0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2374,negated_conjecture,
% 5.51/1.11      ((~(k1_xboole_0 = k5_xboole_0(sK1,sK1))) | (k1_xboole_0 = k5_xboole_0(sK1,sK1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2373,negated_conjecture,
% 5.51/1.11      ((~(k1_xboole_0 = k5_xboole_0(sK2,sK2))) | (k1_xboole_0 = k5_xboole_0(sK2,sK2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2372,axiom,
% 5.51/1.11      (![X3] : ((k1_xboole_0 = k5_xboole_0(X3,X3))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2371,axiom,
% 5.51/1.11      (![X1, X0] : ((k2_tarski(X0,X1) = k2_tarski(X1,X0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2370,axiom,
% 5.51/1.11      (![X0] : ((k2_subset_1(X0) = X0)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2369,negated_conjecture,
% 5.51/1.11      ((~(k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1))) | (k4_subset_1(u1_struct_0(sK0),sK1,sK1) = k2_xboole_0(sK1,sK1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2368,negated_conjecture,
% 5.51/1.11      ((~(k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2))) | (k4_subset_1(u1_struct_0(sK0),sK2,sK2) = k2_xboole_0(sK2,sK2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2367,negated_conjecture,
% 5.51/1.11      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK2) = k2_xboole_0(sK2,u1_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2366,negated_conjecture,
% 5.51/1.11      ((~(k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0)))) | (k4_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),sK1) = k2_xboole_0(sK1,u1_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2365,negated_conjecture,
% 5.51/1.11      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK2,X0) = k4_xboole_0(sK2,X0)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2364,negated_conjecture,
% 5.51/1.11      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((k7_subset_1(u1_struct_0(sK0),sK1,X0) = k4_xboole_0(sK1,X0)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2363,negated_conjecture,
% 5.51/1.11      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK1,sK2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2362,negated_conjecture,
% 5.51/1.11      ((~(k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1))) | (k2_struct_0(sK0) = k4_subset_1(u1_struct_0(sK0),sK2,sK1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2361,negated_conjecture,
% 5.51/1.11      ((~(k2_struct_0(sK0) = k2_xboole_0(sK1,sK2))) | (k2_struct_0(sK0) = k2_xboole_0(sK1,sK2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2360,negated_conjecture,
% 5.51/1.11      ((~(k2_struct_0(sK0) = k2_xboole_0(sK1,k3_xboole_0(k2_struct_0(sK0),sK2)))) | (k2_struct_0(sK0) = k2_xboole_0(sK1,k3_xboole_0(k2_struct_0(sK0),sK2))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2359,negated_conjecture,
% 5.51/1.11      ((~(k2_struct_0(sK0) = k2_xboole_0(sK2,sK1))) | (k2_struct_0(sK0) = k2_xboole_0(sK2,sK1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2358,negated_conjecture,
% 5.51/1.11      ((~(k2_struct_0(sK0) = k2_xboole_0(sK2,k3_xboole_0(k2_struct_0(sK0),sK1)))) | (k2_struct_0(sK0) = k2_xboole_0(sK2,k3_xboole_0(k2_struct_0(sK0),sK1))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2357,negated_conjecture,
% 5.51/1.11      ((~(k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(k2_struct_0(sK0),sK2),sK1))) | (k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(k2_struct_0(sK0),sK2),sK1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2356,negated_conjecture,
% 5.51/1.11      ((~(k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(k2_struct_0(sK0),sK1),sK2))) | (k2_struct_0(sK0) = k2_xboole_0(k3_xboole_0(k2_struct_0(sK0),sK1),sK2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2355,negated_conjecture,
% 5.51/1.11      ((~(sK1 = k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),k1_xboole_0))) | (sK1 = k2_xboole_0(k3_xboole_0(sK1,k2_struct_0(sK0)),k1_xboole_0)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2354,negated_conjecture,
% 5.51/1.11      ((~(sK1 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_struct_0(sK0))))) | (sK1 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK1,k2_struct_0(sK0)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2353,negated_conjecture,
% 5.51/1.11      ((~(sK1 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK2))) | (sK1 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2352,negated_conjecture,
% 5.51/1.11      ((~(sK1 = k4_xboole_0(k2_struct_0(sK0),sK2))) | (sK1 = k4_xboole_0(k2_struct_0(sK0),sK2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2351,negated_conjecture,
% 5.51/1.11      ((~(sK1 = k3_xboole_0(sK1,k2_struct_0(sK0)))) | (sK1 = k3_xboole_0(sK1,k2_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2350,negated_conjecture,
% 5.51/1.11      ((~(sK1 = k3_xboole_0(k2_struct_0(sK0),sK1))) | (sK1 = k3_xboole_0(k2_struct_0(sK0),sK1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2349,negated_conjecture,
% 5.51/1.11      ((~(sK1 = k5_xboole_0(k2_struct_0(sK0),sK2))) | (sK1 = k5_xboole_0(k2_struct_0(sK0),sK2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2348,negated_conjecture,
% 5.51/1.11      ((~(sK2 = k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k1_xboole_0))) | (sK2 = k2_xboole_0(k3_xboole_0(sK2,k2_struct_0(sK0)),k1_xboole_0)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2347,negated_conjecture,
% 5.51/1.11      ((~(sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_struct_0(sK0))))) | (sK2 = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,k2_struct_0(sK0)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2346,negated_conjecture,
% 5.51/1.11      ((~(sK2 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK1))) | (sK2 = k4_xboole_0(k2_xboole_0(sK1,sK2),sK1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2345,negated_conjecture,
% 5.51/1.11      ((~(sK2 = k4_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k4_xboole_0(k2_struct_0(sK0),sK1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2344,negated_conjecture,
% 5.51/1.11      ((~(sK2 = k3_xboole_0(sK2,k2_struct_0(sK0)))) | (sK2 = k3_xboole_0(sK2,k2_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2343,negated_conjecture,
% 5.51/1.11      ((~(sK2 = k3_xboole_0(k2_struct_0(sK0),sK2))) | (sK2 = k3_xboole_0(k2_struct_0(sK0),sK2)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2342,negated_conjecture,
% 5.51/1.11      ((~(sK2 = k5_xboole_0(k2_struct_0(sK0),sK1))) | (sK2 = k5_xboole_0(k2_struct_0(sK0),sK1)))).
% 5.51/1.11  
% 5.51/1.11  tff(u2341,axiom,
% 5.51/1.11      (![X1, X0] : ((~r1_xboole_0(X0,X1) | (k4_xboole_0(k2_xboole_0(X0,X1),X1) = X0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2340,axiom,
% 5.51/1.11      (![X1, X0] : ((~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2339,negated_conjecture,
% 5.51/1.11      ((~r1_xboole_0(sK1,sK2)) | r1_xboole_0(sK1,sK2))).
% 5.51/1.11  
% 5.51/1.11  tff(u2338,negated_conjecture,
% 5.51/1.11      ((~r1_xboole_0(sK2,sK1)) | r1_xboole_0(sK2,sK1))).
% 5.51/1.11  
% 5.51/1.11  tff(u2337,axiom,
% 5.51/1.11      (![X1, X0] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k2_xboole_0(X1,X0) = k4_subset_1(X0,X1,X0)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2336,axiom,
% 5.51/1.11      (![X1, X0, X2] : ((~m1_subset_1(X2,k1_zfmisc_1(X0)) | (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2335,axiom,
% 5.51/1.11      (![X1, X0, X2] : ((~m1_subset_1(X1,k1_zfmisc_1(X0)) | (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2334,negated_conjecture,
% 5.51/1.11      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X1] : ((~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),X1,sK1) = k2_xboole_0(X1,sK1))))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2333,negated_conjecture,
% 5.51/1.11      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | (![X0] : ((~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | (k4_subset_1(u1_struct_0(sK0),X0,sK2) = k2_xboole_0(X0,sK2))))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2332,negated_conjecture,
% 5.51/1.11      ((~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2331,negated_conjecture,
% 5.51/1.11      ((~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) | m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))).
% 5.51/1.11  
% 5.51/1.11  tff(u2330,axiom,
% 5.51/1.11      (![X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))))).
% 5.51/1.11  
% 5.51/1.11  % (423)# SZS output end Saturation.
% 5.51/1.11  % (423)------------------------------
% 5.51/1.11  % (423)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.51/1.11  % (423)Termination reason: Satisfiable
% 5.51/1.11  
% 5.51/1.11  % (423)Memory used [KB]: 7419
% 5.51/1.11  % (423)Time elapsed: 0.318 s
% 5.51/1.11  % (423)------------------------------
% 5.51/1.11  % (423)------------------------------
% 5.51/1.11  % (32709)Success in time 0.73 s
%------------------------------------------------------------------------------
