%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:52 EST 2020

% Result     : Theorem 2.20s
% Output     : Refutation 2.20s
% Verified   : 
% Statistics : Number of formulae       :   97 ( 152 expanded)
%              Number of leaves         :   28 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  218 ( 333 expanded)
%              Number of equality atoms :   69 ( 115 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2818,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f55,f59,f74,f78,f82,f86,f144,f170,f262,f413,f2580,f2747,f2817])).

fof(f2817,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_74
    | ~ spl2_79 ),
    inference(avatar_contradiction_clause,[],[f2816])).

fof(f2816,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_74
    | ~ spl2_79 ),
    inference(subsumption_resolution,[],[f30,f2815])).

fof(f2815,plain,
    ( ! [X80,X81] : k2_xboole_0(X80,X81) = k5_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81))
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_74
    | ~ spl2_79 ),
    inference(forward_demodulation,[],[f2814,f2795])).

fof(f2795,plain,
    ( ! [X14,X13] : k2_xboole_0(X13,X14) = k2_xboole_0(X13,k5_xboole_0(X13,X14))
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_79 ),
    inference(forward_demodulation,[],[f2794,f77])).

fof(f77,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_10
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f2794,plain,
    ( ! [X14,X13] : k2_xboole_0(k5_xboole_0(X13,X14),k3_xboole_0(X13,X14)) = k2_xboole_0(X13,k5_xboole_0(X13,X14))
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_79 ),
    inference(forward_demodulation,[],[f2762,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2762,plain,
    ( ! [X14,X13] : k2_xboole_0(k5_xboole_0(X13,X14),k3_xboole_0(X13,X14)) = k2_xboole_0(k5_xboole_0(X13,X14),X13)
    | ~ spl2_8
    | ~ spl2_79 ),
    inference(superposition,[],[f58,f2746])).

fof(f2746,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3))
    | ~ spl2_79 ),
    inference(avatar_component_clause,[],[f2745])).

fof(f2745,plain,
    ( spl2_79
  <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).

fof(f58,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl2_8
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f2814,plain,
    ( ! [X80,X81] : k5_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81)) = k2_xboole_0(X80,k5_xboole_0(X80,X81))
    | ~ spl2_4
    | ~ spl2_74
    | ~ spl2_79 ),
    inference(forward_demodulation,[],[f2789,f42])).

fof(f2789,plain,
    ( ! [X80,X81] : k2_xboole_0(k5_xboole_0(X80,X81),X80) = k5_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81))
    | ~ spl2_74
    | ~ spl2_79 ),
    inference(superposition,[],[f2579,f2746])).

fof(f2579,plain,
    ( ! [X12,X11] : k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(X12,X11)
    | ~ spl2_74 ),
    inference(avatar_component_clause,[],[f2578])).

fof(f2578,plain,
    ( spl2_74
  <=> ! [X11,X12] : k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(X12,X11) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).

fof(f30,plain,
    ( k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f2747,plain,
    ( spl2_79
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f450,f411,f168,f72,f45,f2745])).

fof(f45,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f72,plain,
    ( spl2_9
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f168,plain,
    ( spl2_15
  <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f411,plain,
    ( spl2_27
  <=> ! [X3,X5,X4] : k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,X4),X5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f450,plain,
    ( ! [X2,X3] : k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3))
    | ~ spl2_5
    | ~ spl2_9
    | ~ spl2_15
    | ~ spl2_27 ),
    inference(forward_demodulation,[],[f423,f247])).

fof(f247,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0))
    | ~ spl2_5
    | ~ spl2_15 ),
    inference(unit_resulting_resolution,[],[f169,f46])).

fof(f46,plain,
    ( ! [X0,X1] :
        ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f45])).

fof(f169,plain,
    ( ! [X0,X1] : r1_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f168])).

fof(f423,plain,
    ( ! [X2,X3] : k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k5_xboole_0(X2,X3))
    | ~ spl2_9
    | ~ spl2_27 ),
    inference(superposition,[],[f412,f73])).

fof(f73,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f72])).

fof(f412,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,X4),X5)
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f411])).

fof(f2580,plain,
    ( spl2_74
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f288,f260,f142,f57,f41,f2578])).

fof(f142,plain,
    ( spl2_14
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f260,plain,
    ( spl2_20
  <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f288,plain,
    ( ! [X12,X11] : k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(X12,X11)
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f287,f58])).

fof(f287,plain,
    ( ! [X12,X11] : k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(X12,k4_xboole_0(X11,X12))
    | ~ spl2_4
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f286,f42])).

fof(f286,plain,
    ( ! [X12,X11] : k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X12),X12)
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(forward_demodulation,[],[f268,f58])).

fof(f268,plain,
    ( ! [X12,X11] : k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k4_xboole_0(X11,X12)))
    | ~ spl2_14
    | ~ spl2_20 ),
    inference(superposition,[],[f261,f143])).

fof(f143,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f142])).

fof(f261,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3)
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f260])).

fof(f413,plain,
    ( spl2_27
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f107,f80,f53,f411])).

fof(f53,plain,
    ( spl2_7
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f80,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f107,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,X4),X5)
    | ~ spl2_7
    | ~ spl2_11 ),
    inference(superposition,[],[f81,f54])).

fof(f54,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f53])).

fof(f81,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f80])).

fof(f262,plain,
    ( spl2_20
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f91,f72,f41,f260])).

fof(f91,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(superposition,[],[f73,f42])).

fof(f170,plain,
    ( spl2_15
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f124,f84,f37,f168])).

fof(f37,plain,
    ( spl2_3
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f84,plain,
    ( spl2_12
  <=> ! [X5,X4] : r1_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f124,plain,
    ( ! [X0,X1] : r1_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1))
    | ~ spl2_3
    | ~ spl2_12 ),
    inference(superposition,[],[f85,f38])).

fof(f38,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f85,plain,
    ( ! [X4,X5] : r1_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f84])).

fof(f144,plain,
    ( spl2_14
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f60,f45,f33,f142])).

fof(f33,plain,
    ( spl2_2
  <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f60,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_2
    | ~ spl2_5 ),
    inference(unit_resulting_resolution,[],[f34,f46])).

fof(f34,plain,
    ( ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f86,plain,
    ( spl2_12
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f68,f53,f33,f84])).

fof(f68,plain,
    ( ! [X4,X5] : r1_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5))
    | ~ spl2_2
    | ~ spl2_7 ),
    inference(superposition,[],[f34,f54])).

fof(f82,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f26,f80])).

fof(f26,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f78,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f23,f76])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

fof(f74,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f22,f72])).

fof(f22,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f59,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f21,f57])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f55,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f20,f53])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f47,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f24,f45])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = X0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f43,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f19,f41])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f39,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f17,f33])).

fof(f17,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f31,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f16,f28])).

fof(f16,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:21:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.44  % (28053)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.46  % (28051)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.46  % (28045)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.48  % (28044)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.48  % (28055)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.48  % (28047)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (28057)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.49  % (28048)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.49  % (28050)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.49  % (28043)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.49  % (28052)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.49  % (28054)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (28054)Refutation not found, incomplete strategy% (28054)------------------------------
% 0.22/0.50  % (28054)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (28054)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (28054)Memory used [KB]: 10490
% 0.22/0.50  % (28054)Time elapsed: 0.081 s
% 0.22/0.50  % (28054)------------------------------
% 0.22/0.50  % (28054)------------------------------
% 0.22/0.50  % (28049)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.50  % (28060)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (28046)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.51  % (28056)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.51  % (28059)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.51  % (28058)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.20/0.64  % (28048)Refutation found. Thanks to Tanya!
% 2.20/0.64  % SZS status Theorem for theBenchmark
% 2.20/0.64  % SZS output start Proof for theBenchmark
% 2.20/0.64  fof(f2818,plain,(
% 2.20/0.64    $false),
% 2.20/0.64    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f47,f55,f59,f74,f78,f82,f86,f144,f170,f262,f413,f2580,f2747,f2817])).
% 2.20/0.64  fof(f2817,plain,(
% 2.20/0.64    spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_10 | ~spl2_74 | ~spl2_79),
% 2.20/0.64    inference(avatar_contradiction_clause,[],[f2816])).
% 2.20/0.64  fof(f2816,plain,(
% 2.20/0.64    $false | (spl2_1 | ~spl2_4 | ~spl2_8 | ~spl2_10 | ~spl2_74 | ~spl2_79)),
% 2.20/0.64    inference(subsumption_resolution,[],[f30,f2815])).
% 2.20/0.64  fof(f2815,plain,(
% 2.20/0.64    ( ! [X80,X81] : (k2_xboole_0(X80,X81) = k5_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81))) ) | (~spl2_4 | ~spl2_8 | ~spl2_10 | ~spl2_74 | ~spl2_79)),
% 2.20/0.64    inference(forward_demodulation,[],[f2814,f2795])).
% 2.20/0.64  fof(f2795,plain,(
% 2.20/0.64    ( ! [X14,X13] : (k2_xboole_0(X13,X14) = k2_xboole_0(X13,k5_xboole_0(X13,X14))) ) | (~spl2_4 | ~spl2_8 | ~spl2_10 | ~spl2_79)),
% 2.20/0.64    inference(forward_demodulation,[],[f2794,f77])).
% 2.20/0.64  fof(f77,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_10),
% 2.20/0.64    inference(avatar_component_clause,[],[f76])).
% 2.20/0.64  fof(f76,plain,(
% 2.20/0.64    spl2_10 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.20/0.64  fof(f2794,plain,(
% 2.20/0.64    ( ! [X14,X13] : (k2_xboole_0(k5_xboole_0(X13,X14),k3_xboole_0(X13,X14)) = k2_xboole_0(X13,k5_xboole_0(X13,X14))) ) | (~spl2_4 | ~spl2_8 | ~spl2_79)),
% 2.20/0.64    inference(forward_demodulation,[],[f2762,f42])).
% 2.20/0.64  fof(f42,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_4),
% 2.20/0.64    inference(avatar_component_clause,[],[f41])).
% 2.20/0.64  fof(f41,plain,(
% 2.20/0.64    spl2_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.20/0.64  fof(f2762,plain,(
% 2.20/0.64    ( ! [X14,X13] : (k2_xboole_0(k5_xboole_0(X13,X14),k3_xboole_0(X13,X14)) = k2_xboole_0(k5_xboole_0(X13,X14),X13)) ) | (~spl2_8 | ~spl2_79)),
% 2.20/0.64    inference(superposition,[],[f58,f2746])).
% 2.20/0.64  fof(f2746,plain,(
% 2.20/0.64    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3))) ) | ~spl2_79),
% 2.20/0.64    inference(avatar_component_clause,[],[f2745])).
% 2.20/0.64  fof(f2745,plain,(
% 2.20/0.64    spl2_79 <=> ! [X3,X2] : k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_79])])).
% 2.20/0.64  fof(f58,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_8),
% 2.20/0.64    inference(avatar_component_clause,[],[f57])).
% 2.20/0.64  fof(f57,plain,(
% 2.20/0.64    spl2_8 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 2.20/0.64  fof(f2814,plain,(
% 2.20/0.64    ( ! [X80,X81] : (k5_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81)) = k2_xboole_0(X80,k5_xboole_0(X80,X81))) ) | (~spl2_4 | ~spl2_74 | ~spl2_79)),
% 2.20/0.64    inference(forward_demodulation,[],[f2789,f42])).
% 2.20/0.64  fof(f2789,plain,(
% 2.20/0.64    ( ! [X80,X81] : (k2_xboole_0(k5_xboole_0(X80,X81),X80) = k5_xboole_0(k5_xboole_0(X80,X81),k3_xboole_0(X80,X81))) ) | (~spl2_74 | ~spl2_79)),
% 2.20/0.64    inference(superposition,[],[f2579,f2746])).
% 2.20/0.64  fof(f2579,plain,(
% 2.20/0.64    ( ! [X12,X11] : (k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(X12,X11)) ) | ~spl2_74),
% 2.20/0.64    inference(avatar_component_clause,[],[f2578])).
% 2.20/0.64  fof(f2578,plain,(
% 2.20/0.64    spl2_74 <=> ! [X11,X12] : k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(X12,X11)),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_74])])).
% 2.20/0.64  fof(f30,plain,(
% 2.20/0.64    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) | spl2_1),
% 2.20/0.64    inference(avatar_component_clause,[],[f28])).
% 2.20/0.64  fof(f28,plain,(
% 2.20/0.64    spl2_1 <=> k2_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.20/0.64  fof(f2747,plain,(
% 2.20/0.64    spl2_79 | ~spl2_5 | ~spl2_9 | ~spl2_15 | ~spl2_27),
% 2.20/0.64    inference(avatar_split_clause,[],[f450,f411,f168,f72,f45,f2745])).
% 2.20/0.64  fof(f45,plain,(
% 2.20/0.64    spl2_5 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.20/0.64  fof(f72,plain,(
% 2.20/0.64    spl2_9 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 2.20/0.64  fof(f168,plain,(
% 2.20/0.64    spl2_15 <=> ! [X1,X0] : r1_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 2.20/0.64  fof(f411,plain,(
% 2.20/0.64    spl2_27 <=> ! [X3,X5,X4] : k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,X4),X5)),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 2.20/0.64  fof(f450,plain,(
% 2.20/0.64    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k4_xboole_0(X2,k5_xboole_0(X2,X3))) ) | (~spl2_5 | ~spl2_9 | ~spl2_15 | ~spl2_27)),
% 2.20/0.64    inference(forward_demodulation,[],[f423,f247])).
% 2.20/0.64  fof(f247,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ) | (~spl2_5 | ~spl2_15)),
% 2.20/0.64    inference(unit_resulting_resolution,[],[f169,f46])).
% 2.20/0.64  fof(f46,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) ) | ~spl2_5),
% 2.20/0.64    inference(avatar_component_clause,[],[f45])).
% 2.20/0.64  fof(f169,plain,(
% 2.20/0.64    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ) | ~spl2_15),
% 2.20/0.64    inference(avatar_component_clause,[],[f168])).
% 2.20/0.64  fof(f423,plain,(
% 2.20/0.64    ( ! [X2,X3] : (k4_xboole_0(k3_xboole_0(X2,X3),k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k5_xboole_0(X2,X3))) ) | (~spl2_9 | ~spl2_27)),
% 2.20/0.64    inference(superposition,[],[f412,f73])).
% 2.20/0.64  fof(f73,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ) | ~spl2_9),
% 2.20/0.64    inference(avatar_component_clause,[],[f72])).
% 2.20/0.64  fof(f412,plain,(
% 2.20/0.64    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,X4),X5)) ) | ~spl2_27),
% 2.20/0.64    inference(avatar_component_clause,[],[f411])).
% 2.20/0.64  fof(f2580,plain,(
% 2.20/0.64    spl2_74 | ~spl2_4 | ~spl2_8 | ~spl2_14 | ~spl2_20),
% 2.20/0.64    inference(avatar_split_clause,[],[f288,f260,f142,f57,f41,f2578])).
% 2.20/0.64  fof(f142,plain,(
% 2.20/0.64    spl2_14 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 2.20/0.64  fof(f260,plain,(
% 2.20/0.64    spl2_20 <=> ! [X3,X2] : k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3)),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 2.20/0.64  fof(f288,plain,(
% 2.20/0.64    ( ! [X12,X11] : (k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(X12,X11)) ) | (~spl2_4 | ~spl2_8 | ~spl2_14 | ~spl2_20)),
% 2.20/0.64    inference(forward_demodulation,[],[f287,f58])).
% 2.20/0.64  fof(f287,plain,(
% 2.20/0.64    ( ! [X12,X11] : (k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(X12,k4_xboole_0(X11,X12))) ) | (~spl2_4 | ~spl2_8 | ~spl2_14 | ~spl2_20)),
% 2.20/0.64    inference(forward_demodulation,[],[f286,f42])).
% 2.20/0.64  fof(f286,plain,(
% 2.20/0.64    ( ! [X12,X11] : (k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X12),X12)) ) | (~spl2_8 | ~spl2_14 | ~spl2_20)),
% 2.20/0.64    inference(forward_demodulation,[],[f268,f58])).
% 2.20/0.64  fof(f268,plain,(
% 2.20/0.64    ( ! [X12,X11] : (k5_xboole_0(X12,k4_xboole_0(X11,X12)) = k2_xboole_0(k4_xboole_0(X11,X12),k4_xboole_0(X12,k4_xboole_0(X11,X12)))) ) | (~spl2_14 | ~spl2_20)),
% 2.20/0.64    inference(superposition,[],[f261,f143])).
% 2.20/0.64  fof(f143,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl2_14),
% 2.20/0.64    inference(avatar_component_clause,[],[f142])).
% 2.20/0.64  fof(f261,plain,(
% 2.20/0.64    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3)) ) | ~spl2_20),
% 2.20/0.64    inference(avatar_component_clause,[],[f260])).
% 2.20/0.64  fof(f413,plain,(
% 2.20/0.64    spl2_27 | ~spl2_7 | ~spl2_11),
% 2.20/0.64    inference(avatar_split_clause,[],[f107,f80,f53,f411])).
% 2.20/0.64  fof(f53,plain,(
% 2.20/0.64    spl2_7 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.20/0.64  fof(f80,plain,(
% 2.20/0.64    spl2_11 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 2.20/0.64  fof(f107,plain,(
% 2.20/0.64    ( ! [X4,X5,X3] : (k4_xboole_0(X3,k2_xboole_0(k4_xboole_0(X3,X4),X5)) = k4_xboole_0(k3_xboole_0(X3,X4),X5)) ) | (~spl2_7 | ~spl2_11)),
% 2.20/0.64    inference(superposition,[],[f81,f54])).
% 2.20/0.64  fof(f54,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_7),
% 2.20/0.64    inference(avatar_component_clause,[],[f53])).
% 2.20/0.64  fof(f81,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_11),
% 2.20/0.64    inference(avatar_component_clause,[],[f80])).
% 2.20/0.64  fof(f262,plain,(
% 2.20/0.64    spl2_20 | ~spl2_4 | ~spl2_9),
% 2.20/0.64    inference(avatar_split_clause,[],[f91,f72,f41,f260])).
% 2.20/0.64  fof(f91,plain,(
% 2.20/0.64    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X3,X2),k4_xboole_0(X2,X3)) = k5_xboole_0(X2,X3)) ) | (~spl2_4 | ~spl2_9)),
% 2.20/0.64    inference(superposition,[],[f73,f42])).
% 2.20/0.64  fof(f170,plain,(
% 2.20/0.64    spl2_15 | ~spl2_3 | ~spl2_12),
% 2.20/0.64    inference(avatar_split_clause,[],[f124,f84,f37,f168])).
% 2.20/0.64  fof(f37,plain,(
% 2.20/0.64    spl2_3 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.20/0.64  fof(f84,plain,(
% 2.20/0.64    spl2_12 <=> ! [X5,X4] : r1_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5))),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 2.20/0.64  fof(f124,plain,(
% 2.20/0.64    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),k4_xboole_0(X0,X1))) ) | (~spl2_3 | ~spl2_12)),
% 2.20/0.64    inference(superposition,[],[f85,f38])).
% 2.20/0.64  fof(f38,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_3),
% 2.20/0.64    inference(avatar_component_clause,[],[f37])).
% 2.20/0.64  fof(f85,plain,(
% 2.20/0.64    ( ! [X4,X5] : (r1_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5))) ) | ~spl2_12),
% 2.20/0.64    inference(avatar_component_clause,[],[f84])).
% 2.20/0.64  fof(f144,plain,(
% 2.20/0.64    spl2_14 | ~spl2_2 | ~spl2_5),
% 2.20/0.64    inference(avatar_split_clause,[],[f60,f45,f33,f142])).
% 2.20/0.64  fof(f33,plain,(
% 2.20/0.64    spl2_2 <=> ! [X1,X0] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.20/0.64    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.20/0.64  fof(f60,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k4_xboole_0(X0,X1),X1)) ) | (~spl2_2 | ~spl2_5)),
% 2.20/0.64    inference(unit_resulting_resolution,[],[f34,f46])).
% 2.20/0.64  fof(f34,plain,(
% 2.20/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) ) | ~spl2_2),
% 2.20/0.64    inference(avatar_component_clause,[],[f33])).
% 2.20/0.64  fof(f86,plain,(
% 2.20/0.64    spl2_12 | ~spl2_2 | ~spl2_7),
% 2.20/0.64    inference(avatar_split_clause,[],[f68,f53,f33,f84])).
% 2.20/0.64  fof(f68,plain,(
% 2.20/0.64    ( ! [X4,X5] : (r1_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5))) ) | (~spl2_2 | ~spl2_7)),
% 2.20/0.64    inference(superposition,[],[f34,f54])).
% 2.20/0.64  fof(f82,plain,(
% 2.20/0.64    spl2_11),
% 2.20/0.64    inference(avatar_split_clause,[],[f26,f80])).
% 2.20/0.64  fof(f26,plain,(
% 2.20/0.64    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 2.20/0.64    inference(cnf_transformation,[],[f5])).
% 2.20/0.64  fof(f5,axiom,(
% 2.20/0.64    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 2.20/0.64  fof(f78,plain,(
% 2.20/0.64    spl2_10),
% 2.20/0.64    inference(avatar_split_clause,[],[f23,f76])).
% 2.20/0.64  fof(f23,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.20/0.64    inference(cnf_transformation,[],[f9])).
% 2.20/0.64  fof(f9,axiom,(
% 2.20/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).
% 2.20/0.64  fof(f74,plain,(
% 2.20/0.64    spl2_9),
% 2.20/0.64    inference(avatar_split_clause,[],[f22,f72])).
% 2.20/0.64  fof(f22,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 2.20/0.64    inference(cnf_transformation,[],[f3])).
% 2.20/0.64  fof(f3,axiom,(
% 2.20/0.64    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 2.20/0.64  fof(f59,plain,(
% 2.20/0.64    spl2_8),
% 2.20/0.64    inference(avatar_split_clause,[],[f21,f57])).
% 2.20/0.64  fof(f21,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.20/0.64    inference(cnf_transformation,[],[f4])).
% 2.20/0.64  fof(f4,axiom,(
% 2.20/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.20/0.64  fof(f55,plain,(
% 2.20/0.64    spl2_7),
% 2.20/0.64    inference(avatar_split_clause,[],[f20,f53])).
% 2.20/0.64  fof(f20,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.20/0.64    inference(cnf_transformation,[],[f6])).
% 2.20/0.64  fof(f6,axiom,(
% 2.20/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.20/0.64  fof(f47,plain,(
% 2.20/0.64    spl2_5),
% 2.20/0.64    inference(avatar_split_clause,[],[f24,f45])).
% 2.20/0.64  fof(f24,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f15])).
% 2.20/0.64  fof(f15,plain,(
% 2.20/0.64    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.20/0.64    inference(nnf_transformation,[],[f8])).
% 2.20/0.64  fof(f8,axiom,(
% 2.20/0.64    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.20/0.64  fof(f43,plain,(
% 2.20/0.64    spl2_4),
% 2.20/0.64    inference(avatar_split_clause,[],[f19,f41])).
% 2.20/0.64  fof(f19,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f1])).
% 2.20/0.64  fof(f1,axiom,(
% 2.20/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.20/0.64  fof(f39,plain,(
% 2.20/0.64    spl2_3),
% 2.20/0.64    inference(avatar_split_clause,[],[f18,f37])).
% 2.20/0.64  fof(f18,plain,(
% 2.20/0.64    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f2])).
% 2.20/0.64  fof(f2,axiom,(
% 2.20/0.64    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.20/0.64  fof(f35,plain,(
% 2.20/0.64    spl2_2),
% 2.20/0.64    inference(avatar_split_clause,[],[f17,f33])).
% 2.20/0.64  fof(f17,plain,(
% 2.20/0.64    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.20/0.64    inference(cnf_transformation,[],[f7])).
% 2.20/0.64  fof(f7,axiom,(
% 2.20/0.64    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.20/0.64  fof(f31,plain,(
% 2.20/0.64    ~spl2_1),
% 2.20/0.64    inference(avatar_split_clause,[],[f16,f28])).
% 2.20/0.64  fof(f16,plain,(
% 2.20/0.64    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.20/0.64    inference(cnf_transformation,[],[f14])).
% 2.20/0.64  fof(f14,plain,(
% 2.20/0.64    k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.20/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 2.20/0.64  fof(f13,plain,(
% 2.20/0.64    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 2.20/0.64    introduced(choice_axiom,[])).
% 2.20/0.64  fof(f12,plain,(
% 2.20/0.64    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.20/0.64    inference(ennf_transformation,[],[f11])).
% 2.20/0.64  fof(f11,negated_conjecture,(
% 2.20/0.64    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.20/0.64    inference(negated_conjecture,[],[f10])).
% 2.20/0.64  fof(f10,conjecture,(
% 2.20/0.64    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 2.20/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).
% 2.20/0.64  % SZS output end Proof for theBenchmark
% 2.20/0.64  % (28048)------------------------------
% 2.20/0.64  % (28048)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.64  % (28048)Termination reason: Refutation
% 2.20/0.64  
% 2.20/0.64  % (28048)Memory used [KB]: 8827
% 2.20/0.64  % (28048)Time elapsed: 0.211 s
% 2.20/0.64  % (28048)------------------------------
% 2.20/0.64  % (28048)------------------------------
% 2.20/0.64  % (28042)Success in time 0.278 s
%------------------------------------------------------------------------------
