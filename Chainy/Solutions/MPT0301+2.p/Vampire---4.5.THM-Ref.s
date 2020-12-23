%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0301+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:09:22 EST 2020

% Result     : Theorem 2.46s
% Output     : Refutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 209 expanded)
%              Number of leaves         :   24 (  74 expanded)
%              Depth                    :   12
%              Number of atoms          :  415 ( 762 expanded)
%              Number of equality atoms :  131 ( 304 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5521,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f1829,f1834,f1835,f2417,f2437,f4887,f4924,f5492,f5506,f5520])).

fof(f5520,plain,
    ( spl45_3
    | ~ spl45_8 ),
    inference(avatar_contradiction_clause,[],[f5519])).

fof(f5519,plain,
    ( $false
    | spl45_3
    | ~ spl45_8 ),
    inference(subsumption_resolution,[],[f5508,f1833])).

fof(f1833,plain,
    ( o_0_0_xboole_0 != sK2
    | spl45_3 ),
    inference(avatar_component_clause,[],[f1831])).

fof(f1831,plain,
    ( spl45_3
  <=> o_0_0_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_3])])).

fof(f5508,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl45_8 ),
    inference(resolution,[],[f5488,f1370])).

fof(f1370,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f787,f753])).

fof(f753,plain,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

fof(f787,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f598])).

fof(f598,plain,(
    ! [X0] :
      ( r2_hidden(sK5(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f414,f597])).

fof(f597,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK5(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f414,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f36])).

fof(f36,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f5488,plain,
    ( ! [X10] : ~ r2_hidden(X10,sK2)
    | ~ spl45_8 ),
    inference(avatar_component_clause,[],[f5487])).

fof(f5487,plain,
    ( spl45_8
  <=> ! [X10] : ~ r2_hidden(X10,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_8])])).

fof(f5506,plain,
    ( spl45_2
    | ~ spl45_9 ),
    inference(avatar_contradiction_clause,[],[f5505])).

fof(f5505,plain,
    ( $false
    | spl45_2
    | ~ spl45_9 ),
    inference(subsumption_resolution,[],[f5494,f1828])).

fof(f1828,plain,
    ( o_0_0_xboole_0 != sK3
    | spl45_2 ),
    inference(avatar_component_clause,[],[f1826])).

fof(f1826,plain,
    ( spl45_2
  <=> o_0_0_xboole_0 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_2])])).

fof(f5494,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl45_9 ),
    inference(resolution,[],[f5491,f1370])).

fof(f5491,plain,
    ( ! [X11] : ~ r2_hidden(X11,sK3)
    | ~ spl45_9 ),
    inference(avatar_component_clause,[],[f5490])).

fof(f5490,plain,
    ( spl45_9
  <=> ! [X11] : ~ r2_hidden(X11,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_9])])).

fof(f5492,plain,
    ( spl45_8
    | spl45_9
    | ~ spl45_1
    | ~ spl45_7 ),
    inference(avatar_split_clause,[],[f5485,f2415,f1822,f5490,f5487])).

fof(f1822,plain,
    ( spl45_1
  <=> o_0_0_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_1])])).

fof(f2415,plain,
    ( spl45_7
  <=> ! [X8] : ~ r2_hidden(X8,o_0_0_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_7])])).

fof(f5485,plain,
    ( ! [X10,X11] :
        ( ~ r2_hidden(X11,sK3)
        | ~ r2_hidden(X10,sK2) )
    | ~ spl45_1
    | ~ spl45_7 ),
    inference(subsumption_resolution,[],[f5484,f2416])).

fof(f2416,plain,
    ( ! [X8] : ~ r2_hidden(X8,o_0_0_xboole_0)
    | ~ spl45_7 ),
    inference(avatar_component_clause,[],[f2415])).

fof(f5484,plain,
    ( ! [X10,X11] :
        ( r2_hidden(k4_tarski(X10,X11),o_0_0_xboole_0)
        | ~ r2_hidden(X11,sK3)
        | ~ r2_hidden(X10,sK2) )
    | ~ spl45_1 ),
    inference(superposition,[],[f1221,f1823])).

fof(f1823,plain,
    ( o_0_0_xboole_0 = k2_zfmisc_1(sK2,sK3)
    | ~ spl45_1 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f1221,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
      | ~ r2_hidden(X1,X3)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f723])).

fof(f723,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f722])).

fof(f722,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f316])).

fof(f316,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_zfmisc_1)).

fof(f4924,plain,
    ( spl45_1
    | ~ spl45_3
    | ~ spl45_7 ),
    inference(avatar_contradiction_clause,[],[f4923])).

fof(f4923,plain,
    ( $false
    | spl45_1
    | ~ spl45_3
    | ~ spl45_7 ),
    inference(trivial_inequality_removal,[],[f4920])).

fof(f4920,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | spl45_1
    | ~ spl45_3
    | ~ spl45_7 ),
    inference(superposition,[],[f4888,f4856])).

fof(f4856,plain,
    ( ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(o_0_0_xboole_0,X1)
    | ~ spl45_7 ),
    inference(resolution,[],[f4838,f1370])).

fof(f4838,plain,
    ( ! [X14,X15] : ~ r2_hidden(X14,k2_zfmisc_1(o_0_0_xboole_0,X15))
    | ~ spl45_7 ),
    inference(resolution,[],[f1757,f2416])).

fof(f1757,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK28(X0,X1,X8),X0)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1077])).

fof(f1077,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK28(X0,X1,X8),X0)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f672])).

fof(f672,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != sK25(X0,X1,X2)
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(sK25(X0,X1,X2),X2) )
          & ( ( sK25(X0,X1,X2) = k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2))
              & r2_hidden(sK27(X0,X1,X2),X1)
              & r2_hidden(sK26(X0,X1,X2),X0) )
            | r2_hidden(sK25(X0,X1,X2),X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ( k4_tarski(sK28(X0,X1,X8),sK29(X0,X1,X8)) = X8
                & r2_hidden(sK29(X0,X1,X8),X1)
                & r2_hidden(sK28(X0,X1,X8),X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK25,sK26,sK27,sK28,sK29])],[f668,f671,f670,f669])).

fof(f669,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4,X5] :
                ( k4_tarski(X4,X5) != X3
                | ~ r2_hidden(X5,X1)
                | ~ r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X6,X7] :
                ( k4_tarski(X6,X7) = X3
                & r2_hidden(X7,X1)
                & r2_hidden(X6,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X5,X4] :
              ( k4_tarski(X4,X5) != sK25(X0,X1,X2)
              | ~ r2_hidden(X5,X1)
              | ~ r2_hidden(X4,X0) )
          | ~ r2_hidden(sK25(X0,X1,X2),X2) )
        & ( ? [X7,X6] :
              ( k4_tarski(X6,X7) = sK25(X0,X1,X2)
              & r2_hidden(X7,X1)
              & r2_hidden(X6,X0) )
          | r2_hidden(sK25(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f670,plain,(
    ! [X2,X1,X0] :
      ( ? [X7,X6] :
          ( k4_tarski(X6,X7) = sK25(X0,X1,X2)
          & r2_hidden(X7,X1)
          & r2_hidden(X6,X0) )
     => ( sK25(X0,X1,X2) = k4_tarski(sK26(X0,X1,X2),sK27(X0,X1,X2))
        & r2_hidden(sK27(X0,X1,X2),X1)
        & r2_hidden(sK26(X0,X1,X2),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f671,plain,(
    ! [X8,X1,X0] :
      ( ? [X11,X12] :
          ( k4_tarski(X11,X12) = X8
          & r2_hidden(X12,X1)
          & r2_hidden(X11,X0) )
     => ( k4_tarski(sK28(X0,X1,X8),sK29(X0,X1,X8)) = X8
        & r2_hidden(sK29(X0,X1,X8),X1)
        & r2_hidden(sK28(X0,X1,X8),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f668,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X6,X7] :
                  ( k4_tarski(X6,X7) = X3
                  & r2_hidden(X7,X1)
                  & r2_hidden(X6,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X8] :
            ( ( r2_hidden(X8,X2)
              | ! [X9,X10] :
                  ( k4_tarski(X9,X10) != X8
                  | ~ r2_hidden(X10,X1)
                  | ~ r2_hidden(X9,X0) ) )
            & ( ? [X11,X12] :
                  ( k4_tarski(X11,X12) = X8
                  & r2_hidden(X12,X1)
                  & r2_hidden(X11,X0) )
              | ~ r2_hidden(X8,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f667])).

fof(f667,plain,(
    ! [X0,X1,X2] :
      ( ( k2_zfmisc_1(X0,X1) = X2
        | ? [X3] :
            ( ( ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ! [X4,X5] :
                  ( k4_tarski(X4,X5) != X3
                  | ~ r2_hidden(X5,X1)
                  | ~ r2_hidden(X4,X0) ) )
            & ( ? [X4,X5] :
                  ( k4_tarski(X4,X5) = X3
                  & r2_hidden(X5,X1)
                  & r2_hidden(X4,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k2_zfmisc_1(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f285])).

fof(f285,axiom,(
    ! [X0,X1,X2] :
      ( k2_zfmisc_1(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ? [X4,X5] :
              ( k4_tarski(X4,X5) = X3
              & r2_hidden(X5,X1)
              & r2_hidden(X4,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

fof(f4888,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(o_0_0_xboole_0,sK3)
    | spl45_1
    | ~ spl45_3 ),
    inference(forward_demodulation,[],[f1824,f1832])).

fof(f1832,plain,
    ( o_0_0_xboole_0 = sK2
    | ~ spl45_3 ),
    inference(avatar_component_clause,[],[f1831])).

fof(f1824,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK2,sK3)
    | spl45_1 ),
    inference(avatar_component_clause,[],[f1822])).

fof(f4887,plain,
    ( spl45_1
    | ~ spl45_2
    | ~ spl45_7 ),
    inference(avatar_contradiction_clause,[],[f4886])).

fof(f4886,plain,
    ( $false
    | spl45_1
    | ~ spl45_2
    | ~ spl45_7 ),
    inference(subsumption_resolution,[],[f4883,f751])).

fof(f751,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f4883,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | spl45_1
    | ~ spl45_2
    | ~ spl45_7 ),
    inference(trivial_inequality_removal,[],[f4878])).

fof(f4878,plain,
    ( o_0_0_xboole_0 != o_0_0_xboole_0
    | ~ v1_xboole_0(o_0_0_xboole_0)
    | spl45_1
    | ~ spl45_2
    | ~ spl45_7 ),
    inference(superposition,[],[f1852,f4824])).

fof(f4824,plain,
    ( ! [X1] : o_0_0_xboole_0 = k2_zfmisc_1(X1,o_0_0_xboole_0)
    | ~ spl45_7 ),
    inference(resolution,[],[f4808,f1370])).

fof(f4808,plain,
    ( ! [X14,X15] : ~ r2_hidden(X14,k2_zfmisc_1(X15,o_0_0_xboole_0))
    | ~ spl45_7 ),
    inference(resolution,[],[f1756,f2416])).

fof(f1756,plain,(
    ! [X0,X8,X1] :
      ( r2_hidden(sK29(X0,X1,X8),X1)
      | ~ r2_hidden(X8,k2_zfmisc_1(X0,X1)) ) ),
    inference(equality_resolution,[],[f1078])).

fof(f1078,plain,(
    ! [X2,X0,X8,X1] :
      ( r2_hidden(sK29(X0,X1,X8),X1)
      | ~ r2_hidden(X8,X2)
      | k2_zfmisc_1(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f672])).

fof(f1852,plain,
    ( ! [X0] :
        ( k2_zfmisc_1(sK2,X0) != X0
        | ~ v1_xboole_0(X0) )
    | spl45_1
    | ~ spl45_2 ),
    inference(superposition,[],[f1836,f1366])).

fof(f1366,plain,(
    ! [X0] :
      ( o_0_0_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f781,f753])).

fof(f781,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f410])).

fof(f410,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f1836,plain,
    ( o_0_0_xboole_0 != k2_zfmisc_1(sK2,o_0_0_xboole_0)
    | spl45_1
    | ~ spl45_2 ),
    inference(forward_demodulation,[],[f1824,f1827])).

fof(f1827,plain,
    ( o_0_0_xboole_0 = sK3
    | ~ spl45_2 ),
    inference(avatar_component_clause,[],[f1826])).

fof(f2437,plain,(
    ~ spl45_6 ),
    inference(avatar_contradiction_clause,[],[f2418])).

fof(f2418,plain,
    ( $false
    | ~ spl45_6 ),
    inference(resolution,[],[f2413,f1348])).

fof(f1348,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f760,f753])).

fof(f760,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f89])).

fof(f89,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f2413,plain,
    ( ! [X6,X7] : ~ r1_tarski(X6,X7)
    | ~ spl45_6 ),
    inference(avatar_component_clause,[],[f2412])).

fof(f2412,plain,
    ( spl45_6
  <=> ! [X7,X6] : ~ r1_tarski(X6,X7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl45_6])])).

fof(f2417,plain,
    ( spl45_6
    | spl45_7 ),
    inference(avatar_split_clause,[],[f2410,f2415,f2412])).

fof(f2410,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,o_0_0_xboole_0)
      | ~ r1_tarski(X6,X7) ) ),
    inference(subsumption_resolution,[],[f2405,f2382])).

fof(f2382,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,o_0_0_xboole_0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(superposition,[],[f1767,f1350])).

fof(f1350,plain,(
    ! [X0] : o_0_0_xboole_0 = k4_xboole_0(o_0_0_xboole_0,X0) ),
    inference(definition_unfolding,[],[f762,f753,f753])).

fof(f762,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f112])).

fof(f112,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

fof(f1767,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | ~ r2_hidden(X4,X1) ) ),
    inference(equality_resolution,[],[f1098])).

fof(f1098,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ r2_hidden(X4,X1)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f687])).

fof(f687,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ( ( r2_hidden(sK32(X0,X1,X2),X1)
            | ~ r2_hidden(sK32(X0,X1,X2),X0)
            | ~ r2_hidden(sK32(X0,X1,X2),X2) )
          & ( ( ~ r2_hidden(sK32(X0,X1,X2),X1)
              & r2_hidden(sK32(X0,X1,X2),X0) )
            | r2_hidden(sK32(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK32])],[f685,f686])).

fof(f686,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( ~ r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( r2_hidden(sK32(X0,X1,X2),X1)
          | ~ r2_hidden(sK32(X0,X1,X2),X0)
          | ~ r2_hidden(sK32(X0,X1,X2),X2) )
        & ( ( ~ r2_hidden(sK32(X0,X1,X2),X1)
            & r2_hidden(sK32(X0,X1,X2),X0) )
          | r2_hidden(sK32(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f685,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( ~ r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f684])).

fof(f684,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f683])).

fof(f683,plain,(
    ! [X0,X1,X2] :
      ( ( k4_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( ~ r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k4_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f2405,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,o_0_0_xboole_0)
      | r2_hidden(X8,X6)
      | ~ r1_tarski(X6,X7) ) ),
    inference(superposition,[],[f1768,f1470])).

fof(f1470,plain,(
    ! [X0,X1] :
      ( o_0_0_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f944,f753])).

fof(f944,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f644])).

fof(f644,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k4_xboole_0(X0,X1)
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k1_xboole_0 != k4_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f97])).

fof(f97,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k4_xboole_0(X0,X1)
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

fof(f1768,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k4_xboole_0(X0,X1))
      | r2_hidden(X4,X0) ) ),
    inference(equality_resolution,[],[f1097])).

fof(f1097,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X0)
      | ~ r2_hidden(X4,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f687])).

fof(f1835,plain,
    ( spl45_1
    | spl45_3
    | spl45_2 ),
    inference(avatar_split_clause,[],[f1340,f1826,f1831,f1822])).

fof(f1340,plain,
    ( o_0_0_xboole_0 = sK3
    | o_0_0_xboole_0 = sK2
    | o_0_0_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(definition_unfolding,[],[f748,f753,f753,f753])).

fof(f748,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 = sK2
    | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f592])).

fof(f592,plain,
    ( ( ( k1_xboole_0 != sK3
        & k1_xboole_0 != sK2 )
      | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 = sK2
      | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f590,f591])).

fof(f591,plain,
    ( ? [X0,X1] :
        ( ( ( k1_xboole_0 != X1
            & k1_xboole_0 != X0 )
          | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
        & ( k1_xboole_0 = X1
          | k1_xboole_0 = X0
          | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) )
   => ( ( ( k1_xboole_0 != sK3
          & k1_xboole_0 != sK2 )
        | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) )
      & ( k1_xboole_0 = sK3
        | k1_xboole_0 = sK2
        | k1_xboole_0 = k2_zfmisc_1(sK2,sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f590,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f589])).

fof(f589,plain,(
    ? [X0,X1] :
      ( ( ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f408])).

fof(f408,plain,(
    ? [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <~> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(ennf_transformation,[],[f321])).

fof(f321,negated_conjecture,(
    ~ ! [X0,X1] :
        ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      <=> ( k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ),
    inference(negated_conjecture,[],[f320])).

fof(f320,conjecture,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f1834,plain,
    ( ~ spl45_1
    | ~ spl45_3 ),
    inference(avatar_split_clause,[],[f1339,f1831,f1822])).

fof(f1339,plain,
    ( o_0_0_xboole_0 != sK2
    | o_0_0_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(definition_unfolding,[],[f749,f753,f753])).

fof(f749,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f592])).

fof(f1829,plain,
    ( ~ spl45_1
    | ~ spl45_2 ),
    inference(avatar_split_clause,[],[f1338,f1826,f1822])).

fof(f1338,plain,
    ( o_0_0_xboole_0 != sK3
    | o_0_0_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(definition_unfolding,[],[f750,f753,f753])).

fof(f750,plain,
    ( k1_xboole_0 != sK3
    | k1_xboole_0 != k2_zfmisc_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f592])).
%------------------------------------------------------------------------------
