%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:26 EST 2020

% Result     : Theorem 36.43s
% Output     : Refutation 36.43s
% Verified   : 
% Statistics : Number of formulae       :  177 (64046 expanded)
%              Number of leaves         :   15 (22335 expanded)
%              Depth                    :   39
%              Number of atoms          :  284 (75596 expanded)
%              Number of equality atoms :  173 (64042 expanded)
%              Maximal formula depth    :    5 (   4 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f53956,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f63,f53889])).

fof(f53889,plain,
    ( spl2_1
    | ~ spl2_2 ),
    inference(avatar_contradiction_clause,[],[f53888])).

fof(f53888,plain,
    ( $false
    | spl2_1
    | ~ spl2_2 ),
    inference(subsumption_resolution,[],[f43,f53887])).

fof(f53887,plain,
    ( ! [X263,X262] : k5_xboole_0(X262,X263) = k4_xboole_0(k5_xboole_0(X262,k4_xboole_0(X263,X262)),k4_xboole_0(X262,k4_xboole_0(X262,X263)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f53499,f53761])).

fof(f53761,plain,
    ( ! [X24,X25] : k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k4_xboole_0(X24,k5_xboole_0(X24,X25))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f53760,f197])).

fof(f197,plain,(
    ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    inference(superposition,[],[f31,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f31,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f23,f25])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f53760,plain,
    ( ! [X24,X25] : k5_xboole_0(X24,k4_xboole_0(X24,X25)) = k4_xboole_0(X24,k5_xboole_0(X24,X25))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f53414,f44785])).

fof(f44785,plain,
    ( ! [X123,X122] : k4_xboole_0(X122,X123) = k4_xboole_0(k5_xboole_0(X122,X123),k4_xboole_0(X123,X122))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f44782,f563])).

fof(f563,plain,
    ( ! [X4] : k5_xboole_0(k1_xboole_0,X4) = X4
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f545,f345])).

fof(f345,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f51,f344])).

fof(f344,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f324,f19])).

fof(f19,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f324,plain,
    ( ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f83,f321])).

fof(f321,plain,
    ( ! [X1] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f67,f320])).

fof(f320,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f291,f72])).

fof(f72,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_2 ),
    inference(superposition,[],[f67,f31])).

fof(f291,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ),
    inference(superposition,[],[f45,f19])).

fof(f45,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0 ),
    inference(backward_demodulation,[],[f34,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f27,f25,f25])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f34,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f22,f25])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f67,plain,
    ( ! [X1] : k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))
    | ~ spl2_2 ),
    inference(superposition,[],[f64,f31])).

fof(f64,plain,
    ( ! [X0] : k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))
    | ~ spl2_2 ),
    inference(superposition,[],[f26,f62])).

fof(f62,plain,
    ( k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl2_2
  <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f26,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f83,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)) ),
    inference(superposition,[],[f33,f19])).

fof(f33,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f20,f25,f25])).

fof(f20,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    ! [X0] : k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f31,f19])).

fof(f545,plain,
    ( ! [X4] : k5_xboole_0(k1_xboole_0,X4) = k5_xboole_0(X4,k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f350,f349])).

fof(f349,plain,
    ( ! [X3] : k1_xboole_0 = k5_xboole_0(X3,X3)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f215,f344])).

fof(f215,plain,(
    ! [X3] : k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3) ),
    inference(superposition,[],[f31,f181])).

fof(f181,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(superposition,[],[f35,f19])).

fof(f350,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f230,f344])).

fof(f230,plain,(
    ! [X0,X1] : k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(superposition,[],[f26,f215])).

fof(f44782,plain,
    ( ! [X123,X122] : k4_xboole_0(k5_xboole_0(X122,X123),k4_xboole_0(X123,X122)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X122,X123))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f35676,f44579])).

fof(f44579,plain,
    ( ! [X4,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X4,X3))
    | ~ spl2_2 ),
    inference(superposition,[],[f8986,f29036])).

fof(f29036,plain,
    ( ! [X8,X7] : k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8))
    | ~ spl2_2 ),
    inference(superposition,[],[f649,f28499])).

fof(f28499,plain,
    ( ! [X37,X38] : k4_xboole_0(X38,X37) = k5_xboole_0(X37,k5_xboole_0(X38,k4_xboole_0(X37,X38)))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f15811,f28497])).

fof(f28497,plain,
    ( ! [X33,X32] : k4_xboole_0(X32,X33) = k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f28496,f8808])).

fof(f8808,plain,
    ( ! [X10,X8,X9] : k4_xboole_0(X8,X10) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X10)))
    | ~ spl2_2 ),
    inference(superposition,[],[f36,f8522])).

fof(f8522,plain,
    ( ! [X37,X36] : k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36)))) = X36
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8521,f19])).

fof(f8521,plain,
    ( ! [X37,X36] : k4_xboole_0(X36,k1_xboole_0) = k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8520,f345])).

fof(f8520,plain,
    ( ! [X37,X36] : k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36)))) = k5_xboole_0(k4_xboole_0(X36,k1_xboole_0),k1_xboole_0)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8519,f344])).

fof(f8519,plain,
    ( ! [X37,X36] : k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36)))) = k5_xboole_0(k4_xboole_0(X36,k1_xboole_0),k4_xboole_0(X36,X36))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8366,f313])).

fof(f313,plain,(
    ! [X6,X5] : k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5 ),
    inference(superposition,[],[f45,f31])).

fof(f8366,plain,
    ( ! [X37,X36] : k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36)))) = k5_xboole_0(k4_xboole_0(X36,k1_xboole_0),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X37,X36))))
    | ~ spl2_2 ),
    inference(superposition,[],[f2829,f344])).

fof(f2829,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1)))) ),
    inference(backward_demodulation,[],[f47,f2828])).

fof(f2828,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13))))) ),
    inference(forward_demodulation,[],[f2827,f36])).

fof(f2827,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13))))) ),
    inference(forward_demodulation,[],[f2826,f872])).

fof(f872,plain,(
    ! [X4,X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) ),
    inference(forward_demodulation,[],[f822,f191])).

fof(f191,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f35,f33])).

fof(f822,plain,(
    ! [X4,X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4) ),
    inference(superposition,[],[f36,f33])).

fof(f2826,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13))))) ),
    inference(forward_demodulation,[],[f2719,f36])).

fof(f2719,plain,(
    ! [X12,X13,X11] : k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(X11,k4_xboole_0(X11,X13))) ),
    inference(superposition,[],[f39,f35])).

fof(f39,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f30,f25,f25,f25])).

fof(f30,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).

fof(f47,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))))) ),
    inference(forward_demodulation,[],[f38,f36])).

fof(f38,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ),
    inference(definition_unfolding,[],[f29,f25,f22,f22,f25,f25])).

fof(f29,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f28496,plain,
    ( ! [X33,X32] : k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33) = k4_xboole_0(X32,k4_xboole_0(X32,k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f28308,f19])).

fof(f28308,plain,
    ( ! [X33,X32] : k4_xboole_0(X32,k4_xboole_0(X32,k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33),k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f33,f27557])).

fof(f27557,plain,
    ( ! [X118,X117] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X117,k4_xboole_0(X118,X117)),X118),X117)
    | ~ spl2_2 ),
    inference(superposition,[],[f26588,f9197])).

fof(f9197,plain,
    ( ! [X12,X11] : k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k4_xboole_0(X12,X11)) = X11
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f9122,f637])).

fof(f637,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)
    | ~ spl2_2 ),
    inference(superposition,[],[f564,f620])).

fof(f620,plain,
    ( ! [X6,X7] : k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f608,f345])).

fof(f608,plain,
    ( ! [X6,X7] : k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X7,k5_xboole_0(X6,X7))
    | ~ spl2_2 ),
    inference(superposition,[],[f564,f342])).

fof(f342,plain,
    ( ! [X0,X1] : k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f235,f321])).

fof(f235,plain,
    ( ! [X0,X1] : k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f234,f72])).

fof(f234,plain,(
    ! [X0,X1] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(forward_demodulation,[],[f228,f83])).

fof(f228,plain,(
    ! [X0,X1] : k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1))) ),
    inference(superposition,[],[f215,f26])).

fof(f564,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f350,f563])).

fof(f9122,plain,
    ( ! [X12,X11] : k4_xboole_0(k5_xboole_0(k4_xboole_0(X12,X11),X11),k4_xboole_0(X12,X11)) = X11
    | ~ spl2_2 ),
    inference(superposition,[],[f8901,f313])).

fof(f8901,plain,
    ( ! [X17,X18] : k4_xboole_0(X18,X17) = k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8811,f632])).

fof(f632,plain,
    ( ! [X8,X9] : k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8
    | ~ spl2_2 ),
    inference(superposition,[],[f620,f620])).

fof(f8811,plain,
    ( ! [X17,X18] : k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17) = k5_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17)
    | ~ spl2_2 ),
    inference(superposition,[],[f87,f8522])).

fof(f87,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))) ),
    inference(superposition,[],[f31,f33])).

fof(f26588,plain,
    ( ! [X6,X4,X5] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X6)))
    | ~ spl2_2 ),
    inference(superposition,[],[f25482,f1213])).

fof(f1213,plain,
    ( ! [X14,X15,X16] : k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))
    | ~ spl2_2 ),
    inference(superposition,[],[f1185,f313])).

fof(f1185,plain,
    ( ! [X24,X23,X22] : k4_xboole_0(X23,k4_xboole_0(k4_xboole_0(X22,X23),X24)) = X23
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f1137,f19])).

fof(f1137,plain,
    ( ! [X24,X23,X22] : k4_xboole_0(X23,k4_xboole_0(k4_xboole_0(k4_xboole_0(X22,X23),X24),k1_xboole_0)) = X23
    | ~ spl2_2 ),
    inference(superposition,[],[f856,f735])).

fof(f735,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f734,f349])).

fof(f734,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2)) ),
    inference(forward_demodulation,[],[f711,f191])).

fof(f711,plain,(
    ! [X2,X1] : k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1)))) ),
    inference(superposition,[],[f87,f33])).

fof(f856,plain,(
    ! [X24,X23,X25] : k4_xboole_0(X25,k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25)))) = X25 ),
    inference(superposition,[],[f313,f36])).

fof(f25482,plain,
    ( ! [X4,X5,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X5),k4_xboole_0(X3,X5))
    | ~ spl2_2 ),
    inference(superposition,[],[f16406,f872])).

fof(f16406,plain,
    ( ! [X57,X58,X56] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X56,X58))),k4_xboole_0(X57,X58))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f16099,f36])).

fof(f16099,plain,
    ( ! [X57,X58,X56] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X56)),X58),k4_xboole_0(X57,X58))
    | ~ spl2_2 ),
    inference(superposition,[],[f754,f832])).

fof(f832,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2) ),
    inference(superposition,[],[f36,f33])).

fof(f754,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)
    | ~ spl2_2 ),
    inference(superposition,[],[f735,f33])).

fof(f15811,plain,
    ( ! [X37,X38] : k5_xboole_0(X37,k5_xboole_0(X38,k4_xboole_0(X37,X38))) = k4_xboole_0(k5_xboole_0(X38,k4_xboole_0(X37,X38)),X37)
    | ~ spl2_2 ),
    inference(superposition,[],[f1063,f8630])).

fof(f8630,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8629,f727])).

fof(f727,plain,
    ( ! [X6,X7] : k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6
    | ~ spl2_2 ),
    inference(superposition,[],[f620,f87])).

fof(f8629,plain,
    ( ! [X0,X1] : k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8628,f191])).

fof(f8628,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8627,f197])).

fof(f8627,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8406,f637])).

fof(f8406,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X0),X1),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f2829,f729])).

fof(f729,plain,
    ( ! [X10,X11] : k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)
    | ~ spl2_2 ),
    inference(superposition,[],[f632,f87])).

fof(f1063,plain,
    ( ! [X14,X15] : k4_xboole_0(X14,X15) = k5_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X14)
    | ~ spl2_2 ),
    inference(superposition,[],[f632,f207])).

fof(f207,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3)) ),
    inference(backward_demodulation,[],[f88,f191])).

fof(f88,plain,(
    ! [X2,X3] : k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2)))) ),
    inference(superposition,[],[f31,f33])).

fof(f649,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2)
    | ~ spl2_2 ),
    inference(superposition,[],[f631,f26])).

fof(f631,plain,
    ( ! [X6,X7] : k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6
    | ~ spl2_2 ),
    inference(superposition,[],[f620,f564])).

fof(f8986,plain,
    ( ! [X35,X33,X34] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X34,X35),k5_xboole_0(k4_xboole_0(X34,X35),k4_xboole_0(X33,X34)))
    | ~ spl2_2 ),
    inference(superposition,[],[f8868,f1213])).

fof(f8868,plain,
    ( ! [X12,X11] : k1_xboole_0 = k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8867,f344])).

fof(f8867,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))) = k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8866,f313])).

fof(f8866,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))) = k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8865,f197])).

fof(f8865,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))) = k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k5_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f8780,f637])).

fof(f8780,plain,
    ( ! [X12,X11] : k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))) = k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k5_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),X11)))
    | ~ spl2_2 ),
    inference(superposition,[],[f8522,f8522])).

fof(f35676,plain,
    ( ! [X123,X122] : k4_xboole_0(k5_xboole_0(X122,X123),k4_xboole_0(X123,X122)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X123,X122),k5_xboole_0(X122,X123)),k4_xboole_0(X122,X123))
    | ~ spl2_2 ),
    inference(superposition,[],[f29037,f29033])).

fof(f29033,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))
    | ~ spl2_2 ),
    inference(superposition,[],[f570,f28499])).

fof(f570,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f543,f563])).

fof(f543,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))
    | ~ spl2_2 ),
    inference(superposition,[],[f350,f26])).

fof(f29037,plain,
    ( ! [X10,X9] : k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10))
    | ~ spl2_2 ),
    inference(superposition,[],[f665,f28499])).

fof(f665,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2
    | ~ spl2_2 ),
    inference(superposition,[],[f632,f26])).

fof(f53414,plain,
    ( ! [X24,X25] : k4_xboole_0(X24,k5_xboole_0(X24,X25)) = k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X24,X25),k4_xboole_0(X25,X24)))
    | ~ spl2_2 ),
    inference(superposition,[],[f87,f53087])).

fof(f53087,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(k5_xboole_0(X5,X4),X5)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f52691,f345])).

fof(f52691,plain,
    ( ! [X4,X5] : k4_xboole_0(k5_xboole_0(X5,X4),X5) = k5_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f564,f46347])).

fof(f46347,plain,
    ( ! [X109,X108] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X108,X109),k4_xboole_0(k5_xboole_0(X109,X108),X109))
    | ~ spl2_2 ),
    inference(backward_demodulation,[],[f45377,f46346])).

fof(f46346,plain,
    ( ! [X39,X40] : k4_xboole_0(k5_xboole_0(X39,X40),X39) = k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(k5_xboole_0(X39,X40),X39)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f46144,f19])).

fof(f46144,plain,
    ( ! [X39,X40] : k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(k5_xboole_0(X39,X40),X39))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X39,X40),X39),k1_xboole_0)
    | ~ spl2_2 ),
    inference(superposition,[],[f33,f45029])).

fof(f45029,plain,
    ( ! [X26,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X25,X26),X25),X26)
    | ~ spl2_2 ),
    inference(superposition,[],[f44579,f564])).

fof(f45377,plain,
    ( ! [X109,X108] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X108,X109),k4_xboole_0(X108,k4_xboole_0(X108,k4_xboole_0(k5_xboole_0(X109,X108),X109))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f45376,f19])).

fof(f45376,plain,
    ( ! [X109,X108] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k4_xboole_0(X108,X109),k1_xboole_0),k4_xboole_0(X108,k4_xboole_0(X108,k4_xboole_0(k5_xboole_0(X109,X108),X109))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f45375,f16289])).

fof(f16289,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(k4_xboole_0(X12,X13),X11)) = k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X11,X13))) ),
    inference(forward_demodulation,[],[f16029,f36])).

fof(f16029,plain,(
    ! [X12,X13,X11] : k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(k4_xboole_0(X12,X13),X11)) = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X13) ),
    inference(superposition,[],[f832,f33])).

fof(f45375,plain,
    ( ! [X109,X108] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k4_xboole_0(X108,X109),k1_xboole_0),k4_xboole_0(k4_xboole_0(X108,X109),k4_xboole_0(k4_xboole_0(X108,X109),k5_xboole_0(X109,X108))))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f45151,f33])).

fof(f45151,plain,
    ( ! [X109,X108] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(k4_xboole_0(X108,X109),k1_xboole_0),k4_xboole_0(k5_xboole_0(X109,X108),k4_xboole_0(k5_xboole_0(X109,X108),k4_xboole_0(X108,X109))))
    | ~ spl2_2 ),
    inference(superposition,[],[f979,f44579])).

fof(f979,plain,
    ( ! [X21,X20] : k1_xboole_0 = k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f978,f344])).

fof(f978,plain,
    ( ! [X21,X20] : k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = k4_xboole_0(X21,X21)
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f977,f19])).

fof(f977,plain,
    ( ! [X21,X20] : k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = k4_xboole_0(X21,k4_xboole_0(X21,k1_xboole_0))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f976,f344])).

fof(f976,plain,(
    ! [X21,X20] : k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X20,X20))) ),
    inference(forward_demodulation,[],[f946,f36])).

fof(f946,plain,(
    ! [X21,X20] : k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),X20) = k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21))) ),
    inference(superposition,[],[f87,f191])).

fof(f53499,plain,
    ( ! [X263,X262] : k5_xboole_0(X262,X263) = k4_xboole_0(k5_xboole_0(X262,k4_xboole_0(X263,X262)),k4_xboole_0(X262,k5_xboole_0(X262,X263)))
    | ~ spl2_2 ),
    inference(superposition,[],[f28907,f53087])).

fof(f28907,plain,
    ( ! [X4,X3] : k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X3,X4)) = X4
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f28724,f27276])).

fof(f27276,plain,
    ( ! [X76,X77,X75] : k4_xboole_0(X75,k4_xboole_0(X77,k5_xboole_0(X76,k4_xboole_0(X75,X76)))) = X75
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f27072,f19])).

fof(f27072,plain,
    ( ! [X76,X77,X75] : k4_xboole_0(X75,k4_xboole_0(k4_xboole_0(X77,k5_xboole_0(X76,k4_xboole_0(X75,X76))),k1_xboole_0)) = X75
    | ~ spl2_2 ),
    inference(superposition,[],[f26161,f15898])).

fof(f15898,plain,
    ( ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f15799,f349])).

fof(f15799,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))
    | ~ spl2_2 ),
    inference(superposition,[],[f31,f8630])).

fof(f26161,plain,
    ( ! [X30,X28,X29] : k4_xboole_0(X30,k4_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X30,X28))) = X30
    | ~ spl2_2 ),
    inference(superposition,[],[f25243,f313])).

fof(f25243,plain,
    ( ! [X30,X31,X29] : k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X29,k4_xboole_0(X31,X30)))) = X29
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f25017,f345])).

fof(f25017,plain,
    ( ! [X30,X31,X29] : k5_xboole_0(X29,k1_xboole_0) = k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X29,k4_xboole_0(X31,X30))))
    | ~ spl2_2 ),
    inference(superposition,[],[f31,f21993])).

fof(f21993,plain,
    ( ! [X10,X11,X9] : k1_xboole_0 = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X11,X10)))))
    | ~ spl2_2 ),
    inference(superposition,[],[f16269,f36])).

fof(f16269,plain,
    ( ! [X19,X17,X18] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X17)),k4_xboole_0(X18,k4_xboole_0(X19,X17)))
    | ~ spl2_2 ),
    inference(forward_demodulation,[],[f16014,f344])).

fof(f16014,plain,(
    ! [X19,X17,X18] : k4_xboole_0(X17,X17) = k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X17)),k4_xboole_0(X18,k4_xboole_0(X19,X17))) ),
    inference(superposition,[],[f832,f856])).

fof(f28724,plain,
    ( ! [X4,X3] : k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X3,X4))
    | ~ spl2_2 ),
    inference(superposition,[],[f33,f28497])).

fof(f43,plain,
    ( k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f41,plain,
    ( spl2_1
  <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f63,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f55,f60])).

fof(f55,plain,(
    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[],[f51,f19])).

fof(f44,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f32,f41])).

fof(f32,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f18,f22,f25])).

fof(f18,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:47:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (19420)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (19411)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (19421)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (19413)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (19417)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (19415)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (19410)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (19425)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (19419)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.50  % (19408)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (19419)Refutation not found, incomplete strategy% (19419)------------------------------
% 0.21/0.50  % (19419)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (19419)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (19419)Memory used [KB]: 10490
% 0.21/0.50  % (19419)Time elapsed: 0.091 s
% 0.21/0.50  % (19419)------------------------------
% 0.21/0.50  % (19419)------------------------------
% 0.21/0.50  % (19409)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.50  % (19412)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (19416)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.51  % (19422)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.51  % (19423)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.51  % (19414)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (19418)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.52  % (19424)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 5.34/1.05  % (19412)Time limit reached!
% 5.34/1.05  % (19412)------------------------------
% 5.34/1.05  % (19412)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.34/1.05  % (19412)Termination reason: Time limit
% 5.34/1.05  
% 5.34/1.05  % (19412)Memory used [KB]: 15095
% 5.34/1.05  % (19412)Time elapsed: 0.640 s
% 5.34/1.05  % (19412)------------------------------
% 5.34/1.05  % (19412)------------------------------
% 12.35/1.92  % (19414)Time limit reached!
% 12.35/1.92  % (19414)------------------------------
% 12.35/1.92  % (19414)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.35/1.93  % (19414)Termination reason: Time limit
% 12.35/1.93  % (19414)Termination phase: Saturation
% 12.35/1.93  
% 12.35/1.93  % (19414)Memory used [KB]: 36843
% 12.35/1.93  % (19414)Time elapsed: 1.500 s
% 12.35/1.93  % (19414)------------------------------
% 12.35/1.93  % (19414)------------------------------
% 12.97/2.06  % (19413)Time limit reached!
% 12.97/2.06  % (19413)------------------------------
% 12.97/2.06  % (19413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 12.97/2.06  % (19413)Termination reason: Time limit
% 12.97/2.06  
% 12.97/2.06  % (19413)Memory used [KB]: 42600
% 12.97/2.06  % (19413)Time elapsed: 1.598 s
% 12.97/2.06  % (19413)------------------------------
% 12.97/2.06  % (19413)------------------------------
% 14.81/2.22  % (19410)Time limit reached!
% 14.81/2.22  % (19410)------------------------------
% 14.81/2.22  % (19410)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 14.81/2.22  % (19410)Termination reason: Time limit
% 14.81/2.22  % (19410)Termination phase: Saturation
% 14.81/2.22  
% 14.81/2.22  % (19410)Memory used [KB]: 41321
% 14.81/2.22  % (19410)Time elapsed: 1.800 s
% 14.81/2.22  % (19410)------------------------------
% 14.81/2.22  % (19410)------------------------------
% 17.86/2.61  % (19420)Time limit reached!
% 17.86/2.61  % (19420)------------------------------
% 17.86/2.61  % (19420)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 17.86/2.61  % (19420)Termination reason: Time limit
% 17.86/2.61  % (19420)Termination phase: Saturation
% 17.86/2.61  
% 17.86/2.61  % (19420)Memory used [KB]: 69465
% 17.86/2.61  % (19420)Time elapsed: 2.200 s
% 17.86/2.61  % (19420)------------------------------
% 17.86/2.61  % (19420)------------------------------
% 36.43/4.92  % (19418)Refutation found. Thanks to Tanya!
% 36.43/4.92  % SZS status Theorem for theBenchmark
% 36.43/4.92  % SZS output start Proof for theBenchmark
% 36.43/4.92  fof(f53956,plain,(
% 36.43/4.92    $false),
% 36.43/4.92    inference(avatar_sat_refutation,[],[f44,f63,f53889])).
% 36.43/4.92  fof(f53889,plain,(
% 36.43/4.92    spl2_1 | ~spl2_2),
% 36.43/4.92    inference(avatar_contradiction_clause,[],[f53888])).
% 36.43/4.92  fof(f53888,plain,(
% 36.43/4.92    $false | (spl2_1 | ~spl2_2)),
% 36.43/4.92    inference(subsumption_resolution,[],[f43,f53887])).
% 36.43/4.92  fof(f53887,plain,(
% 36.43/4.92    ( ! [X263,X262] : (k5_xboole_0(X262,X263) = k4_xboole_0(k5_xboole_0(X262,k4_xboole_0(X263,X262)),k4_xboole_0(X262,k4_xboole_0(X262,X263)))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f53499,f53761])).
% 36.43/4.92  fof(f53761,plain,(
% 36.43/4.92    ( ! [X24,X25] : (k4_xboole_0(X24,k4_xboole_0(X24,X25)) = k4_xboole_0(X24,k5_xboole_0(X24,X25))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f53760,f197])).
% 36.43/4.92  fof(f197,plain,(
% 36.43/4.92    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X4,X5)) = k5_xboole_0(X4,k4_xboole_0(X4,X5))) )),
% 36.43/4.92    inference(superposition,[],[f31,f35])).
% 36.43/4.92  fof(f35,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 36.43/4.92    inference(definition_unfolding,[],[f24,f25])).
% 36.43/4.92  fof(f25,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 36.43/4.92    inference(cnf_transformation,[],[f8])).
% 36.43/4.92  fof(f8,axiom,(
% 36.43/4.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 36.43/4.92  fof(f24,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 36.43/4.92    inference(cnf_transformation,[],[f7])).
% 36.43/4.92  fof(f7,axiom,(
% 36.43/4.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 36.43/4.92  fof(f31,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 36.43/4.92    inference(definition_unfolding,[],[f23,f25])).
% 36.43/4.92  fof(f23,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 36.43/4.92    inference(cnf_transformation,[],[f2])).
% 36.43/4.92  fof(f2,axiom,(
% 36.43/4.92    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 36.43/4.92  fof(f53760,plain,(
% 36.43/4.92    ( ! [X24,X25] : (k5_xboole_0(X24,k4_xboole_0(X24,X25)) = k4_xboole_0(X24,k5_xboole_0(X24,X25))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f53414,f44785])).
% 36.43/4.92  fof(f44785,plain,(
% 36.43/4.92    ( ! [X123,X122] : (k4_xboole_0(X122,X123) = k4_xboole_0(k5_xboole_0(X122,X123),k4_xboole_0(X123,X122))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f44782,f563])).
% 36.43/4.92  fof(f563,plain,(
% 36.43/4.92    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = X4) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f545,f345])).
% 36.43/4.92  fof(f345,plain,(
% 36.43/4.92    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f51,f344])).
% 36.43/4.92  fof(f344,plain,(
% 36.43/4.92    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f324,f19])).
% 36.43/4.92  fof(f19,plain,(
% 36.43/4.92    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 36.43/4.92    inference(cnf_transformation,[],[f6])).
% 36.43/4.92  fof(f6,axiom,(
% 36.43/4.92    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 36.43/4.92  fof(f324,plain,(
% 36.43/4.92    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k1_xboole_0)) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f83,f321])).
% 36.43/4.92  fof(f321,plain,(
% 36.43/4.92    ( ! [X1] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X1)) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f67,f320])).
% 36.43/4.92  fof(f320,plain,(
% 36.43/4.92    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f291,f72])).
% 36.43/4.92  fof(f72,plain,(
% 36.43/4.92    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f67,f31])).
% 36.43/4.92  fof(f291,plain,(
% 36.43/4.92    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0)))) )),
% 36.43/4.92    inference(superposition,[],[f45,f19])).
% 36.43/4.92  fof(f45,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X0)))) = X0) )),
% 36.43/4.92    inference(backward_demodulation,[],[f34,f36])).
% 36.43/4.92  fof(f36,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 36.43/4.92    inference(definition_unfolding,[],[f27,f25,f25])).
% 36.43/4.92  fof(f27,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 36.43/4.92    inference(cnf_transformation,[],[f9])).
% 36.43/4.92  fof(f9,axiom,(
% 36.43/4.92    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 36.43/4.92  fof(f34,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k5_xboole_0(X0,k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X0)) = X0) )),
% 36.43/4.92    inference(definition_unfolding,[],[f21,f22,f25])).
% 36.43/4.92  fof(f22,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 36.43/4.92    inference(cnf_transformation,[],[f12])).
% 36.43/4.92  fof(f12,axiom,(
% 36.43/4.92    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 36.43/4.92  fof(f21,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 36.43/4.92    inference(cnf_transformation,[],[f4])).
% 36.43/4.92  fof(f4,axiom,(
% 36.43/4.92    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 36.43/4.92  fof(f67,plain,(
% 36.43/4.92    ( ! [X1] : (k4_xboole_0(k1_xboole_0,X1) = k5_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X1))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f64,f31])).
% 36.43/4.92  fof(f64,plain,(
% 36.43/4.92    ( ! [X0] : (k5_xboole_0(k1_xboole_0,X0) = k5_xboole_0(k1_xboole_0,k5_xboole_0(k1_xboole_0,X0))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f26,f62])).
% 36.43/4.92  fof(f62,plain,(
% 36.43/4.92    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0) | ~spl2_2),
% 36.43/4.92    inference(avatar_component_clause,[],[f60])).
% 36.43/4.92  fof(f60,plain,(
% 36.43/4.92    spl2_2 <=> k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 36.43/4.92    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 36.43/4.92  fof(f26,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 36.43/4.92    inference(cnf_transformation,[],[f11])).
% 36.43/4.92  fof(f11,axiom,(
% 36.43/4.92    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 36.43/4.92  fof(f83,plain,(
% 36.43/4.92    ( ! [X0] : (k4_xboole_0(X0,X0) = k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,X0))) )),
% 36.43/4.92    inference(superposition,[],[f33,f19])).
% 36.43/4.92  fof(f33,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 36.43/4.92    inference(definition_unfolding,[],[f20,f25,f25])).
% 36.43/4.92  fof(f20,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 36.43/4.92    inference(cnf_transformation,[],[f1])).
% 36.43/4.92  fof(f1,axiom,(
% 36.43/4.92    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 36.43/4.92  fof(f51,plain,(
% 36.43/4.92    ( ! [X0] : (k5_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 36.43/4.92    inference(superposition,[],[f31,f19])).
% 36.43/4.92  fof(f545,plain,(
% 36.43/4.92    ( ! [X4] : (k5_xboole_0(k1_xboole_0,X4) = k5_xboole_0(X4,k1_xboole_0)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f350,f349])).
% 36.43/4.92  fof(f349,plain,(
% 36.43/4.92    ( ! [X3] : (k1_xboole_0 = k5_xboole_0(X3,X3)) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f215,f344])).
% 36.43/4.92  fof(f215,plain,(
% 36.43/4.92    ( ! [X3] : (k4_xboole_0(X3,X3) = k5_xboole_0(X3,X3)) )),
% 36.43/4.92    inference(superposition,[],[f31,f181])).
% 36.43/4.92  fof(f181,plain,(
% 36.43/4.92    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 36.43/4.92    inference(superposition,[],[f35,f19])).
% 36.43/4.92  fof(f350,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = k5_xboole_0(k1_xboole_0,X1)) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f230,f344])).
% 36.43/4.92  fof(f230,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X0,X0),X1) = k5_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 36.43/4.92    inference(superposition,[],[f26,f215])).
% 36.43/4.92  fof(f44782,plain,(
% 36.43/4.92    ( ! [X123,X122] : (k4_xboole_0(k5_xboole_0(X122,X123),k4_xboole_0(X123,X122)) = k5_xboole_0(k1_xboole_0,k4_xboole_0(X122,X123))) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f35676,f44579])).
% 36.43/4.92  fof(f44579,plain,(
% 36.43/4.92    ( ! [X4,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k5_xboole_0(X4,X3))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f8986,f29036])).
% 36.43/4.92  fof(f29036,plain,(
% 36.43/4.92    ( ! [X8,X7] : (k5_xboole_0(X7,X8) = k5_xboole_0(k4_xboole_0(X8,X7),k4_xboole_0(X7,X8))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f649,f28499])).
% 36.43/4.92  fof(f28499,plain,(
% 36.43/4.92    ( ! [X37,X38] : (k4_xboole_0(X38,X37) = k5_xboole_0(X37,k5_xboole_0(X38,k4_xboole_0(X37,X38)))) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f15811,f28497])).
% 36.43/4.92  fof(f28497,plain,(
% 36.43/4.92    ( ! [X33,X32] : (k4_xboole_0(X32,X33) = k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33)) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f28496,f8808])).
% 36.43/4.92  fof(f8808,plain,(
% 36.43/4.92    ( ! [X10,X8,X9] : (k4_xboole_0(X8,X10) = k4_xboole_0(X8,k4_xboole_0(X8,k4_xboole_0(k5_xboole_0(X8,k4_xboole_0(X9,X8)),X10)))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f36,f8522])).
% 36.43/4.92  fof(f8522,plain,(
% 36.43/4.92    ( ! [X37,X36] : (k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36)))) = X36) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8521,f19])).
% 36.43/4.92  fof(f8521,plain,(
% 36.43/4.92    ( ! [X37,X36] : (k4_xboole_0(X36,k1_xboole_0) = k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8520,f345])).
% 36.43/4.92  fof(f8520,plain,(
% 36.43/4.92    ( ! [X37,X36] : (k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36)))) = k5_xboole_0(k4_xboole_0(X36,k1_xboole_0),k1_xboole_0)) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8519,f344])).
% 36.43/4.92  fof(f8519,plain,(
% 36.43/4.92    ( ! [X37,X36] : (k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36)))) = k5_xboole_0(k4_xboole_0(X36,k1_xboole_0),k4_xboole_0(X36,X36))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8366,f313])).
% 36.43/4.92  fof(f313,plain,(
% 36.43/4.92    ( ! [X6,X5] : (k4_xboole_0(X5,k4_xboole_0(X6,X5)) = X5) )),
% 36.43/4.92    inference(superposition,[],[f45,f31])).
% 36.43/4.92  fof(f8366,plain,(
% 36.43/4.92    ( ! [X37,X36] : (k4_xboole_0(X36,k4_xboole_0(X36,k5_xboole_0(X36,k4_xboole_0(X37,X36)))) = k5_xboole_0(k4_xboole_0(X36,k1_xboole_0),k4_xboole_0(X36,k4_xboole_0(X36,k4_xboole_0(X37,X36))))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f2829,f344])).
% 36.43/4.92  fof(f2829,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,X1))))) )),
% 36.43/4.92    inference(backward_demodulation,[],[f47,f2828])).
% 36.43/4.92  fof(f2828,plain,(
% 36.43/4.92    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,X13))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13)))))) )),
% 36.43/4.92    inference(forward_demodulation,[],[f2827,f36])).
% 36.43/4.92  fof(f2827,plain,(
% 36.43/4.92    ( ! [X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13)))))) )),
% 36.43/4.92    inference(forward_demodulation,[],[f2826,f872])).
% 36.43/4.92  fof(f872,plain,(
% 36.43/4.92    ( ! [X4,X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),X4) = k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4)))) )),
% 36.43/4.92    inference(forward_demodulation,[],[f822,f191])).
% 36.43/4.92  fof(f191,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 36.43/4.92    inference(superposition,[],[f35,f33])).
% 36.43/4.92  fof(f822,plain,(
% 36.43/4.92    ( ! [X4,X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(k4_xboole_0(X2,X3),X4))) = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))),X4)) )),
% 36.43/4.92    inference(superposition,[],[f36,f33])).
% 36.43/4.92  fof(f2826,plain,(
% 36.43/4.92    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13))) = k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X11,k4_xboole_0(X11,X13)))))) )),
% 36.43/4.92    inference(forward_demodulation,[],[f2719,f36])).
% 36.43/4.92  fof(f2719,plain,(
% 36.43/4.92    ( ! [X12,X13,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),X13))) = k4_xboole_0(k4_xboole_0(X11,k4_xboole_0(X11,X12)),k4_xboole_0(X11,k4_xboole_0(X11,X13)))) )),
% 36.43/4.92    inference(superposition,[],[f39,f35])).
% 36.43/4.92  fof(f39,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 36.43/4.92    inference(definition_unfolding,[],[f30,f25,f25,f25])).
% 36.43/4.92  fof(f30,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 36.43/4.92    inference(cnf_transformation,[],[f10])).
% 36.43/4.92  fof(f10,axiom,(
% 36.43/4.92    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_xboole_1)).
% 36.43/4.92  fof(f47,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))))))) )),
% 36.43/4.92    inference(forward_demodulation,[],[f38,f36])).
% 36.43/4.92  fof(f38,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X2,X1)))) = k5_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X2)),k4_xboole_0(X0,k4_xboole_0(X0,X1))))) )),
% 36.43/4.92    inference(definition_unfolding,[],[f29,f25,f22,f22,f25,f25])).
% 36.43/4.92  fof(f29,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 36.43/4.92    inference(cnf_transformation,[],[f5])).
% 36.43/4.92  fof(f5,axiom,(
% 36.43/4.92    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).
% 36.43/4.92  fof(f28496,plain,(
% 36.43/4.92    ( ! [X33,X32] : (k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33) = k4_xboole_0(X32,k4_xboole_0(X32,k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33)))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f28308,f19])).
% 36.43/4.92  fof(f28308,plain,(
% 36.43/4.92    ( ! [X33,X32] : (k4_xboole_0(X32,k4_xboole_0(X32,k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X32,k4_xboole_0(X33,X32)),X33),k1_xboole_0)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f33,f27557])).
% 36.43/4.92  fof(f27557,plain,(
% 36.43/4.92    ( ! [X118,X117] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X117,k4_xboole_0(X118,X117)),X118),X117)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f26588,f9197])).
% 36.43/4.92  fof(f9197,plain,(
% 36.43/4.92    ( ! [X12,X11] : (k4_xboole_0(k5_xboole_0(X11,k4_xboole_0(X12,X11)),k4_xboole_0(X12,X11)) = X11) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f9122,f637])).
% 36.43/4.92  fof(f637,plain,(
% 36.43/4.92    ( ! [X2,X1] : (k5_xboole_0(X1,X2) = k5_xboole_0(X2,X1)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f564,f620])).
% 36.43/4.92  fof(f620,plain,(
% 36.43/4.92    ( ! [X6,X7] : (k5_xboole_0(X7,k5_xboole_0(X6,X7)) = X6) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f608,f345])).
% 36.43/4.92  fof(f608,plain,(
% 36.43/4.92    ( ! [X6,X7] : (k5_xboole_0(X6,k1_xboole_0) = k5_xboole_0(X7,k5_xboole_0(X6,X7))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f564,f342])).
% 36.43/4.92  fof(f342,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f235,f321])).
% 36.43/4.92  fof(f235,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f234,f72])).
% 36.43/4.92  fof(f234,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,k5_xboole_0(X0,X1))) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 36.43/4.92    inference(forward_demodulation,[],[f228,f83])).
% 36.43/4.92  fof(f228,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,X1)) = k5_xboole_0(X0,k5_xboole_0(X1,k5_xboole_0(X0,X1)))) )),
% 36.43/4.92    inference(superposition,[],[f215,f26])).
% 36.43/4.92  fof(f564,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k5_xboole_0(X0,k5_xboole_0(X0,X1)) = X1) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f350,f563])).
% 36.43/4.92  fof(f9122,plain,(
% 36.43/4.92    ( ! [X12,X11] : (k4_xboole_0(k5_xboole_0(k4_xboole_0(X12,X11),X11),k4_xboole_0(X12,X11)) = X11) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f8901,f313])).
% 36.43/4.92  fof(f8901,plain,(
% 36.43/4.92    ( ! [X17,X18] : (k4_xboole_0(X18,X17) = k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17)) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8811,f632])).
% 36.43/4.92  fof(f632,plain,(
% 36.43/4.92    ( ! [X8,X9] : (k5_xboole_0(k5_xboole_0(X9,X8),X9) = X8) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f620,f620])).
% 36.43/4.92  fof(f8811,plain,(
% 36.43/4.92    ( ! [X17,X18] : (k4_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17) = k5_xboole_0(k5_xboole_0(X17,k4_xboole_0(X18,X17)),X17)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f87,f8522])).
% 36.43/4.92  fof(f87,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0)))) )),
% 36.43/4.92    inference(superposition,[],[f31,f33])).
% 36.43/4.92  fof(f26588,plain,(
% 36.43/4.92    ( ! [X6,X4,X5] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,k4_xboole_0(X5,X6)))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f25482,f1213])).
% 36.43/4.92  fof(f1213,plain,(
% 36.43/4.92    ( ! [X14,X15,X16] : (k4_xboole_0(X15,X14) = k4_xboole_0(k4_xboole_0(X15,X14),k4_xboole_0(X14,X16))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f1185,f313])).
% 36.43/4.92  fof(f1185,plain,(
% 36.43/4.92    ( ! [X24,X23,X22] : (k4_xboole_0(X23,k4_xboole_0(k4_xboole_0(X22,X23),X24)) = X23) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f1137,f19])).
% 36.43/4.92  fof(f1137,plain,(
% 36.43/4.92    ( ! [X24,X23,X22] : (k4_xboole_0(X23,k4_xboole_0(k4_xboole_0(k4_xboole_0(X22,X23),X24),k1_xboole_0)) = X23) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f856,f735])).
% 36.43/4.92  fof(f735,plain,(
% 36.43/4.92    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X1,X2),X1)) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f734,f349])).
% 36.43/4.92  fof(f734,plain,(
% 36.43/4.92    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,X2))) )),
% 36.43/4.92    inference(forward_demodulation,[],[f711,f191])).
% 36.43/4.92  fof(f711,plain,(
% 36.43/4.92    ( ! [X2,X1] : (k4_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k4_xboole_0(X1,k4_xboole_0(X2,k4_xboole_0(X2,X1))))) )),
% 36.43/4.92    inference(superposition,[],[f87,f33])).
% 36.43/4.92  fof(f856,plain,(
% 36.43/4.92    ( ! [X24,X23,X25] : (k4_xboole_0(X25,k4_xboole_0(X23,k4_xboole_0(X23,k4_xboole_0(X24,X25)))) = X25) )),
% 36.43/4.92    inference(superposition,[],[f313,f36])).
% 36.43/4.92  fof(f25482,plain,(
% 36.43/4.92    ( ! [X4,X5,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X3,X4),X5),k4_xboole_0(X3,X5))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f16406,f872])).
% 36.43/4.92  fof(f16406,plain,(
% 36.43/4.92    ( ! [X57,X58,X56] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,k4_xboole_0(X56,X58))),k4_xboole_0(X57,X58))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f16099,f36])).
% 36.43/4.92  fof(f16099,plain,(
% 36.43/4.92    ( ! [X57,X58,X56] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k4_xboole_0(X57,k4_xboole_0(X57,X56)),X58),k4_xboole_0(X57,X58))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f754,f832])).
% 36.43/4.92  fof(f832,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),X2)) )),
% 36.43/4.92    inference(superposition,[],[f36,f33])).
% 36.43/4.92  fof(f754,plain,(
% 36.43/4.92    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X2,k4_xboole_0(X2,X1)),X1)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f735,f33])).
% 36.43/4.92  fof(f15811,plain,(
% 36.43/4.92    ( ! [X37,X38] : (k5_xboole_0(X37,k5_xboole_0(X38,k4_xboole_0(X37,X38))) = k4_xboole_0(k5_xboole_0(X38,k4_xboole_0(X37,X38)),X37)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f1063,f8630])).
% 36.43/4.92  fof(f8630,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = X0) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8629,f727])).
% 36.43/4.92  fof(f727,plain,(
% 36.43/4.92    ( ! [X6,X7] : (k5_xboole_0(k4_xboole_0(X7,k4_xboole_0(X7,X6)),k4_xboole_0(X6,X7)) = X6) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f620,f87])).
% 36.43/4.92  fof(f8629,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,X1)) = k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8628,f191])).
% 36.43/4.92  fof(f8628,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k4_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X0))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8627,f197])).
% 36.43/4.92  fof(f8627,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(X1,k4_xboole_0(X1,X0)),k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X1,X0))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8406,f637])).
% 36.43/4.92  fof(f8406,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) = k5_xboole_0(k5_xboole_0(k4_xboole_0(X1,X0),X1),k4_xboole_0(X0,k5_xboole_0(k4_xboole_0(X1,X0),X1)))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f2829,f729])).
% 36.43/4.92  fof(f729,plain,(
% 36.43/4.92    ( ! [X10,X11] : (k4_xboole_0(X11,k4_xboole_0(X11,X10)) = k5_xboole_0(k4_xboole_0(X10,X11),X10)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f632,f87])).
% 36.43/4.92  fof(f1063,plain,(
% 36.43/4.92    ( ! [X14,X15] : (k4_xboole_0(X14,X15) = k5_xboole_0(k4_xboole_0(X15,k4_xboole_0(X15,X14)),X14)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f632,f207])).
% 36.43/4.92  fof(f207,plain,(
% 36.43/4.92    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,X3))) )),
% 36.43/4.92    inference(backward_demodulation,[],[f88,f191])).
% 36.43/4.92  fof(f88,plain,(
% 36.43/4.92    ( ! [X2,X3] : (k4_xboole_0(X3,k4_xboole_0(X3,X2)) = k5_xboole_0(X2,k4_xboole_0(X2,k4_xboole_0(X3,k4_xboole_0(X3,X2))))) )),
% 36.43/4.92    inference(superposition,[],[f31,f33])).
% 36.43/4.92  fof(f649,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),X2)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f631,f26])).
% 36.43/4.92  fof(f631,plain,(
% 36.43/4.92    ( ! [X6,X7] : (k5_xboole_0(k5_xboole_0(X6,X7),X7) = X6) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f620,f564])).
% 36.43/4.92  fof(f8986,plain,(
% 36.43/4.92    ( ! [X35,X33,X34] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X34,X35),k5_xboole_0(k4_xboole_0(X34,X35),k4_xboole_0(X33,X34)))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f8868,f1213])).
% 36.43/4.92  fof(f8868,plain,(
% 36.43/4.92    ( ! [X12,X11] : (k1_xboole_0 = k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11)))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8867,f344])).
% 36.43/4.92  fof(f8867,plain,(
% 36.43/4.92    ( ! [X12,X11] : (k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))) = k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8866,f313])).
% 36.43/4.92  fof(f8866,plain,(
% 36.43/4.92    ( ! [X12,X11] : (k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))) = k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8865,f197])).
% 36.43/4.92  fof(f8865,plain,(
% 36.43/4.92    ( ! [X12,X11] : (k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))) = k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k5_xboole_0(X11,k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f8780,f637])).
% 36.43/4.92  fof(f8780,plain,(
% 36.43/4.92    ( ! [X12,X11] : (k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))) = k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k4_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),k5_xboole_0(k4_xboole_0(X11,k5_xboole_0(X11,k4_xboole_0(X12,X11))),X11)))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f8522,f8522])).
% 36.43/4.92  fof(f35676,plain,(
% 36.43/4.92    ( ! [X123,X122] : (k4_xboole_0(k5_xboole_0(X122,X123),k4_xboole_0(X123,X122)) = k5_xboole_0(k4_xboole_0(k4_xboole_0(X123,X122),k5_xboole_0(X122,X123)),k4_xboole_0(X122,X123))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f29037,f29033])).
% 36.43/4.92  fof(f29033,plain,(
% 36.43/4.92    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(k5_xboole_0(X1,X2),k4_xboole_0(X2,X1))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f570,f28499])).
% 36.43/4.92  fof(f570,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2))) = X2) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f543,f563])).
% 36.43/4.92  fof(f543,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k5_xboole_0(k1_xboole_0,X2) = k5_xboole_0(k5_xboole_0(X0,X1),k5_xboole_0(X0,k5_xboole_0(X1,X2)))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f350,f26])).
% 36.43/4.92  fof(f29037,plain,(
% 36.43/4.92    ( ! [X10,X9] : (k4_xboole_0(X9,X10) = k5_xboole_0(k4_xboole_0(X10,X9),k5_xboole_0(X9,X10))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f665,f28499])).
% 36.43/4.92  fof(f665,plain,(
% 36.43/4.92    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,k5_xboole_0(X1,X2)),k5_xboole_0(X0,X1)) = X2) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f632,f26])).
% 36.43/4.92  fof(f53414,plain,(
% 36.43/4.92    ( ! [X24,X25] : (k4_xboole_0(X24,k5_xboole_0(X24,X25)) = k5_xboole_0(X24,k4_xboole_0(k5_xboole_0(X24,X25),k4_xboole_0(X25,X24)))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f87,f53087])).
% 36.43/4.92  fof(f53087,plain,(
% 36.43/4.92    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(k5_xboole_0(X5,X4),X5)) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f52691,f345])).
% 36.43/4.92  fof(f52691,plain,(
% 36.43/4.92    ( ! [X4,X5] : (k4_xboole_0(k5_xboole_0(X5,X4),X5) = k5_xboole_0(k4_xboole_0(X4,X5),k1_xboole_0)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f564,f46347])).
% 36.43/4.92  fof(f46347,plain,(
% 36.43/4.92    ( ! [X109,X108] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X108,X109),k4_xboole_0(k5_xboole_0(X109,X108),X109))) ) | ~spl2_2),
% 36.43/4.92    inference(backward_demodulation,[],[f45377,f46346])).
% 36.43/4.92  fof(f46346,plain,(
% 36.43/4.92    ( ! [X39,X40] : (k4_xboole_0(k5_xboole_0(X39,X40),X39) = k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(k5_xboole_0(X39,X40),X39)))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f46144,f19])).
% 36.43/4.92  fof(f46144,plain,(
% 36.43/4.92    ( ! [X39,X40] : (k4_xboole_0(X40,k4_xboole_0(X40,k4_xboole_0(k5_xboole_0(X39,X40),X39))) = k4_xboole_0(k4_xboole_0(k5_xboole_0(X39,X40),X39),k1_xboole_0)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f33,f45029])).
% 36.43/4.92  fof(f45029,plain,(
% 36.43/4.92    ( ! [X26,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(k5_xboole_0(X25,X26),X25),X26)) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f44579,f564])).
% 36.43/4.92  fof(f45377,plain,(
% 36.43/4.92    ( ! [X109,X108] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X108,X109),k4_xboole_0(X108,k4_xboole_0(X108,k4_xboole_0(k5_xboole_0(X109,X108),X109))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f45376,f19])).
% 36.43/4.92  fof(f45376,plain,(
% 36.43/4.92    ( ! [X109,X108] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k4_xboole_0(X108,X109),k1_xboole_0),k4_xboole_0(X108,k4_xboole_0(X108,k4_xboole_0(k5_xboole_0(X109,X108),X109))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f45375,f16289])).
% 36.43/4.92  fof(f16289,plain,(
% 36.43/4.92    ( ! [X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(k4_xboole_0(X12,X13),X11)) = k4_xboole_0(X12,k4_xboole_0(X12,k4_xboole_0(X11,X13)))) )),
% 36.43/4.92    inference(forward_demodulation,[],[f16029,f36])).
% 36.43/4.92  fof(f16029,plain,(
% 36.43/4.92    ( ! [X12,X13,X11] : (k4_xboole_0(k4_xboole_0(X12,X13),k4_xboole_0(k4_xboole_0(X12,X13),X11)) = k4_xboole_0(k4_xboole_0(X12,k4_xboole_0(X12,X11)),X13)) )),
% 36.43/4.92    inference(superposition,[],[f832,f33])).
% 36.43/4.92  fof(f45375,plain,(
% 36.43/4.92    ( ! [X109,X108] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k4_xboole_0(X108,X109),k1_xboole_0),k4_xboole_0(k4_xboole_0(X108,X109),k4_xboole_0(k4_xboole_0(X108,X109),k5_xboole_0(X109,X108))))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f45151,f33])).
% 36.43/4.92  fof(f45151,plain,(
% 36.43/4.92    ( ! [X109,X108] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(k4_xboole_0(X108,X109),k1_xboole_0),k4_xboole_0(k5_xboole_0(X109,X108),k4_xboole_0(k5_xboole_0(X109,X108),k4_xboole_0(X108,X109))))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f979,f44579])).
% 36.43/4.92  fof(f979,plain,(
% 36.43/4.92    ( ! [X21,X20] : (k1_xboole_0 = k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21)))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f978,f344])).
% 36.43/4.92  fof(f978,plain,(
% 36.43/4.92    ( ! [X21,X20] : (k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = k4_xboole_0(X21,X21)) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f977,f19])).
% 36.43/4.92  fof(f977,plain,(
% 36.43/4.92    ( ! [X21,X20] : (k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = k4_xboole_0(X21,k4_xboole_0(X21,k1_xboole_0))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f976,f344])).
% 36.43/4.92  fof(f976,plain,(
% 36.43/4.92    ( ! [X21,X20] : (k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21))) = k4_xboole_0(X21,k4_xboole_0(X21,k4_xboole_0(X20,X20)))) )),
% 36.43/4.92    inference(forward_demodulation,[],[f946,f36])).
% 36.43/4.92  fof(f946,plain,(
% 36.43/4.92    ( ! [X21,X20] : (k4_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),X20) = k5_xboole_0(k4_xboole_0(X21,k4_xboole_0(X21,X20)),k4_xboole_0(X20,k4_xboole_0(X20,X21)))) )),
% 36.43/4.92    inference(superposition,[],[f87,f191])).
% 36.43/4.92  fof(f53499,plain,(
% 36.43/4.92    ( ! [X263,X262] : (k5_xboole_0(X262,X263) = k4_xboole_0(k5_xboole_0(X262,k4_xboole_0(X263,X262)),k4_xboole_0(X262,k5_xboole_0(X262,X263)))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f28907,f53087])).
% 36.43/4.92  fof(f28907,plain,(
% 36.43/4.92    ( ! [X4,X3] : (k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X3,X4)) = X4) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f28724,f27276])).
% 36.43/4.92  fof(f27276,plain,(
% 36.43/4.92    ( ! [X76,X77,X75] : (k4_xboole_0(X75,k4_xboole_0(X77,k5_xboole_0(X76,k4_xboole_0(X75,X76)))) = X75) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f27072,f19])).
% 36.43/4.92  fof(f27072,plain,(
% 36.43/4.92    ( ! [X76,X77,X75] : (k4_xboole_0(X75,k4_xboole_0(k4_xboole_0(X77,k5_xboole_0(X76,k4_xboole_0(X75,X76))),k1_xboole_0)) = X75) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f26161,f15898])).
% 36.43/4.92  fof(f15898,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f15799,f349])).
% 36.43/4.92  fof(f15799,plain,(
% 36.43/4.92    ( ! [X0,X1] : (k5_xboole_0(X0,X0) = k4_xboole_0(X0,k5_xboole_0(X1,k4_xboole_0(X0,X1)))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f31,f8630])).
% 36.43/4.92  fof(f26161,plain,(
% 36.43/4.92    ( ! [X30,X28,X29] : (k4_xboole_0(X30,k4_xboole_0(k4_xboole_0(X29,X28),k4_xboole_0(X30,X28))) = X30) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f25243,f313])).
% 36.43/4.92  fof(f25243,plain,(
% 36.43/4.92    ( ! [X30,X31,X29] : (k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X29,k4_xboole_0(X31,X30)))) = X29) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f25017,f345])).
% 36.43/4.92  fof(f25017,plain,(
% 36.43/4.92    ( ! [X30,X31,X29] : (k5_xboole_0(X29,k1_xboole_0) = k4_xboole_0(X29,k4_xboole_0(X30,k4_xboole_0(X29,k4_xboole_0(X31,X30))))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f31,f21993])).
% 36.43/4.92  fof(f21993,plain,(
% 36.43/4.92    ( ! [X10,X11,X9] : (k1_xboole_0 = k4_xboole_0(X9,k4_xboole_0(X9,k4_xboole_0(X10,k4_xboole_0(X9,k4_xboole_0(X11,X10)))))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f16269,f36])).
% 36.43/4.92  fof(f16269,plain,(
% 36.43/4.92    ( ! [X19,X17,X18] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X17)),k4_xboole_0(X18,k4_xboole_0(X19,X17)))) ) | ~spl2_2),
% 36.43/4.92    inference(forward_demodulation,[],[f16014,f344])).
% 36.43/4.92  fof(f16014,plain,(
% 36.43/4.92    ( ! [X19,X17,X18] : (k4_xboole_0(X17,X17) = k4_xboole_0(k4_xboole_0(X18,k4_xboole_0(X18,X17)),k4_xboole_0(X18,k4_xboole_0(X19,X17)))) )),
% 36.43/4.92    inference(superposition,[],[f832,f856])).
% 36.43/4.92  fof(f28724,plain,(
% 36.43/4.92    ( ! [X4,X3] : (k4_xboole_0(X4,k4_xboole_0(X4,k5_xboole_0(X3,k4_xboole_0(X4,X3)))) = k4_xboole_0(k5_xboole_0(X3,k4_xboole_0(X4,X3)),k4_xboole_0(X3,X4))) ) | ~spl2_2),
% 36.43/4.92    inference(superposition,[],[f33,f28497])).
% 36.43/4.92  fof(f43,plain,(
% 36.43/4.92    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_1),
% 36.43/4.92    inference(avatar_component_clause,[],[f41])).
% 36.43/4.92  fof(f41,plain,(
% 36.43/4.92    spl2_1 <=> k5_xboole_0(sK0,sK1) = k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 36.43/4.92    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 36.43/4.92  fof(f63,plain,(
% 36.43/4.92    spl2_2),
% 36.43/4.92    inference(avatar_split_clause,[],[f55,f60])).
% 36.43/4.92  fof(f55,plain,(
% 36.43/4.92    k1_xboole_0 = k5_xboole_0(k1_xboole_0,k1_xboole_0)),
% 36.43/4.92    inference(superposition,[],[f51,f19])).
% 36.43/4.92  fof(f44,plain,(
% 36.43/4.92    ~spl2_1),
% 36.43/4.92    inference(avatar_split_clause,[],[f32,f41])).
% 36.43/4.92  fof(f32,plain,(
% 36.43/4.92    k5_xboole_0(sK0,sK1) != k4_xboole_0(k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 36.43/4.92    inference(definition_unfolding,[],[f18,f22,f25])).
% 36.43/4.92  fof(f18,plain,(
% 36.43/4.92    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 36.43/4.92    inference(cnf_transformation,[],[f17])).
% 36.43/4.92  fof(f17,plain,(
% 36.43/4.92    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 36.43/4.92    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f16])).
% 36.43/4.92  fof(f16,plain,(
% 36.43/4.92    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 36.43/4.92    introduced(choice_axiom,[])).
% 36.43/4.92  fof(f15,plain,(
% 36.43/4.92    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 36.43/4.92    inference(ennf_transformation,[],[f14])).
% 36.43/4.92  fof(f14,negated_conjecture,(
% 36.43/4.92    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 36.43/4.92    inference(negated_conjecture,[],[f13])).
% 36.43/4.92  fof(f13,conjecture,(
% 36.43/4.92    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 36.43/4.92    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t101_xboole_1)).
% 36.43/4.92  % SZS output end Proof for theBenchmark
% 36.43/4.92  % (19418)------------------------------
% 36.43/4.92  % (19418)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 36.43/4.92  % (19418)Termination reason: Refutation
% 36.43/4.92  
% 36.43/4.92  % (19418)Memory used [KB]: 134326
% 36.43/4.92  % (19418)Time elapsed: 4.520 s
% 36.43/4.92  % (19418)------------------------------
% 36.43/4.92  % (19418)------------------------------
% 36.56/4.94  % (19407)Success in time 4.581 s
%------------------------------------------------------------------------------
