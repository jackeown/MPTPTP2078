%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:12 EST 2020

% Result     : Theorem 1.52s
% Output     : Refutation 1.52s
% Verified   : 
% Statistics : Number of formulae       :  142 ( 287 expanded)
%              Number of leaves         :   34 ( 136 expanded)
%              Depth                    :   10
%              Number of atoms          :  344 ( 617 expanded)
%              Number of equality atoms :  118 ( 263 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7008,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f37,f41,f45,f54,f58,f79,f83,f153,f157,f161,f165,f261,f308,f349,f386,f390,f472,f509,f985,f3185,f3942,f4943,f6786])).

fof(f6786,plain,
    ( ~ spl3_18
    | spl3_34
    | ~ spl3_57
    | ~ spl3_70
    | ~ spl3_88 ),
    inference(avatar_contradiction_clause,[],[f6785])).

fof(f6785,plain,
    ( $false
    | ~ spl3_18
    | spl3_34
    | ~ spl3_57
    | ~ spl3_70
    | ~ spl3_88 ),
    inference(subsumption_resolution,[],[f984,f6784])).

fof(f6784,plain,
    ( ! [X64,X65,X63] : k4_xboole_0(X63,k4_xboole_0(X64,X65)) = k2_xboole_0(k4_xboole_0(X63,X64),k4_xboole_0(X63,k4_xboole_0(X63,X65)))
    | ~ spl3_18
    | ~ spl3_57
    | ~ spl3_70
    | ~ spl3_88 ),
    inference(forward_demodulation,[],[f6600,f4168])).

fof(f4168,plain,
    ( ! [X41,X42,X40] : k4_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(X40,k4_xboole_0(X40,k2_xboole_0(k4_xboole_0(X40,X41),X42)))
    | ~ spl3_57
    | ~ spl3_70 ),
    inference(forward_demodulation,[],[f3994,f3941])).

fof(f3941,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X11,X10),X12)) = k4_xboole_0(X10,X12)
    | ~ spl3_70 ),
    inference(avatar_component_clause,[],[f3940])).

fof(f3940,plain,
    ( spl3_70
  <=> ! [X11,X10,X12] : k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X11,X10),X12)) = k4_xboole_0(X10,X12) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f3994,plain,
    ( ! [X41,X42,X40] : k4_xboole_0(X40,k2_xboole_0(k4_xboole_0(X40,X40),k4_xboole_0(X41,X42))) = k4_xboole_0(X40,k4_xboole_0(X40,k2_xboole_0(k4_xboole_0(X40,X41),X42)))
    | ~ spl3_57 ),
    inference(superposition,[],[f3184,f3184])).

fof(f3184,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f3183])).

fof(f3183,plain,
    ( spl3_57
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f6600,plain,
    ( ! [X64,X65,X63] : k2_xboole_0(k4_xboole_0(X63,X64),k4_xboole_0(X63,k4_xboole_0(X63,X65))) = k4_xboole_0(X63,k4_xboole_0(X63,k2_xboole_0(k4_xboole_0(X63,X64),X65)))
    | ~ spl3_18
    | ~ spl3_88 ),
    inference(superposition,[],[f4942,f307])).

fof(f307,plain,
    ( ! [X12,X11] : k2_xboole_0(k4_xboole_0(X11,X12),X11) = X11
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f306])).

fof(f306,plain,
    ( spl3_18
  <=> ! [X11,X12] : k2_xboole_0(k4_xboole_0(X11,X12),X11) = X11 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f4942,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2)))
    | ~ spl3_88 ),
    inference(avatar_component_clause,[],[f4941])).

fof(f4941,plain,
    ( spl3_88
  <=> ! [X1,X0,X2] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f984,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f982])).

fof(f982,plain,
    ( spl3_34
  <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f4943,plain,
    ( spl3_88
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f176,f151,f52,f4941])).

fof(f52,plain,
    ( spl3_4
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f151,plain,
    ( spl3_11
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f176,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2)))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f32,f175])).

fof(f175,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(X4,k2_xboole_0(X3,X5))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f167,f152])).

fof(f152,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f151])).

fof(f167,plain,
    ( ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(k4_xboole_0(X4,X3),X5)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(superposition,[],[f152,f53])).

fof(f53,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f52])).

fof(f32,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f26,f19,f19])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f26,plain,(
    ! [X2,X0,X1] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).

fof(f3942,plain,
    ( spl3_70
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f524,f507,f151,f3940])).

fof(f507,plain,
    ( spl3_25
  <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f524,plain,
    ( ! [X12,X10,X11] : k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X11,X10),X12)) = k4_xboole_0(X10,X12)
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(superposition,[],[f152,f508])).

fof(f508,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f507])).

fof(f3185,plain,(
    spl3_57 ),
    inference(avatar_split_clause,[],[f33,f3183])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2)) ),
    inference(backward_demodulation,[],[f31,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f31,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2) ),
    inference(definition_unfolding,[],[f24,f19,f19])).

fof(f24,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f985,plain,(
    ~ spl3_34 ),
    inference(avatar_split_clause,[],[f27,f982])).

fof(f27,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) ),
    inference(definition_unfolding,[],[f16,f19])).

fof(f16,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).

fof(f14,plain,
    ( ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))
   => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2)) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f509,plain,
    ( spl3_25
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_22
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f493,f470,f384,f155,f151,f81,f56,f52,f43,f39,f507])).

fof(f39,plain,
    ( spl3_2
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f43,plain,
    ( spl3_3
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f56,plain,
    ( spl3_5
  <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f81,plain,
    ( spl3_7
  <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f155,plain,
    ( spl3_12
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f384,plain,
    ( spl3_22
  <=> ! [X7,X6] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f470,plain,
    ( spl3_24
  <=> ! [X5,X4] : k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f493,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_22
    | ~ spl3_24 ),
    inference(backward_demodulation,[],[f425,f492])).

fof(f492,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,X14)) = X15
    | ~ spl3_2
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f477,f471])).

fof(f471,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f470])).

fof(f477,plain,
    ( ! [X14,X15] : k4_xboole_0(X15,k4_xboole_0(X14,X14)) = k2_xboole_0(k4_xboole_0(X14,X14),X15)
    | ~ spl3_2
    | ~ spl3_24 ),
    inference(superposition,[],[f471,f40])).

fof(f40,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f39])).

fof(f425,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_12
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f222,f423])).

fof(f423,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X5,X5)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_7
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f93,f421])).

fof(f421,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(backward_demodulation,[],[f411,f398])).

fof(f398,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X1) = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(superposition,[],[f385,f152])).

fof(f385,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f384])).

fof(f411,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f410,f57])).

fof(f57,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f56])).

fof(f410,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1)))
    | ~ spl3_3
    | ~ spl3_11
    | ~ spl3_22 ),
    inference(forward_demodulation,[],[f391,f152])).

fof(f391,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1))
    | ~ spl3_3
    | ~ spl3_22 ),
    inference(superposition,[],[f385,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f43])).

fof(f93,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))
    | ~ spl3_3
    | ~ spl3_7 ),
    inference(superposition,[],[f44,f82])).

fof(f82,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f222,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X2,X3))) = k4_xboole_0(X2,k4_xboole_0(X3,X2))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f203,f48])).

fof(f48,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f44,f40])).

fof(f203,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X2,X3))) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f156,f53])).

fof(f156,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f472,plain,
    ( spl3_24
    | ~ spl3_11
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f420,f388,f384,f151,f470])).

fof(f388,plain,
    ( spl3_23
  <=> ! [X5,X4] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),X5) = X5 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f420,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5
    | ~ spl3_11
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f389,f398])).

fof(f389,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),X5) = X5
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f388])).

fof(f390,plain,
    ( spl3_23
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f377,f347,f151,f77,f39,f388])).

fof(f77,plain,
    ( spl3_6
  <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f347,plain,
    ( spl3_20
  <=> ! [X3,X4] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f377,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),X5) = X5
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f376,f40])).

fof(f376,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X5))),X5) = X5
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f356,f152])).

fof(f356,plain,
    ( ! [X4,X5] : k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)),X5) = X5
    | ~ spl3_6
    | ~ spl3_20 ),
    inference(superposition,[],[f348,f78])).

fof(f78,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f348,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = X3
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f347])).

fof(f386,plain,
    ( spl3_22
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f320,f306,f43,f384])).

fof(f320,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)
    | ~ spl3_3
    | ~ spl3_18 ),
    inference(superposition,[],[f44,f307])).

fof(f349,plain,
    ( spl3_20
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f271,f259,f155,f347])).

fof(f259,plain,
    ( spl3_16
  <=> ! [X13,X14] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f271,plain,
    ( ! [X4,X3] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = X3
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(superposition,[],[f260,f156])).

fof(f260,plain,
    ( ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f259])).

fof(f308,plain,
    ( spl3_18
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f288,f259,f159,f155,f306])).

fof(f159,plain,
    ( spl3_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f288,plain,
    ( ! [X12,X11] : k2_xboole_0(k4_xboole_0(X11,X12),X11) = X11
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_16 ),
    inference(forward_demodulation,[],[f267,f239])).

fof(f239,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3)))
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(superposition,[],[f160,f156])).

fof(f160,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f159])).

fof(f267,plain,
    ( ! [X12,X11] : k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X11))),X11) = X11
    | ~ spl3_12
    | ~ spl3_16 ),
    inference(superposition,[],[f260,f156])).

fof(f261,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f255,f163,f159,f39,f259])).

fof(f163,plain,
    ( spl3_14
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f255,plain,
    ( ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13
    | ~ spl3_2
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f244,f164])).

fof(f164,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f163])).

fof(f244,plain,
    ( ! [X14,X13] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,X14))
    | ~ spl3_2
    | ~ spl3_13 ),
    inference(superposition,[],[f40,f160])).

fof(f165,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f30,f163])).

fof(f30,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f23,f19])).

fof(f23,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f161,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f29,f159])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f21,f19])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f157,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f28,f155])).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f17,f19,f19])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f153,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f25,f151])).

fof(f83,plain,
    ( spl3_7
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f64,f52,f39,f81])).

fof(f64,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f62,f40])).

fof(f62,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f40,f53])).

fof(f79,plain,
    ( spl3_6
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f63,f52,f39,f77])).

fof(f63,plain,
    ( ! [X4,X5] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f61,f53])).

fof(f61,plain,
    ( ! [X4,X5] : k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4)
    | ~ spl3_2
    | ~ spl3_4 ),
    inference(superposition,[],[f53,f40])).

fof(f58,plain,
    ( spl3_5
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f50,f43,f39,f56])).

fof(f50,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f49,f40])).

fof(f49,plain,
    ( ! [X0,X1] : k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))
    | ~ spl3_2
    | ~ spl3_3 ),
    inference(superposition,[],[f40,f44])).

fof(f54,plain,
    ( spl3_4
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f46,f43,f35,f52])).

fof(f35,plain,
    ( spl3_1
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f46,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(superposition,[],[f44,f36])).

fof(f36,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f35])).

fof(f45,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f22,f43])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f41,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f20,f39])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f37,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f18,f35])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:44:49 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.41  % (17352)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.41  % (17352)Refutation not found, incomplete strategy% (17352)------------------------------
% 0.20/0.41  % (17352)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.41  % (17352)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.41  
% 0.20/0.41  % (17352)Memory used [KB]: 10618
% 0.20/0.41  % (17352)Time elapsed: 0.004 s
% 0.20/0.41  % (17352)------------------------------
% 0.20/0.41  % (17352)------------------------------
% 0.20/0.44  % (17348)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.45  % (17341)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (17349)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (17343)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (17347)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (17353)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (17342)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.47  % (17355)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (17354)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.47  % (17356)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.47  % (17358)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (17351)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.48  % (17345)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (17344)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.49  % (17346)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (17350)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.50  % (17357)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.52/0.58  % (17348)Refutation found. Thanks to Tanya!
% 1.52/0.58  % SZS status Theorem for theBenchmark
% 1.52/0.58  % SZS output start Proof for theBenchmark
% 1.52/0.58  fof(f7008,plain,(
% 1.52/0.58    $false),
% 1.52/0.58    inference(avatar_sat_refutation,[],[f37,f41,f45,f54,f58,f79,f83,f153,f157,f161,f165,f261,f308,f349,f386,f390,f472,f509,f985,f3185,f3942,f4943,f6786])).
% 1.52/0.58  fof(f6786,plain,(
% 1.52/0.58    ~spl3_18 | spl3_34 | ~spl3_57 | ~spl3_70 | ~spl3_88),
% 1.52/0.58    inference(avatar_contradiction_clause,[],[f6785])).
% 1.52/0.58  fof(f6785,plain,(
% 1.52/0.58    $false | (~spl3_18 | spl3_34 | ~spl3_57 | ~spl3_70 | ~spl3_88)),
% 1.52/0.58    inference(subsumption_resolution,[],[f984,f6784])).
% 1.52/0.58  fof(f6784,plain,(
% 1.52/0.58    ( ! [X64,X65,X63] : (k4_xboole_0(X63,k4_xboole_0(X64,X65)) = k2_xboole_0(k4_xboole_0(X63,X64),k4_xboole_0(X63,k4_xboole_0(X63,X65)))) ) | (~spl3_18 | ~spl3_57 | ~spl3_70 | ~spl3_88)),
% 1.52/0.58    inference(forward_demodulation,[],[f6600,f4168])).
% 1.52/0.58  fof(f4168,plain,(
% 1.52/0.58    ( ! [X41,X42,X40] : (k4_xboole_0(X40,k4_xboole_0(X41,X42)) = k4_xboole_0(X40,k4_xboole_0(X40,k2_xboole_0(k4_xboole_0(X40,X41),X42)))) ) | (~spl3_57 | ~spl3_70)),
% 1.52/0.58    inference(forward_demodulation,[],[f3994,f3941])).
% 1.52/0.58  fof(f3941,plain,(
% 1.52/0.58    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X11,X10),X12)) = k4_xboole_0(X10,X12)) ) | ~spl3_70),
% 1.52/0.58    inference(avatar_component_clause,[],[f3940])).
% 1.52/0.58  fof(f3940,plain,(
% 1.52/0.58    spl3_70 <=> ! [X11,X10,X12] : k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X11,X10),X12)) = k4_xboole_0(X10,X12)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 1.52/0.58  fof(f3994,plain,(
% 1.52/0.58    ( ! [X41,X42,X40] : (k4_xboole_0(X40,k2_xboole_0(k4_xboole_0(X40,X40),k4_xboole_0(X41,X42))) = k4_xboole_0(X40,k4_xboole_0(X40,k2_xboole_0(k4_xboole_0(X40,X41),X42)))) ) | ~spl3_57),
% 1.52/0.58    inference(superposition,[],[f3184,f3184])).
% 1.52/0.58  fof(f3184,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) ) | ~spl3_57),
% 1.52/0.58    inference(avatar_component_clause,[],[f3183])).
% 1.52/0.58  fof(f3183,plain,(
% 1.52/0.58    spl3_57 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 1.52/0.58  fof(f6600,plain,(
% 1.52/0.58    ( ! [X64,X65,X63] : (k2_xboole_0(k4_xboole_0(X63,X64),k4_xboole_0(X63,k4_xboole_0(X63,X65))) = k4_xboole_0(X63,k4_xboole_0(X63,k2_xboole_0(k4_xboole_0(X63,X64),X65)))) ) | (~spl3_18 | ~spl3_88)),
% 1.52/0.58    inference(superposition,[],[f4942,f307])).
% 1.52/0.58  fof(f307,plain,(
% 1.52/0.58    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X11,X12),X11) = X11) ) | ~spl3_18),
% 1.52/0.58    inference(avatar_component_clause,[],[f306])).
% 1.52/0.58  fof(f306,plain,(
% 1.52/0.58    spl3_18 <=> ! [X11,X12] : k2_xboole_0(k4_xboole_0(X11,X12),X11) = X11),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.52/0.58  fof(f4942,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) ) | ~spl3_88),
% 1.52/0.58    inference(avatar_component_clause,[],[f4941])).
% 1.52/0.58  fof(f4941,plain,(
% 1.52/0.58    spl3_88 <=> ! [X1,X0,X2] : k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2)))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 1.52/0.58  fof(f984,plain,(
% 1.52/0.58    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2))) | spl3_34),
% 1.52/0.58    inference(avatar_component_clause,[],[f982])).
% 1.52/0.58  fof(f982,plain,(
% 1.52/0.58    spl3_34 <=> k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) = k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.52/0.58  fof(f4943,plain,(
% 1.52/0.58    spl3_88 | ~spl3_4 | ~spl3_11),
% 1.52/0.58    inference(avatar_split_clause,[],[f176,f151,f52,f4941])).
% 1.52/0.58  fof(f52,plain,(
% 1.52/0.58    spl3_4 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.52/0.58  fof(f151,plain,(
% 1.52/0.58    spl3_11 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.52/0.58  fof(f176,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X1,k2_xboole_0(X0,X2)))) ) | (~spl3_4 | ~spl3_11)),
% 1.52/0.58    inference(backward_demodulation,[],[f32,f175])).
% 1.52/0.58  fof(f175,plain,(
% 1.52/0.58    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(X4,k2_xboole_0(X3,X5))) ) | (~spl3_4 | ~spl3_11)),
% 1.52/0.58    inference(forward_demodulation,[],[f167,f152])).
% 1.52/0.58  fof(f152,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl3_11),
% 1.52/0.58    inference(avatar_component_clause,[],[f151])).
% 1.52/0.58  fof(f167,plain,(
% 1.52/0.58    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X4),k2_xboole_0(X3,X5)) = k4_xboole_0(k4_xboole_0(X4,X3),X5)) ) | (~spl3_4 | ~spl3_11)),
% 1.52/0.58    inference(superposition,[],[f152,f53])).
% 1.52/0.58  fof(f53,plain,(
% 1.52/0.58    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | ~spl3_4),
% 1.52/0.58    inference(avatar_component_clause,[],[f52])).
% 1.52/0.58  fof(f32,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X1,k4_xboole_0(X1,X2))) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2)))) )),
% 1.52/0.58    inference(definition_unfolding,[],[f26,f19,f19])).
% 1.52/0.58  fof(f19,plain,(
% 1.52/0.58    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.52/0.58    inference(cnf_transformation,[],[f8])).
% 1.52/0.58  fof(f8,axiom,(
% 1.52/0.58    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.52/0.58  fof(f26,plain,(
% 1.52/0.58    ( ! [X2,X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))) )),
% 1.52/0.58    inference(cnf_transformation,[],[f3])).
% 1.52/0.58  fof(f3,axiom,(
% 1.52/0.58    ! [X0,X1,X2] : k2_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X2))),
% 1.52/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_xboole_1)).
% 1.52/0.58  fof(f3942,plain,(
% 1.52/0.58    spl3_70 | ~spl3_11 | ~spl3_25),
% 1.52/0.58    inference(avatar_split_clause,[],[f524,f507,f151,f3940])).
% 1.52/0.58  fof(f507,plain,(
% 1.52/0.58    spl3_25 <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2),
% 1.52/0.58    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.52/0.58  fof(f524,plain,(
% 1.52/0.58    ( ! [X12,X10,X11] : (k4_xboole_0(X10,k2_xboole_0(k4_xboole_0(X11,X10),X12)) = k4_xboole_0(X10,X12)) ) | (~spl3_11 | ~spl3_25)),
% 1.52/0.58    inference(superposition,[],[f152,f508])).
% 1.52/0.58  fof(f508,plain,(
% 1.52/0.58    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | ~spl3_25),
% 1.52/0.58    inference(avatar_component_clause,[],[f507])).
% 1.52/0.58  fof(f3185,plain,(
% 1.52/0.58    spl3_57),
% 1.52/0.58    inference(avatar_split_clause,[],[f33,f3183])).
% 1.52/0.59  fof(f33,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(X0,k2_xboole_0(k4_xboole_0(X0,X1),X2))) )),
% 1.52/0.59    inference(backward_demodulation,[],[f31,f25])).
% 1.52/0.59  fof(f25,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.52/0.59    inference(cnf_transformation,[],[f6])).
% 1.52/0.59  fof(f6,axiom,(
% 1.52/0.59    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.52/0.59  fof(f31,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X1,X2))) = k4_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),X2)) )),
% 1.52/0.59    inference(definition_unfolding,[],[f24,f19,f19])).
% 1.52/0.59  fof(f24,plain,(
% 1.52/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f9])).
% 1.52/0.59  fof(f9,axiom,(
% 1.52/0.59    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2)),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).
% 1.52/0.59  fof(f985,plain,(
% 1.52/0.59    ~spl3_34),
% 1.52/0.59    inference(avatar_split_clause,[],[f27,f982])).
% 1.52/0.59  fof(f27,plain,(
% 1.52/0.59    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK2)))),
% 1.52/0.59    inference(definition_unfolding,[],[f16,f19])).
% 1.52/0.59  fof(f16,plain,(
% 1.52/0.59    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.52/0.59    inference(cnf_transformation,[],[f15])).
% 1.52/0.59  fof(f15,plain,(
% 1.52/0.59    k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.52/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f14])).
% 1.52/0.59  fof(f14,plain,(
% 1.52/0.59    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) => k4_xboole_0(sK0,k4_xboole_0(sK1,sK2)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK2))),
% 1.52/0.59    introduced(choice_axiom,[])).
% 1.52/0.59  fof(f13,plain,(
% 1.52/0.59    ? [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) != k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.52/0.59    inference(ennf_transformation,[],[f12])).
% 1.52/0.59  fof(f12,negated_conjecture,(
% 1.52/0.59    ~! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.52/0.59    inference(negated_conjecture,[],[f11])).
% 1.52/0.59  fof(f11,conjecture,(
% 1.52/0.59    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 1.52/0.59  fof(f509,plain,(
% 1.52/0.59    spl3_25 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_11 | ~spl3_12 | ~spl3_22 | ~spl3_24),
% 1.52/0.59    inference(avatar_split_clause,[],[f493,f470,f384,f155,f151,f81,f56,f52,f43,f39,f507])).
% 1.52/0.59  fof(f39,plain,(
% 1.52/0.59    spl3_2 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.52/0.59  fof(f43,plain,(
% 1.52/0.59    spl3_3 <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.52/0.59  fof(f56,plain,(
% 1.52/0.59    spl3_5 <=> ! [X1,X0] : k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.52/0.59  fof(f81,plain,(
% 1.52/0.59    spl3_7 <=> ! [X1,X2] : k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.52/0.59  fof(f155,plain,(
% 1.52/0.59    spl3_12 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.52/0.59  fof(f384,plain,(
% 1.52/0.59    spl3_22 <=> ! [X7,X6] : k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.52/0.59  fof(f470,plain,(
% 1.52/0.59    spl3_24 <=> ! [X5,X4] : k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.52/0.59  fof(f493,plain,(
% 1.52/0.59    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_11 | ~spl3_12 | ~spl3_22 | ~spl3_24)),
% 1.52/0.59    inference(backward_demodulation,[],[f425,f492])).
% 1.52/0.59  fof(f492,plain,(
% 1.52/0.59    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,X14)) = X15) ) | (~spl3_2 | ~spl3_24)),
% 1.52/0.59    inference(forward_demodulation,[],[f477,f471])).
% 1.52/0.59  fof(f471,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5) ) | ~spl3_24),
% 1.52/0.59    inference(avatar_component_clause,[],[f470])).
% 1.52/0.59  fof(f477,plain,(
% 1.52/0.59    ( ! [X14,X15] : (k4_xboole_0(X15,k4_xboole_0(X14,X14)) = k2_xboole_0(k4_xboole_0(X14,X14),X15)) ) | (~spl3_2 | ~spl3_24)),
% 1.52/0.59    inference(superposition,[],[f471,f40])).
% 1.52/0.59  fof(f40,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl3_2),
% 1.52/0.59    inference(avatar_component_clause,[],[f39])).
% 1.52/0.59  fof(f425,plain,(
% 1.52/0.59    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k4_xboole_0(X2,k4_xboole_0(X2,X2))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_5 | ~spl3_7 | ~spl3_11 | ~spl3_12 | ~spl3_22)),
% 1.52/0.59    inference(backward_demodulation,[],[f222,f423])).
% 1.52/0.59  fof(f423,plain,(
% 1.52/0.59    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(X5,X5)) ) | (~spl3_3 | ~spl3_5 | ~spl3_7 | ~spl3_11 | ~spl3_22)),
% 1.52/0.59    inference(backward_demodulation,[],[f93,f421])).
% 1.52/0.59  fof(f421,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X0) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | (~spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_22)),
% 1.52/0.59    inference(backward_demodulation,[],[f411,f398])).
% 1.52/0.59  fof(f398,plain,(
% 1.52/0.59    ( ! [X2,X1] : (k4_xboole_0(X1,X1) = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | (~spl3_11 | ~spl3_22)),
% 1.52/0.59    inference(superposition,[],[f385,f152])).
% 1.52/0.59  fof(f385,plain,(
% 1.52/0.59    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)) ) | ~spl3_22),
% 1.52/0.59    inference(avatar_component_clause,[],[f384])).
% 1.52/0.59  fof(f411,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k2_xboole_0(X1,X0)) = k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | (~spl3_3 | ~spl3_5 | ~spl3_11 | ~spl3_22)),
% 1.52/0.59    inference(forward_demodulation,[],[f410,f57])).
% 1.52/0.59  fof(f57,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) ) | ~spl3_5),
% 1.52/0.59    inference(avatar_component_clause,[],[f56])).
% 1.52/0.59  fof(f410,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(X0,k2_xboole_0(X1,k2_xboole_0(X0,X1)))) ) | (~spl3_3 | ~spl3_11 | ~spl3_22)),
% 1.52/0.59    inference(forward_demodulation,[],[f391,f152])).
% 1.52/0.59  fof(f391,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),k2_xboole_0(X0,X1)) = k4_xboole_0(k4_xboole_0(X0,X1),k2_xboole_0(X0,X1))) ) | (~spl3_3 | ~spl3_22)),
% 1.52/0.59    inference(superposition,[],[f385,f44])).
% 1.52/0.59  fof(f44,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) ) | ~spl3_3),
% 1.52/0.59    inference(avatar_component_clause,[],[f43])).
% 1.52/0.59  fof(f93,plain,(
% 1.52/0.59    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) ) | (~spl3_3 | ~spl3_7)),
% 1.52/0.59    inference(superposition,[],[f44,f82])).
% 1.52/0.59  fof(f82,plain,(
% 1.52/0.59    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) ) | ~spl3_7),
% 1.52/0.59    inference(avatar_component_clause,[],[f81])).
% 1.52/0.59  fof(f222,plain,(
% 1.52/0.59    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X2,X3))) = k4_xboole_0(X2,k4_xboole_0(X3,X2))) ) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 1.52/0.59    inference(forward_demodulation,[],[f203,f48])).
% 1.52/0.59  fof(f48,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k4_xboole_0(X4,k4_xboole_0(X5,X4)) = k4_xboole_0(k2_xboole_0(X4,X5),k4_xboole_0(X5,X4))) ) | (~spl3_2 | ~spl3_3)),
% 1.52/0.59    inference(superposition,[],[f44,f40])).
% 1.52/0.59  fof(f203,plain,(
% 1.52/0.59    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X2,k2_xboole_0(X2,X3))) = k4_xboole_0(k2_xboole_0(X2,X3),k4_xboole_0(X3,X2))) ) | (~spl3_4 | ~spl3_12)),
% 1.52/0.59    inference(superposition,[],[f156,f53])).
% 1.52/0.59  fof(f156,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl3_12),
% 1.52/0.59    inference(avatar_component_clause,[],[f155])).
% 1.52/0.59  fof(f472,plain,(
% 1.52/0.59    spl3_24 | ~spl3_11 | ~spl3_22 | ~spl3_23),
% 1.52/0.59    inference(avatar_split_clause,[],[f420,f388,f384,f151,f470])).
% 1.52/0.59  fof(f388,plain,(
% 1.52/0.59    spl3_23 <=> ! [X5,X4] : k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),X5) = X5),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.52/0.59  fof(f420,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,X4),X5) = X5) ) | (~spl3_11 | ~spl3_22 | ~spl3_23)),
% 1.52/0.59    inference(backward_demodulation,[],[f389,f398])).
% 1.52/0.59  fof(f389,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),X5) = X5) ) | ~spl3_23),
% 1.52/0.59    inference(avatar_component_clause,[],[f388])).
% 1.52/0.59  fof(f390,plain,(
% 1.52/0.59    spl3_23 | ~spl3_2 | ~spl3_6 | ~spl3_11 | ~spl3_20),
% 1.52/0.59    inference(avatar_split_clause,[],[f377,f347,f151,f77,f39,f388])).
% 1.52/0.59  fof(f77,plain,(
% 1.52/0.59    spl3_6 <=> ! [X5,X4] : k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.52/0.59  fof(f347,plain,(
% 1.52/0.59    spl3_20 <=> ! [X3,X4] : k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = X3),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.52/0.59  fof(f377,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,X4)),X5) = X5) ) | (~spl3_2 | ~spl3_6 | ~spl3_11 | ~spl3_20)),
% 1.52/0.59    inference(forward_demodulation,[],[f376,f40])).
% 1.52/0.59  fof(f376,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(X4,k2_xboole_0(X5,k4_xboole_0(X4,X5))),X5) = X5) ) | (~spl3_6 | ~spl3_11 | ~spl3_20)),
% 1.52/0.59    inference(forward_demodulation,[],[f356,f152])).
% 1.52/0.59  fof(f356,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k2_xboole_0(k4_xboole_0(k4_xboole_0(X4,X5),k4_xboole_0(X4,X5)),X5) = X5) ) | (~spl3_6 | ~spl3_20)),
% 1.52/0.59    inference(superposition,[],[f348,f78])).
% 1.52/0.59  fof(f78,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) ) | ~spl3_6),
% 1.52/0.59    inference(avatar_component_clause,[],[f77])).
% 1.52/0.59  fof(f348,plain,(
% 1.52/0.59    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = X3) ) | ~spl3_20),
% 1.52/0.59    inference(avatar_component_clause,[],[f347])).
% 1.52/0.59  fof(f386,plain,(
% 1.52/0.59    spl3_22 | ~spl3_3 | ~spl3_18),
% 1.52/0.59    inference(avatar_split_clause,[],[f320,f306,f43,f384])).
% 1.52/0.59  fof(f320,plain,(
% 1.52/0.59    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),X6) = k4_xboole_0(X6,X6)) ) | (~spl3_3 | ~spl3_18)),
% 1.52/0.59    inference(superposition,[],[f44,f307])).
% 1.52/0.59  fof(f349,plain,(
% 1.52/0.59    spl3_20 | ~spl3_12 | ~spl3_16),
% 1.52/0.59    inference(avatar_split_clause,[],[f271,f259,f155,f347])).
% 1.52/0.59  fof(f259,plain,(
% 1.52/0.59    spl3_16 <=> ! [X13,X14] : k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.52/0.59  fof(f271,plain,(
% 1.52/0.59    ( ! [X4,X3] : (k2_xboole_0(k4_xboole_0(X4,k4_xboole_0(X4,X3)),X3) = X3) ) | (~spl3_12 | ~spl3_16)),
% 1.52/0.59    inference(superposition,[],[f260,f156])).
% 1.52/0.59  fof(f260,plain,(
% 1.52/0.59    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13) ) | ~spl3_16),
% 1.52/0.59    inference(avatar_component_clause,[],[f259])).
% 1.52/0.59  fof(f308,plain,(
% 1.52/0.59    spl3_18 | ~spl3_12 | ~spl3_13 | ~spl3_16),
% 1.52/0.59    inference(avatar_split_clause,[],[f288,f259,f159,f155,f306])).
% 1.52/0.59  fof(f159,plain,(
% 1.52/0.59    spl3_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.52/0.59  fof(f288,plain,(
% 1.52/0.59    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X11,X12),X11) = X11) ) | (~spl3_12 | ~spl3_13 | ~spl3_16)),
% 1.52/0.59    inference(forward_demodulation,[],[f267,f239])).
% 1.52/0.59  fof(f239,plain,(
% 1.52/0.59    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k4_xboole_0(X3,k4_xboole_0(X4,k4_xboole_0(X4,X3)))) ) | (~spl3_12 | ~spl3_13)),
% 1.52/0.59    inference(superposition,[],[f160,f156])).
% 1.52/0.59  fof(f160,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl3_13),
% 1.52/0.59    inference(avatar_component_clause,[],[f159])).
% 1.52/0.59  fof(f267,plain,(
% 1.52/0.59    ( ! [X12,X11] : (k2_xboole_0(k4_xboole_0(X11,k4_xboole_0(X12,k4_xboole_0(X12,X11))),X11) = X11) ) | (~spl3_12 | ~spl3_16)),
% 1.52/0.59    inference(superposition,[],[f260,f156])).
% 1.52/0.59  fof(f261,plain,(
% 1.52/0.59    spl3_16 | ~spl3_2 | ~spl3_13 | ~spl3_14),
% 1.52/0.59    inference(avatar_split_clause,[],[f255,f163,f159,f39,f259])).
% 1.52/0.59  fof(f163,plain,(
% 1.52/0.59    spl3_14 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.52/0.59  fof(f255,plain,(
% 1.52/0.59    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = X13) ) | (~spl3_2 | ~spl3_13 | ~spl3_14)),
% 1.52/0.59    inference(forward_demodulation,[],[f244,f164])).
% 1.52/0.59  fof(f164,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl3_14),
% 1.52/0.59    inference(avatar_component_clause,[],[f163])).
% 1.52/0.59  fof(f244,plain,(
% 1.52/0.59    ( ! [X14,X13] : (k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),X13) = k2_xboole_0(k4_xboole_0(X13,k4_xboole_0(X13,X14)),k4_xboole_0(X13,X14))) ) | (~spl3_2 | ~spl3_13)),
% 1.52/0.59    inference(superposition,[],[f40,f160])).
% 1.52/0.59  fof(f165,plain,(
% 1.52/0.59    spl3_14),
% 1.52/0.59    inference(avatar_split_clause,[],[f30,f163])).
% 1.52/0.59  fof(f30,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.52/0.59    inference(definition_unfolding,[],[f23,f19])).
% 1.52/0.59  fof(f23,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.52/0.59    inference(cnf_transformation,[],[f10])).
% 1.52/0.59  fof(f10,axiom,(
% 1.52/0.59    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.52/0.59  fof(f161,plain,(
% 1.52/0.59    spl3_13),
% 1.52/0.59    inference(avatar_split_clause,[],[f29,f159])).
% 1.52/0.59  fof(f29,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 1.52/0.59    inference(definition_unfolding,[],[f21,f19])).
% 1.52/0.59  fof(f21,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.52/0.59    inference(cnf_transformation,[],[f7])).
% 1.52/0.59  fof(f7,axiom,(
% 1.52/0.59    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.52/0.59  fof(f157,plain,(
% 1.52/0.59    spl3_12),
% 1.52/0.59    inference(avatar_split_clause,[],[f28,f155])).
% 1.52/0.59  fof(f28,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 1.52/0.59    inference(definition_unfolding,[],[f17,f19,f19])).
% 1.52/0.59  fof(f17,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f2])).
% 1.52/0.59  fof(f2,axiom,(
% 1.52/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.52/0.59  fof(f153,plain,(
% 1.52/0.59    spl3_11),
% 1.52/0.59    inference(avatar_split_clause,[],[f25,f151])).
% 1.52/0.59  fof(f83,plain,(
% 1.52/0.59    spl3_7 | ~spl3_2 | ~spl3_4),
% 1.52/0.59    inference(avatar_split_clause,[],[f64,f52,f39,f81])).
% 1.52/0.59  fof(f64,plain,(
% 1.52/0.59    ( ! [X2,X1] : (k2_xboole_0(X1,X2) = k2_xboole_0(X1,k2_xboole_0(X1,X2))) ) | (~spl3_2 | ~spl3_4)),
% 1.52/0.59    inference(forward_demodulation,[],[f62,f40])).
% 1.52/0.59  fof(f62,plain,(
% 1.52/0.59    ( ! [X2,X1] : (k2_xboole_0(X1,k2_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X2,X1))) ) | (~spl3_2 | ~spl3_4)),
% 1.52/0.59    inference(superposition,[],[f40,f53])).
% 1.52/0.59  fof(f79,plain,(
% 1.52/0.59    spl3_6 | ~spl3_2 | ~spl3_4),
% 1.52/0.59    inference(avatar_split_clause,[],[f63,f52,f39,f77])).
% 1.52/0.59  fof(f63,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k4_xboole_0(X5,X4) = k4_xboole_0(k4_xboole_0(X5,X4),X4)) ) | (~spl3_2 | ~spl3_4)),
% 1.52/0.59    inference(forward_demodulation,[],[f61,f53])).
% 1.52/0.59  fof(f61,plain,(
% 1.52/0.59    ( ! [X4,X5] : (k4_xboole_0(k4_xboole_0(X5,X4),X4) = k4_xboole_0(k2_xboole_0(X4,X5),X4)) ) | (~spl3_2 | ~spl3_4)),
% 1.52/0.59    inference(superposition,[],[f53,f40])).
% 1.52/0.59  fof(f58,plain,(
% 1.52/0.59    spl3_5 | ~spl3_2 | ~spl3_3),
% 1.52/0.59    inference(avatar_split_clause,[],[f50,f43,f39,f56])).
% 1.52/0.59  fof(f50,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(X1,X0) = k2_xboole_0(X1,k2_xboole_0(X0,X1))) ) | (~spl3_2 | ~spl3_3)),
% 1.52/0.59    inference(forward_demodulation,[],[f49,f40])).
% 1.52/0.59  fof(f49,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(X1,k2_xboole_0(X0,X1)) = k2_xboole_0(X1,k4_xboole_0(X0,X1))) ) | (~spl3_2 | ~spl3_3)),
% 1.52/0.59    inference(superposition,[],[f40,f44])).
% 1.52/0.59  fof(f54,plain,(
% 1.52/0.59    spl3_4 | ~spl3_1 | ~spl3_3),
% 1.52/0.59    inference(avatar_split_clause,[],[f46,f43,f35,f52])).
% 1.52/0.59  fof(f35,plain,(
% 1.52/0.59    spl3_1 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.52/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.52/0.59  fof(f46,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X1,X0),X1)) ) | (~spl3_1 | ~spl3_3)),
% 1.52/0.59    inference(superposition,[],[f44,f36])).
% 1.52/0.59  fof(f36,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl3_1),
% 1.52/0.59    inference(avatar_component_clause,[],[f35])).
% 1.52/0.59  fof(f45,plain,(
% 1.52/0.59    spl3_3),
% 1.52/0.59    inference(avatar_split_clause,[],[f22,f43])).
% 1.52/0.59  fof(f22,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f5])).
% 1.52/0.59  fof(f5,axiom,(
% 1.52/0.59    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 1.52/0.59  fof(f41,plain,(
% 1.52/0.59    spl3_2),
% 1.52/0.59    inference(avatar_split_clause,[],[f20,f39])).
% 1.52/0.59  fof(f20,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.52/0.59    inference(cnf_transformation,[],[f4])).
% 1.52/0.59  fof(f4,axiom,(
% 1.52/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.52/0.59  fof(f37,plain,(
% 1.52/0.59    spl3_1),
% 1.52/0.59    inference(avatar_split_clause,[],[f18,f35])).
% 1.52/0.59  fof(f18,plain,(
% 1.52/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.52/0.59    inference(cnf_transformation,[],[f1])).
% 1.52/0.59  fof(f1,axiom,(
% 1.52/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.52/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.52/0.59  % SZS output end Proof for theBenchmark
% 1.52/0.59  % (17348)------------------------------
% 1.52/0.59  % (17348)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.52/0.59  % (17348)Termination reason: Refutation
% 1.52/0.59  
% 1.52/0.59  % (17348)Memory used [KB]: 11641
% 1.52/0.59  % (17348)Time elapsed: 0.182 s
% 1.52/0.59  % (17348)------------------------------
% 1.52/0.59  % (17348)------------------------------
% 1.52/0.59  % (17340)Success in time 0.238 s
%------------------------------------------------------------------------------
