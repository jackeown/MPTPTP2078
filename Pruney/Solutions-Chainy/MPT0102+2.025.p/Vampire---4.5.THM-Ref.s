%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:31:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 219 expanded)
%              Number of leaves         :   29 (  94 expanded)
%              Depth                    :   11
%              Number of atoms          :  196 ( 351 expanded)
%              Number of equality atoms :   91 ( 201 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    7 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1048,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f118,f134,f138,f142,f483,f520,f568,f655,f715,f881,f893,f1042])).

fof(f1042,plain,
    ( ~ spl2_3
    | ~ spl2_12
    | spl2_34
    | ~ spl2_37 ),
    inference(avatar_contradiction_clause,[],[f1041])).

fof(f1041,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_12
    | spl2_34
    | ~ spl2_37 ),
    inference(subsumption_resolution,[],[f880,f1040])).

fof(f1040,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(X15,X16) = k4_xboole_0(k2_xboole_0(X15,X17),k4_xboole_0(k2_xboole_0(X15,X17),k4_xboole_0(X15,X16)))
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_37 ),
    inference(forward_demodulation,[],[f1027,f56])).

fof(f56,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl2_3
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f1027,plain,
    ( ! [X17,X15,X16] : k4_xboole_0(k2_xboole_0(X15,X17),k4_xboole_0(k2_xboole_0(X15,X17),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(X15,X16),k1_xboole_0)
    | ~ spl2_12
    | ~ spl2_37 ),
    inference(superposition,[],[f137,f892])).

fof(f892,plain,
    ( ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X3,X2))
    | ~ spl2_37 ),
    inference(avatar_component_clause,[],[f891])).

fof(f891,plain,
    ( spl2_37
  <=> ! [X3,X2,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).

fof(f137,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_12
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f880,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_34 ),
    inference(avatar_component_clause,[],[f878])).

fof(f878,plain,
    ( spl2_34
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f893,plain,
    ( spl2_37
    | ~ spl2_4
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f845,f713,f59,f891])).

fof(f59,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f713,plain,
    ( spl2_33
  <=> ! [X25,X23,X24] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k2_xboole_0(X25,X23)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f845,plain,
    ( ! [X4,X2,X3] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X3,X2))
    | ~ spl2_4
    | ~ spl2_33 ),
    inference(superposition,[],[f714,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f714,plain,
    ( ! [X24,X23,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k2_xboole_0(X25,X23))
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f713])).

fof(f881,plain,
    ( ~ spl2_34
    | ~ spl2_11
    | spl2_23
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f564,f518,f480,f132,f878])).

fof(f132,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f480,plain,
    ( spl2_23
  <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f518,plain,
    ( spl2_25
  <=> ! [X11,X10] : k2_xboole_0(X10,k4_xboole_0(X10,X11)) = X10 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f564,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | ~ spl2_11
    | spl2_23
    | ~ spl2_25 ),
    inference(backward_demodulation,[],[f482,f554])).

fof(f554,plain,
    ( ! [X10,X11,X9] : k2_xboole_0(X9,X10) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(k2_xboole_0(X9,X10),X11)))
    | ~ spl2_11
    | ~ spl2_25 ),
    inference(superposition,[],[f519,f133])).

fof(f133,plain,
    ( ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f132])).

fof(f519,plain,
    ( ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X10,X11)) = X10
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f518])).

fof(f482,plain,
    ( k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f480])).

fof(f715,plain,
    ( spl2_33
    | ~ spl2_25
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f664,f653,f518,f713])).

fof(f653,plain,
    ( spl2_29
  <=> ! [X18,X20,X19] : k1_xboole_0 = k4_xboole_0(X20,k2_xboole_0(X18,k2_xboole_0(X19,X20))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f664,plain,
    ( ! [X24,X23,X25] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k2_xboole_0(X25,X23))
    | ~ spl2_25
    | ~ spl2_29 ),
    inference(superposition,[],[f654,f519])).

fof(f654,plain,
    ( ! [X19,X20,X18] : k1_xboole_0 = k4_xboole_0(X20,k2_xboole_0(X18,k2_xboole_0(X19,X20)))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f653])).

fof(f655,plain,
    ( spl2_29
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(avatar_split_clause,[],[f579,f566,f132,f653])).

fof(f566,plain,
    ( spl2_26
  <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f579,plain,
    ( ! [X19,X20,X18] : k1_xboole_0 = k4_xboole_0(X20,k2_xboole_0(X18,k2_xboole_0(X19,X20)))
    | ~ spl2_11
    | ~ spl2_26 ),
    inference(superposition,[],[f567,f133])).

fof(f567,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f566])).

fof(f568,plain,
    ( spl2_26
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f466,f140,f116,f51,f566])).

fof(f51,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f116,plain,
    ( spl2_10
  <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f140,plain,
    ( spl2_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f466,plain,
    ( ! [X2,X3] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl2_2
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f445,f52])).

fof(f52,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f51])).

fof(f445,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X2) = k4_xboole_0(X2,k2_xboole_0(X3,X2))
    | ~ spl2_10
    | ~ spl2_13 ),
    inference(superposition,[],[f141,f117])).

fof(f117,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f116])).

fof(f141,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f140])).

fof(f520,plain,
    ( spl2_25
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f471,f140,f136,f67,f518])).

fof(f67,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f471,plain,
    ( ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X10,X11)) = X10
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(backward_demodulation,[],[f246,f446])).

fof(f446,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4)))
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(superposition,[],[f141,f137])).

fof(f246,plain,
    ( ! [X10,X11] : k2_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10)))) = X10
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(superposition,[],[f68,f137])).

fof(f68,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f67])).

fof(f483,plain,(
    ~ spl2_23 ),
    inference(avatar_split_clause,[],[f45,f480])).

fof(f45,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f44,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

fof(f44,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) ),
    inference(backward_demodulation,[],[f43,f38])).

fof(f38,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f28,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f43,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f42,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f42,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f32,f35])).

fof(f35,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0)) ),
    inference(definition_unfolding,[],[f23,f27,f27])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f32,plain,(
    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)))) ),
    inference(definition_unfolding,[],[f19,f27,f31,f31])).

fof(f31,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f29,f27])).

fof(f29,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f19,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).

fof(f17,plain,
    ( ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))
   => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f142,plain,(
    spl2_13 ),
    inference(avatar_split_clause,[],[f38,f140])).

fof(f138,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f35,f136])).

fof(f134,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f30,f132])).

fof(f118,plain,
    ( spl2_10
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f71,f63,f59,f116])).

fof(f63,plain,
    ( spl2_5
  <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f71,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f64,f60])).

fof(f64,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f69,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f37,f67])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f26,f27])).

fof(f26,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f65,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f36,f63])).

fof(f36,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0 ),
    inference(definition_unfolding,[],[f25,f27])).

fof(f25,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

fof(f61,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f24,f59])).

fof(f57,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f41,f55])).

fof(f41,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(backward_demodulation,[],[f34,f40])).

fof(f40,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f39,f22])).

fof(f22,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] : k2_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X0,X0),X0) ),
    inference(backward_demodulation,[],[f33,f34])).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0))) ),
    inference(definition_unfolding,[],[f20,f31])).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0 ),
    inference(definition_unfolding,[],[f21,f27])).

fof(f21,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f53,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f40,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n003.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 21:07:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (9262)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.46  % (9263)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (9264)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (9272)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.47  % (9274)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.48  % (9270)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (9260)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (9269)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.48  % (9265)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (9273)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.48  % (9261)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (9275)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (9271)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (9267)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (9271)Refutation not found, incomplete strategy% (9271)------------------------------
% 0.21/0.49  % (9271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (9271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (9271)Memory used [KB]: 10490
% 0.21/0.49  % (9271)Time elapsed: 0.072 s
% 0.21/0.49  % (9271)------------------------------
% 0.21/0.49  % (9271)------------------------------
% 0.21/0.49  % (9268)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (9277)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.50  % (9276)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (9266)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (9267)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f1048,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f69,f118,f134,f138,f142,f483,f520,f568,f655,f715,f881,f893,f1042])).
% 0.21/0.54  fof(f1042,plain,(
% 0.21/0.54    ~spl2_3 | ~spl2_12 | spl2_34 | ~spl2_37),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f1041])).
% 0.21/0.54  fof(f1041,plain,(
% 0.21/0.54    $false | (~spl2_3 | ~spl2_12 | spl2_34 | ~spl2_37)),
% 0.21/0.54    inference(subsumption_resolution,[],[f880,f1040])).
% 0.21/0.54  fof(f1040,plain,(
% 0.21/0.54    ( ! [X17,X15,X16] : (k4_xboole_0(X15,X16) = k4_xboole_0(k2_xboole_0(X15,X17),k4_xboole_0(k2_xboole_0(X15,X17),k4_xboole_0(X15,X16)))) ) | (~spl2_3 | ~spl2_12 | ~spl2_37)),
% 0.21/0.54    inference(forward_demodulation,[],[f1027,f56])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    spl2_3 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.54  fof(f1027,plain,(
% 0.21/0.54    ( ! [X17,X15,X16] : (k4_xboole_0(k2_xboole_0(X15,X17),k4_xboole_0(k2_xboole_0(X15,X17),k4_xboole_0(X15,X16))) = k4_xboole_0(k4_xboole_0(X15,X16),k1_xboole_0)) ) | (~spl2_12 | ~spl2_37)),
% 0.21/0.54    inference(superposition,[],[f137,f892])).
% 0.21/0.54  fof(f892,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X3,X2))) ) | ~spl2_37),
% 0.21/0.54    inference(avatar_component_clause,[],[f891])).
% 0.21/0.54  fof(f891,plain,(
% 0.21/0.54    spl2_37 <=> ! [X3,X2,X4] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X3,X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_37])])).
% 0.21/0.54  fof(f137,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) ) | ~spl2_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f136])).
% 0.21/0.54  fof(f136,plain,(
% 0.21/0.54    spl2_12 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.54  fof(f880,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_34),
% 0.21/0.54    inference(avatar_component_clause,[],[f878])).
% 0.21/0.54  fof(f878,plain,(
% 0.21/0.54    spl2_34 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.54  fof(f893,plain,(
% 0.21/0.54    spl2_37 | ~spl2_4 | ~spl2_33),
% 0.21/0.54    inference(avatar_split_clause,[],[f845,f713,f59,f891])).
% 0.21/0.54  fof(f59,plain,(
% 0.21/0.54    spl2_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.54  fof(f713,plain,(
% 0.21/0.54    spl2_33 <=> ! [X25,X23,X24] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k2_xboole_0(X25,X23))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.21/0.54  fof(f845,plain,(
% 0.21/0.54    ( ! [X4,X2,X3] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X3,X4),k2_xboole_0(X3,X2))) ) | (~spl2_4 | ~spl2_33)),
% 0.21/0.54    inference(superposition,[],[f714,f60])).
% 0.21/0.54  fof(f60,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f59])).
% 0.21/0.54  fof(f714,plain,(
% 0.21/0.54    ( ! [X24,X23,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k2_xboole_0(X25,X23))) ) | ~spl2_33),
% 0.21/0.54    inference(avatar_component_clause,[],[f713])).
% 0.21/0.54  fof(f881,plain,(
% 0.21/0.54    ~spl2_34 | ~spl2_11 | spl2_23 | ~spl2_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f564,f518,f480,f132,f878])).
% 0.21/0.54  fof(f132,plain,(
% 0.21/0.54    spl2_11 <=> ! [X1,X0,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.54  fof(f480,plain,(
% 0.21/0.54    spl2_23 <=> k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) = k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.21/0.54  fof(f518,plain,(
% 0.21/0.54    spl2_25 <=> ! [X11,X10] : k2_xboole_0(X10,k4_xboole_0(X10,X11)) = X10),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.21/0.54  fof(f564,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | (~spl2_11 | spl2_23 | ~spl2_25)),
% 0.21/0.54    inference(backward_demodulation,[],[f482,f554])).
% 0.21/0.54  fof(f554,plain,(
% 0.21/0.54    ( ! [X10,X11,X9] : (k2_xboole_0(X9,X10) = k2_xboole_0(X9,k2_xboole_0(X10,k4_xboole_0(k2_xboole_0(X9,X10),X11)))) ) | (~spl2_11 | ~spl2_25)),
% 0.21/0.54    inference(superposition,[],[f519,f133])).
% 0.21/0.54  fof(f133,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_11),
% 0.21/0.54    inference(avatar_component_clause,[],[f132])).
% 0.21/0.54  fof(f519,plain,(
% 0.21/0.54    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X10,X11)) = X10) ) | ~spl2_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f518])).
% 0.21/0.54  fof(f482,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))) | spl2_23),
% 0.21/0.54    inference(avatar_component_clause,[],[f480])).
% 0.21/0.54  fof(f715,plain,(
% 0.21/0.54    spl2_33 | ~spl2_25 | ~spl2_29),
% 0.21/0.54    inference(avatar_split_clause,[],[f664,f653,f518,f713])).
% 0.21/0.54  fof(f653,plain,(
% 0.21/0.54    spl2_29 <=> ! [X18,X20,X19] : k1_xboole_0 = k4_xboole_0(X20,k2_xboole_0(X18,k2_xboole_0(X19,X20)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.54  fof(f664,plain,(
% 0.21/0.54    ( ! [X24,X23,X25] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X23,X24),k2_xboole_0(X25,X23))) ) | (~spl2_25 | ~spl2_29)),
% 0.21/0.54    inference(superposition,[],[f654,f519])).
% 0.21/0.54  fof(f654,plain,(
% 0.21/0.54    ( ! [X19,X20,X18] : (k1_xboole_0 = k4_xboole_0(X20,k2_xboole_0(X18,k2_xboole_0(X19,X20)))) ) | ~spl2_29),
% 0.21/0.54    inference(avatar_component_clause,[],[f653])).
% 0.21/0.54  fof(f655,plain,(
% 0.21/0.54    spl2_29 | ~spl2_11 | ~spl2_26),
% 0.21/0.54    inference(avatar_split_clause,[],[f579,f566,f132,f653])).
% 0.21/0.54  fof(f566,plain,(
% 0.21/0.54    spl2_26 <=> ! [X3,X2] : k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.54  fof(f579,plain,(
% 0.21/0.54    ( ! [X19,X20,X18] : (k1_xboole_0 = k4_xboole_0(X20,k2_xboole_0(X18,k2_xboole_0(X19,X20)))) ) | (~spl2_11 | ~spl2_26)),
% 0.21/0.54    inference(superposition,[],[f567,f133])).
% 0.21/0.54  fof(f567,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | ~spl2_26),
% 0.21/0.54    inference(avatar_component_clause,[],[f566])).
% 0.21/0.54  fof(f568,plain,(
% 0.21/0.54    spl2_26 | ~spl2_2 | ~spl2_10 | ~spl2_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f466,f140,f116,f51,f566])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    spl2_2 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.54  fof(f116,plain,(
% 0.21/0.54    spl2_10 <=> ! [X1,X2] : k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.54  fof(f140,plain,(
% 0.21/0.54    spl2_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.54  fof(f466,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k1_xboole_0 = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | (~spl2_2 | ~spl2_10 | ~spl2_13)),
% 0.21/0.54    inference(forward_demodulation,[],[f445,f52])).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_2),
% 0.21/0.54    inference(avatar_component_clause,[],[f51])).
% 0.21/0.54  fof(f445,plain,(
% 0.21/0.54    ( ! [X2,X3] : (k4_xboole_0(X2,X2) = k4_xboole_0(X2,k2_xboole_0(X3,X2))) ) | (~spl2_10 | ~spl2_13)),
% 0.21/0.54    inference(superposition,[],[f141,f117])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1) ) | ~spl2_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f116])).
% 0.21/0.54  fof(f141,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) ) | ~spl2_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f140])).
% 0.21/0.54  fof(f520,plain,(
% 0.21/0.54    spl2_25 | ~spl2_6 | ~spl2_12 | ~spl2_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f471,f140,f136,f67,f518])).
% 0.21/0.54  fof(f67,plain,(
% 0.21/0.54    spl2_6 <=> ! [X1,X0] : k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.54  fof(f471,plain,(
% 0.21/0.54    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X10,X11)) = X10) ) | (~spl2_6 | ~spl2_12 | ~spl2_13)),
% 0.21/0.54    inference(backward_demodulation,[],[f246,f446])).
% 0.21/0.54  fof(f446,plain,(
% 0.21/0.54    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X5,k4_xboole_0(X5,X4)))) ) | (~spl2_12 | ~spl2_13)),
% 0.21/0.54    inference(superposition,[],[f141,f137])).
% 0.21/0.54  fof(f246,plain,(
% 0.21/0.54    ( ! [X10,X11] : (k2_xboole_0(X10,k4_xboole_0(X10,k4_xboole_0(X11,k4_xboole_0(X11,X10)))) = X10) ) | (~spl2_6 | ~spl2_12)),
% 0.21/0.54    inference(superposition,[],[f68,f137])).
% 0.21/0.54  fof(f68,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) ) | ~spl2_6),
% 0.21/0.54    inference(avatar_component_clause,[],[f67])).
% 0.21/0.54  fof(f483,plain,(
% 0.21/0.54    ~spl2_23),
% 0.21/0.54    inference(avatar_split_clause,[],[f45,f480])).
% 0.21/0.54  fof(f45,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(sK0,k2_xboole_0(sK1,k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.21/0.54    inference(backward_demodulation,[],[f44,f30])).
% 0.21/0.54  fof(f30,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : k2_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))),
% 0.21/0.54    inference(backward_demodulation,[],[f43,f38])).
% 0.21/0.54  fof(f38,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f28,f27])).
% 0.21/0.54  fof(f27,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  fof(f28,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))))),
% 0.21/0.54    inference(backward_demodulation,[],[f42,f24])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))))))),
% 0.21/0.54    inference(backward_demodulation,[],[f32,f35])).
% 0.21/0.54  fof(f35,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k4_xboole_0(X1,k4_xboole_0(X1,X0))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f23,f27,f27])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) != k4_xboole_0(k2_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1)),k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k4_xboole_0(k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),k2_xboole_0(sK0,sK1))))),
% 0.21/0.54    inference(definition_unfolding,[],[f19,f27,f31,f31])).
% 0.21/0.54  fof(f31,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f29,f27])).
% 0.21/0.54  fof(f29,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f5])).
% 0.21/0.54  fof(f5,axiom,(
% 0.21/0.54    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.21/0.54  fof(f19,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f18])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f17])).
% 0.21/0.54  fof(f17,plain,(
% 0.21/0.54    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) => k3_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,sK1),k2_xboole_0(sK0,sK1))),
% 0.21/0.54    introduced(choice_axiom,[])).
% 0.21/0.54  fof(f16,plain,(
% 0.21/0.54    ? [X0,X1] : k3_xboole_0(X0,X1) != k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f13])).
% 0.21/0.54  fof(f13,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f12])).
% 0.21/0.54  fof(f12,conjecture,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).
% 0.21/0.54  fof(f142,plain,(
% 0.21/0.54    spl2_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f38,f140])).
% 0.21/0.54  fof(f138,plain,(
% 0.21/0.54    spl2_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f35,f136])).
% 0.21/0.54  fof(f134,plain,(
% 0.21/0.54    spl2_11),
% 0.21/0.54    inference(avatar_split_clause,[],[f30,f132])).
% 0.21/0.54  fof(f118,plain,(
% 0.21/0.54    spl2_10 | ~spl2_4 | ~spl2_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f71,f63,f59,f116])).
% 0.21/0.54  fof(f63,plain,(
% 0.21/0.54    spl2_5 <=> ! [X1,X0] : k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.54  fof(f71,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k4_xboole_0(X1,k4_xboole_0(X1,k2_xboole_0(X2,X1))) = X1) ) | (~spl2_4 | ~spl2_5)),
% 0.21/0.54    inference(superposition,[],[f64,f60])).
% 0.21/0.54  fof(f64,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) ) | ~spl2_5),
% 0.21/0.54    inference(avatar_component_clause,[],[f63])).
% 0.21/0.54  fof(f69,plain,(
% 0.21/0.54    spl2_6),
% 0.21/0.54    inference(avatar_split_clause,[],[f37,f67])).
% 0.21/0.54  fof(f37,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f26,f27])).
% 0.21/0.54  fof(f26,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.54  fof(f65,plain,(
% 0.21/0.54    spl2_5),
% 0.21/0.54    inference(avatar_split_clause,[],[f36,f63])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,k2_xboole_0(X0,X1))) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f25,f27])).
% 0.21/0.54  fof(f25,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f6])).
% 0.21/0.54  fof(f6,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X0,X1)) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).
% 0.21/0.54  fof(f61,plain,(
% 0.21/0.54    spl2_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f24,f59])).
% 0.21/0.54  fof(f57,plain,(
% 0.21/0.54    spl2_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f41,f55])).
% 0.21/0.54  fof(f41,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.54    inference(backward_demodulation,[],[f34,f40])).
% 0.21/0.54  fof(f40,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f39,f22])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0] : (k2_xboole_0(X0,X0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ! [X0] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.54    inference(rectify,[],[f3])).
% 0.21/0.54  fof(f3,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X0,X0),X0)) )),
% 0.21/0.54    inference(backward_demodulation,[],[f33,f34])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X0,X0),k4_xboole_0(X0,k4_xboole_0(X0,X0)))) )),
% 0.21/0.54    inference(definition_unfolding,[],[f20,f31])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0] : (k5_xboole_0(X0,X0) = k1_xboole_0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f11])).
% 0.21/0.54  fof(f11,axiom,(
% 0.21/0.54    ! [X0] : k5_xboole_0(X0,X0) = k1_xboole_0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.54  fof(f34,plain,(
% 0.21/0.54    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(X0,X0)) = X0) )),
% 0.21/0.54    inference(definition_unfolding,[],[f21,f27])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f14])).
% 0.21/0.54  fof(f14,plain,(
% 0.21/0.54    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.54    inference(rectify,[],[f4])).
% 0.21/0.54  fof(f4,axiom,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 0.21/0.54  fof(f53,plain,(
% 0.21/0.54    spl2_2),
% 0.21/0.54    inference(avatar_split_clause,[],[f40,f51])).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (9267)------------------------------
% 0.21/0.54  % (9267)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (9267)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (9267)Memory used [KB]: 6780
% 0.21/0.54  % (9267)Time elapsed: 0.052 s
% 0.21/0.54  % (9267)------------------------------
% 0.21/0.54  % (9267)------------------------------
% 0.21/0.54  % (9259)Success in time 0.179 s
%------------------------------------------------------------------------------
