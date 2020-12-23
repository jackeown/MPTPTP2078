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
% DateTime   : Thu Dec  3 12:30:16 EST 2020

% Result     : Theorem 2.67s
% Output     : Refutation 3.20s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 299 expanded)
%              Number of leaves         :   35 ( 143 expanded)
%              Depth                    :   14
%              Number of atoms          :  391 ( 719 expanded)
%              Number of equality atoms :  115 ( 273 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   3 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9636,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f33,f37,f41,f45,f49,f54,f62,f107,f125,f129,f169,f191,f208,f259,f397,f431,f435,f775,f2514,f3201,f3889,f4801,f7383,f9440,f9619])).

fof(f9619,plain,
    ( ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_25
    | ~ spl2_35
    | spl2_58
    | ~ spl2_69
    | ~ spl2_82
    | ~ spl2_91
    | ~ spl2_103 ),
    inference(avatar_contradiction_clause,[],[f9618])).

fof(f9618,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_25
    | ~ spl2_35
    | spl2_58
    | ~ spl2_69
    | ~ spl2_82
    | ~ spl2_91
    | ~ spl2_103 ),
    inference(subsumption_resolution,[],[f2513,f9617])).

fof(f9617,plain,
    ( ! [X37,X35,X36] : k4_xboole_0(k2_xboole_0(X35,X37),k4_xboole_0(X35,k4_xboole_0(X35,X36))) = k2_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X37,X35))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_25
    | ~ spl2_35
    | ~ spl2_69
    | ~ spl2_82
    | ~ spl2_91
    | ~ spl2_103 ),
    inference(forward_demodulation,[],[f9512,f7485])).

fof(f7485,plain,
    ( ! [X28,X26,X27] : k2_xboole_0(X26,k4_xboole_0(X28,k4_xboole_0(X27,X26))) = k2_xboole_0(X26,k4_xboole_0(X28,X27))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_25
    | ~ spl2_35
    | ~ spl2_69
    | ~ spl2_82
    | ~ spl2_91 ),
    inference(forward_demodulation,[],[f7435,f7260])).

fof(f7260,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X28,X26)) = k2_xboole_0(X26,k4_xboole_0(X27,X28))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_25
    | ~ spl2_35
    | ~ spl2_69
    | ~ spl2_82 ),
    inference(forward_demodulation,[],[f7259,f4338])).

fof(f4338,plain,
    ( ! [X14,X12,X13] : k2_xboole_0(X12,k4_xboole_0(X14,X13)) = k2_xboole_0(X12,k4_xboole_0(k2_xboole_0(X12,X14),X13))
    | ~ spl2_35
    | ~ spl2_69 ),
    inference(superposition,[],[f3888,f774])).

fof(f774,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl2_35
  <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f3888,plain,
    ( ! [X12,X10,X11] : k2_xboole_0(X10,X12) = k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12))
    | ~ spl2_69 ),
    inference(avatar_component_clause,[],[f3887])).

fof(f3887,plain,
    ( spl2_69
  <=> ! [X11,X10,X12] : k2_xboole_0(X10,X12) = k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).

fof(f7259,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X28,X26)) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(X26,X27),X28))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_25
    | ~ spl2_82 ),
    inference(forward_demodulation,[],[f7258,f40])).

fof(f40,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl2_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f7258,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X28,X26)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X26,X27),X28),X26)
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_13
    | ~ spl2_25
    | ~ spl2_82 ),
    inference(forward_demodulation,[],[f7062,f7228])).

fof(f7228,plain,
    ( ! [X8,X7] : k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) = X7
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_25
    | ~ spl2_82 ),
    inference(backward_demodulation,[],[f74,f7225])).

fof(f7225,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25
    | ~ spl2_82 ),
    inference(forward_demodulation,[],[f7224,f434])).

fof(f434,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f433])).

fof(f433,plain,
    ( spl2_25
  <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f7224,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X2))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_82 ),
    inference(forward_demodulation,[],[f7223,f40])).

fof(f7223,plain,
    ( ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(X2,k4_xboole_0(X3,X2))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_82 ),
    inference(forward_demodulation,[],[f7055,f32])).

fof(f32,plain,
    ( ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f31])).

fof(f31,plain,
    ( spl2_1
  <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f7055,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))
    | ~ spl2_2
    | ~ spl2_82 ),
    inference(superposition,[],[f4800,f36])).

fof(f36,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f4800,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))
    | ~ spl2_82 ),
    inference(avatar_component_clause,[],[f4799])).

fof(f4799,plain,
    ( spl2_82
  <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).

fof(f74,plain,
    ( ! [X8,X7] : k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7))
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(superposition,[],[f48,f44])).

fof(f44,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f43])).

fof(f43,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f48,plain,
    ( ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f7062,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X28,X26)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X26,X27),X28),k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X27,X26)))
    | ~ spl2_13
    | ~ spl2_82 ),
    inference(superposition,[],[f4800,f128])).

fof(f128,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl2_13
  <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f7435,plain,
    ( ! [X28,X26,X27] : k4_xboole_0(k2_xboole_0(X26,X28),k4_xboole_0(X27,X26)) = k2_xboole_0(X26,k4_xboole_0(X28,k4_xboole_0(X27,X26)))
    | ~ spl2_35
    | ~ spl2_91 ),
    inference(superposition,[],[f774,f7382])).

fof(f7382,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2
    | ~ spl2_91 ),
    inference(avatar_component_clause,[],[f7381])).

fof(f7381,plain,
    ( spl2_91
  <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).

fof(f9512,plain,
    ( ! [X37,X35,X36] : k4_xboole_0(k2_xboole_0(X35,X37),k4_xboole_0(X35,k4_xboole_0(X35,X36))) = k2_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X37,k4_xboole_0(X35,k4_xboole_0(X35,X36))))
    | ~ spl2_35
    | ~ spl2_103 ),
    inference(superposition,[],[f774,f9439])).

fof(f9439,plain,
    ( ! [X6,X7] : k4_xboole_0(X6,X7) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7)))
    | ~ spl2_103 ),
    inference(avatar_component_clause,[],[f9438])).

fof(f9438,plain,
    ( spl2_103
  <=> ! [X7,X6] : k4_xboole_0(X6,X7) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).

fof(f2513,plain,
    ( k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))
    | spl2_58 ),
    inference(avatar_component_clause,[],[f2511])).

fof(f2511,plain,
    ( spl2_58
  <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f9440,plain,
    ( spl2_103
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_25
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f7227,f4799,f433,f127,f123,f39,f35,f31,f9438])).

fof(f123,plain,
    ( spl2_12
  <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f7227,plain,
    ( ! [X6,X7] : k4_xboole_0(X6,X7) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7)))
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_25
    | ~ spl2_82 ),
    inference(backward_demodulation,[],[f371,f7225])).

fof(f371,plain,
    ( ! [X6,X7] : k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7)))
    | ~ spl2_12
    | ~ spl2_13 ),
    inference(superposition,[],[f128,f124])).

fof(f124,plain,
    ( ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f7383,plain,
    ( spl2_91
    | ~ spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_25
    | ~ spl2_82 ),
    inference(avatar_split_clause,[],[f7225,f4799,f433,f39,f35,f31,f7381])).

fof(f4801,plain,(
    spl2_82 ),
    inference(avatar_split_clause,[],[f28,f4799])).

fof(f28,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2))) ),
    inference(definition_unfolding,[],[f23,f20])).

fof(f20,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f23,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).

fof(f3889,plain,
    ( spl2_69
    | ~ spl2_4
    | ~ spl2_62 ),
    inference(avatar_split_clause,[],[f3302,f3199,f43,f3887])).

fof(f3199,plain,
    ( spl2_62
  <=> ! [X27,X29,X28] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k4_xboole_0(X29,X27) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).

fof(f3302,plain,
    ( ! [X12,X10,X11] : k2_xboole_0(X10,X12) = k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12))
    | ~ spl2_4
    | ~ spl2_62 ),
    inference(forward_demodulation,[],[f3258,f44])).

fof(f3258,plain,
    ( ! [X12,X10,X11] : k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)) = k2_xboole_0(X10,k4_xboole_0(X12,X10))
    | ~ spl2_4
    | ~ spl2_62 ),
    inference(superposition,[],[f44,f3200])).

fof(f3200,plain,
    ( ! [X28,X29,X27] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k4_xboole_0(X29,X27)
    | ~ spl2_62 ),
    inference(avatar_component_clause,[],[f3199])).

fof(f3201,plain,
    ( spl2_62
    | ~ spl2_10
    | ~ spl2_24
    | ~ spl2_35 ),
    inference(avatar_split_clause,[],[f1718,f773,f429,f105,f3199])).

fof(f105,plain,
    ( spl2_10
  <=> ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f429,plain,
    ( spl2_24
  <=> ! [X15,X14] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),X14) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f1718,plain,
    ( ! [X28,X29,X27] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k4_xboole_0(X29,X27)
    | ~ spl2_10
    | ~ spl2_24
    | ~ spl2_35 ),
    inference(forward_demodulation,[],[f1654,f106])).

fof(f106,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f1654,plain,
    ( ! [X28,X29,X27] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X29,X27))
    | ~ spl2_24
    | ~ spl2_35 ),
    inference(superposition,[],[f774,f430])).

fof(f430,plain,
    ( ! [X14,X15] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),X14)
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f429])).

fof(f2514,plain,(
    ~ spl2_58 ),
    inference(avatar_split_clause,[],[f25,f2511])).

fof(f25,plain,(
    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f15,f20])).

fof(f15,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
   => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).

fof(f775,plain,(
    spl2_35 ),
    inference(avatar_split_clause,[],[f24,f773])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f435,plain,
    ( spl2_25
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f407,f395,f39,f433])).

fof(f395,plain,
    ( spl2_23
  <=> ! [X20,X21] : k2_xboole_0(k4_xboole_0(X20,X21),X20) = X20 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f407,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(superposition,[],[f396,f40])).

fof(f396,plain,
    ( ! [X21,X20] : k2_xboole_0(k4_xboole_0(X20,X21),X20) = X20
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f395])).

fof(f431,plain,
    ( spl2_24
    | ~ spl2_12
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f375,f206,f123,f429])).

fof(f206,plain,
    ( spl2_18
  <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f375,plain,
    ( ! [X14,X15] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),X14)
    | ~ spl2_12
    | ~ spl2_18 ),
    inference(superposition,[],[f207,f124])).

fof(f207,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f397,plain,
    ( spl2_23
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f378,f257,f123,f395])).

fof(f257,plain,
    ( spl2_20
  <=> ! [X1,X2] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f378,plain,
    ( ! [X21,X20] : k2_xboole_0(k4_xboole_0(X20,X21),X20) = X20
    | ~ spl2_12
    | ~ spl2_20 ),
    inference(superposition,[],[f258,f124])).

fof(f258,plain,
    ( ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f257])).

fof(f259,plain,
    ( spl2_20
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f177,f167,f39,f257])).

fof(f167,plain,
    ( spl2_16
  <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f177,plain,
    ( ! [X2,X1] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_3
    | ~ spl2_16 ),
    inference(superposition,[],[f168,f40])).

fof(f168,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f167])).

fof(f208,plain,
    ( spl2_18
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f193,f189,f39,f206])).

fof(f189,plain,
    ( spl2_17
  <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f193,plain,
    ( ! [X2,X1] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))
    | ~ spl2_3
    | ~ spl2_17 ),
    inference(superposition,[],[f190,f40])).

fof(f190,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,
    ( spl2_17
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f187,f167,f47,f35,f189])).

fof(f187,plain,
    ( ! [X6,X5] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))
    | ~ spl2_2
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(forward_demodulation,[],[f185,f36])).

fof(f185,plain,
    ( ! [X6,X5] : k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))
    | ~ spl2_5
    | ~ spl2_16 ),
    inference(superposition,[],[f48,f168])).

fof(f169,plain,
    ( spl2_16
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f145,f127,f43,f167])).

fof(f145,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(forward_demodulation,[],[f140,f44])).

fof(f140,plain,
    ( ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3))
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(superposition,[],[f44,f128])).

fof(f129,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f71,f47,f39,f127])).

fof(f71,plain,
    ( ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3)
    | ~ spl2_3
    | ~ spl2_5 ),
    inference(superposition,[],[f48,f40])).

fof(f125,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f27,f123])).

fof(f27,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f22,f20])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f107,plain,
    ( spl2_10
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f87,f60,f52,f47,f31,f105])).

fof(f52,plain,
    ( spl2_6
  <=> ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f60,plain,
    ( spl2_7
  <=> ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f87,plain,
    ( ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_7 ),
    inference(backward_demodulation,[],[f61,f84])).

fof(f84,plain,
    ( ! [X1] : k2_xboole_0(X1,X1) = X1
    | ~ spl2_1
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(backward_demodulation,[],[f53,f82])).

fof(f82,plain,
    ( ! [X2] : k2_xboole_0(X2,k1_xboole_0) = X2
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(forward_demodulation,[],[f76,f32])).

fof(f76,plain,
    ( ! [X2] : k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)
    | ~ spl2_1
    | ~ spl2_5 ),
    inference(superposition,[],[f48,f32])).

fof(f53,plain,
    ( ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f52])).

fof(f61,plain,
    ( ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f60])).

fof(f62,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f55,f52,f39,f60])).

fof(f55,plain,
    ( ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1)
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f53,f40])).

fof(f54,plain,
    ( spl2_6
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f50,f43,f35,f52])).

fof(f50,plain,
    ( ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_4 ),
    inference(superposition,[],[f44,f36])).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f21,f47])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f45,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f41,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f35])).

fof(f29,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f26,f17])).

fof(f17,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f26,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f16,f20])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

fof(f33,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f17,f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:39:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.43  % (5843)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.48  % (5835)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (5834)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.48  % (5831)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (5832)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.49  % (5841)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.49  % (5838)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (5828)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (5839)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.50  % (5842)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.22/0.50  % (5839)Refutation not found, incomplete strategy% (5839)------------------------------
% 0.22/0.50  % (5839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (5839)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (5839)Memory used [KB]: 10490
% 0.22/0.50  % (5839)Time elapsed: 0.076 s
% 0.22/0.50  % (5839)------------------------------
% 0.22/0.50  % (5839)------------------------------
% 0.22/0.50  % (5833)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.50  % (5840)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (5837)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.22/0.50  % (5845)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.22/0.51  % (5830)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.22/0.51  % (5829)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.51  % (5844)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 1.20/0.52  % (5836)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 2.67/0.75  % (5835)Refutation found. Thanks to Tanya!
% 2.67/0.75  % SZS status Theorem for theBenchmark
% 2.67/0.76  % SZS output start Proof for theBenchmark
% 2.67/0.76  fof(f9636,plain,(
% 2.67/0.76    $false),
% 2.67/0.76    inference(avatar_sat_refutation,[],[f33,f37,f41,f45,f49,f54,f62,f107,f125,f129,f169,f191,f208,f259,f397,f431,f435,f775,f2514,f3201,f3889,f4801,f7383,f9440,f9619])).
% 2.67/0.76  fof(f9619,plain,(
% 2.67/0.76    ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13 | ~spl2_25 | ~spl2_35 | spl2_58 | ~spl2_69 | ~spl2_82 | ~spl2_91 | ~spl2_103),
% 2.67/0.76    inference(avatar_contradiction_clause,[],[f9618])).
% 2.67/0.76  fof(f9618,plain,(
% 2.67/0.76    $false | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13 | ~spl2_25 | ~spl2_35 | spl2_58 | ~spl2_69 | ~spl2_82 | ~spl2_91 | ~spl2_103)),
% 2.67/0.76    inference(subsumption_resolution,[],[f2513,f9617])).
% 2.67/0.76  fof(f9617,plain,(
% 2.67/0.76    ( ! [X37,X35,X36] : (k4_xboole_0(k2_xboole_0(X35,X37),k4_xboole_0(X35,k4_xboole_0(X35,X36))) = k2_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X37,X35))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13 | ~spl2_25 | ~spl2_35 | ~spl2_69 | ~spl2_82 | ~spl2_91 | ~spl2_103)),
% 2.67/0.76    inference(forward_demodulation,[],[f9512,f7485])).
% 2.67/0.76  fof(f7485,plain,(
% 2.67/0.76    ( ! [X28,X26,X27] : (k2_xboole_0(X26,k4_xboole_0(X28,k4_xboole_0(X27,X26))) = k2_xboole_0(X26,k4_xboole_0(X28,X27))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13 | ~spl2_25 | ~spl2_35 | ~spl2_69 | ~spl2_82 | ~spl2_91)),
% 2.67/0.76    inference(forward_demodulation,[],[f7435,f7260])).
% 2.67/0.76  fof(f7260,plain,(
% 2.67/0.76    ( ! [X28,X26,X27] : (k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X28,X26)) = k2_xboole_0(X26,k4_xboole_0(X27,X28))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13 | ~spl2_25 | ~spl2_35 | ~spl2_69 | ~spl2_82)),
% 2.67/0.76    inference(forward_demodulation,[],[f7259,f4338])).
% 2.67/0.76  fof(f4338,plain,(
% 2.67/0.76    ( ! [X14,X12,X13] : (k2_xboole_0(X12,k4_xboole_0(X14,X13)) = k2_xboole_0(X12,k4_xboole_0(k2_xboole_0(X12,X14),X13))) ) | (~spl2_35 | ~spl2_69)),
% 2.67/0.76    inference(superposition,[],[f3888,f774])).
% 2.67/0.76  fof(f774,plain,(
% 2.67/0.76    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) ) | ~spl2_35),
% 2.67/0.76    inference(avatar_component_clause,[],[f773])).
% 2.67/0.76  fof(f773,plain,(
% 2.67/0.76    spl2_35 <=> ! [X1,X0,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).
% 2.67/0.76  fof(f3888,plain,(
% 2.67/0.76    ( ! [X12,X10,X11] : (k2_xboole_0(X10,X12) = k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12))) ) | ~spl2_69),
% 2.67/0.76    inference(avatar_component_clause,[],[f3887])).
% 2.67/0.76  fof(f3887,plain,(
% 2.67/0.76    spl2_69 <=> ! [X11,X10,X12] : k2_xboole_0(X10,X12) = k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_69])])).
% 2.67/0.76  fof(f7259,plain,(
% 2.67/0.76    ( ! [X28,X26,X27] : (k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X28,X26)) = k2_xboole_0(X26,k4_xboole_0(k2_xboole_0(X26,X27),X28))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13 | ~spl2_25 | ~spl2_82)),
% 2.67/0.76    inference(forward_demodulation,[],[f7258,f40])).
% 2.67/0.76  fof(f40,plain,(
% 2.67/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_3),
% 2.67/0.76    inference(avatar_component_clause,[],[f39])).
% 2.67/0.76  fof(f39,plain,(
% 2.67/0.76    spl2_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 2.67/0.76  fof(f7258,plain,(
% 2.67/0.76    ( ! [X28,X26,X27] : (k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X28,X26)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X26,X27),X28),X26)) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_13 | ~spl2_25 | ~spl2_82)),
% 2.67/0.76    inference(forward_demodulation,[],[f7062,f7228])).
% 2.67/0.76  fof(f7228,plain,(
% 2.67/0.76    ( ! [X8,X7] : (k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7)) = X7) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_25 | ~spl2_82)),
% 2.67/0.76    inference(backward_demodulation,[],[f74,f7225])).
% 2.67/0.76  fof(f7225,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_25 | ~spl2_82)),
% 2.67/0.76    inference(forward_demodulation,[],[f7224,f434])).
% 2.67/0.76  fof(f434,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) ) | ~spl2_25),
% 2.67/0.76    inference(avatar_component_clause,[],[f433])).
% 2.67/0.76  fof(f433,plain,(
% 2.67/0.76    spl2_25 <=> ! [X3,X2] : k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 2.67/0.76  fof(f7224,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k4_xboole_0(X3,X2))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_82)),
% 2.67/0.76    inference(forward_demodulation,[],[f7223,f40])).
% 2.67/0.76  fof(f7223,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = k4_xboole_0(X2,k4_xboole_0(X3,X2))) ) | (~spl2_1 | ~spl2_2 | ~spl2_82)),
% 2.67/0.76    inference(forward_demodulation,[],[f7055,f32])).
% 2.67/0.76  fof(f32,plain,(
% 2.67/0.76    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 2.67/0.76    inference(avatar_component_clause,[],[f31])).
% 2.67/0.76  fof(f31,plain,(
% 2.67/0.76    spl2_1 <=> ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 2.67/0.76  fof(f7055,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k1_xboole_0))) ) | (~spl2_2 | ~spl2_82)),
% 2.67/0.76    inference(superposition,[],[f4800,f36])).
% 2.67/0.76  fof(f36,plain,(
% 2.67/0.76    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_2),
% 2.67/0.76    inference(avatar_component_clause,[],[f35])).
% 2.67/0.76  fof(f35,plain,(
% 2.67/0.76    spl2_2 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 2.67/0.76  fof(f4800,plain,(
% 2.67/0.76    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) ) | ~spl2_82),
% 2.67/0.76    inference(avatar_component_clause,[],[f4799])).
% 2.67/0.76  fof(f4799,plain,(
% 2.67/0.76    spl2_82 <=> ! [X1,X0,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_82])])).
% 2.67/0.76  fof(f74,plain,(
% 2.67/0.76    ( ! [X8,X7] : (k4_xboole_0(X7,k4_xboole_0(X8,X7)) = k4_xboole_0(k2_xboole_0(X7,X8),k4_xboole_0(X8,X7))) ) | (~spl2_4 | ~spl2_5)),
% 2.67/0.76    inference(superposition,[],[f48,f44])).
% 2.67/0.76  fof(f44,plain,(
% 2.67/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_4),
% 2.67/0.76    inference(avatar_component_clause,[],[f43])).
% 2.67/0.76  fof(f43,plain,(
% 2.67/0.76    spl2_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 2.67/0.76  fof(f48,plain,(
% 2.67/0.76    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) ) | ~spl2_5),
% 2.67/0.76    inference(avatar_component_clause,[],[f47])).
% 2.67/0.76  fof(f47,plain,(
% 2.67/0.76    spl2_5 <=> ! [X1,X0] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 2.67/0.76  fof(f7062,plain,(
% 2.67/0.76    ( ! [X28,X26,X27] : (k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X28,X26)) = k2_xboole_0(k4_xboole_0(k2_xboole_0(X26,X27),X28),k4_xboole_0(k2_xboole_0(X26,X27),k4_xboole_0(X27,X26)))) ) | (~spl2_13 | ~spl2_82)),
% 2.67/0.76    inference(superposition,[],[f4800,f128])).
% 2.67/0.76  fof(f128,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3)) ) | ~spl2_13),
% 2.67/0.76    inference(avatar_component_clause,[],[f127])).
% 2.67/0.76  fof(f127,plain,(
% 2.67/0.76    spl2_13 <=> ! [X3,X2] : k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3)),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 2.67/0.76  fof(f7435,plain,(
% 2.67/0.76    ( ! [X28,X26,X27] : (k4_xboole_0(k2_xboole_0(X26,X28),k4_xboole_0(X27,X26)) = k2_xboole_0(X26,k4_xboole_0(X28,k4_xboole_0(X27,X26)))) ) | (~spl2_35 | ~spl2_91)),
% 2.67/0.76    inference(superposition,[],[f774,f7382])).
% 2.67/0.76  fof(f7382,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2) ) | ~spl2_91),
% 2.67/0.76    inference(avatar_component_clause,[],[f7381])).
% 2.67/0.76  fof(f7381,plain,(
% 2.67/0.76    spl2_91 <=> ! [X3,X2] : k4_xboole_0(X2,k4_xboole_0(X3,X2)) = X2),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_91])])).
% 2.67/0.76  fof(f9512,plain,(
% 2.67/0.76    ( ! [X37,X35,X36] : (k4_xboole_0(k2_xboole_0(X35,X37),k4_xboole_0(X35,k4_xboole_0(X35,X36))) = k2_xboole_0(k4_xboole_0(X35,X36),k4_xboole_0(X37,k4_xboole_0(X35,k4_xboole_0(X35,X36))))) ) | (~spl2_35 | ~spl2_103)),
% 2.67/0.76    inference(superposition,[],[f774,f9439])).
% 2.67/0.76  fof(f9439,plain,(
% 2.67/0.76    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7)))) ) | ~spl2_103),
% 2.67/0.76    inference(avatar_component_clause,[],[f9438])).
% 2.67/0.76  fof(f9438,plain,(
% 2.67/0.76    spl2_103 <=> ! [X7,X6] : k4_xboole_0(X6,X7) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7)))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).
% 2.67/0.76  fof(f2513,plain,(
% 2.67/0.76    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))) | spl2_58),
% 2.67/0.76    inference(avatar_component_clause,[],[f2511])).
% 2.67/0.76  fof(f2511,plain,(
% 2.67/0.76    spl2_58 <=> k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) = k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 2.67/0.76  fof(f9440,plain,(
% 2.67/0.76    spl2_103 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_12 | ~spl2_13 | ~spl2_25 | ~spl2_82),
% 2.67/0.76    inference(avatar_split_clause,[],[f7227,f4799,f433,f127,f123,f39,f35,f31,f9438])).
% 2.67/0.76  fof(f123,plain,(
% 2.67/0.76    spl2_12 <=> ! [X1,X0] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 2.67/0.76  fof(f7227,plain,(
% 2.67/0.76    ( ! [X6,X7] : (k4_xboole_0(X6,X7) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7)))) ) | (~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_12 | ~spl2_13 | ~spl2_25 | ~spl2_82)),
% 2.67/0.76    inference(backward_demodulation,[],[f371,f7225])).
% 2.67/0.76  fof(f371,plain,(
% 2.67/0.76    ( ! [X6,X7] : (k4_xboole_0(k4_xboole_0(X6,X7),k4_xboole_0(X6,k4_xboole_0(X6,X7))) = k4_xboole_0(X6,k4_xboole_0(X6,k4_xboole_0(X6,X7)))) ) | (~spl2_12 | ~spl2_13)),
% 2.67/0.76    inference(superposition,[],[f128,f124])).
% 2.67/0.76  fof(f124,plain,(
% 2.67/0.76    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) ) | ~spl2_12),
% 2.67/0.76    inference(avatar_component_clause,[],[f123])).
% 2.67/0.76  fof(f7383,plain,(
% 2.67/0.76    spl2_91 | ~spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_25 | ~spl2_82),
% 2.67/0.76    inference(avatar_split_clause,[],[f7225,f4799,f433,f39,f35,f31,f7381])).
% 2.67/0.76  fof(f4801,plain,(
% 2.67/0.76    spl2_82),
% 2.67/0.76    inference(avatar_split_clause,[],[f28,f4799])).
% 2.67/0.76  fof(f28,plain,(
% 2.67/0.76    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X2)))) )),
% 2.67/0.76    inference(definition_unfolding,[],[f23,f20])).
% 2.67/0.76  fof(f20,plain,(
% 2.67/0.76    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 2.67/0.76    inference(cnf_transformation,[],[f7])).
% 2.67/0.76  fof(f7,axiom,(
% 2.67/0.76    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 2.67/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.67/0.76  fof(f23,plain,(
% 2.67/0.76    ( ! [X2,X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))) )),
% 2.67/0.76    inference(cnf_transformation,[],[f9])).
% 2.67/0.76  fof(f9,axiom,(
% 2.67/0.76    ! [X0,X1,X2] : k4_xboole_0(X0,k4_xboole_0(X1,X2)) = k2_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X0,X2))),
% 2.67/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_xboole_1)).
% 2.67/0.76  fof(f3889,plain,(
% 2.67/0.76    spl2_69 | ~spl2_4 | ~spl2_62),
% 2.67/0.76    inference(avatar_split_clause,[],[f3302,f3199,f43,f3887])).
% 2.67/0.76  fof(f3199,plain,(
% 2.67/0.76    spl2_62 <=> ! [X27,X29,X28] : k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k4_xboole_0(X29,X27)),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_62])])).
% 2.67/0.76  fof(f3302,plain,(
% 2.67/0.76    ( ! [X12,X10,X11] : (k2_xboole_0(X10,X12) = k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12))) ) | (~spl2_4 | ~spl2_62)),
% 2.67/0.76    inference(forward_demodulation,[],[f3258,f44])).
% 2.67/0.76  fof(f3258,plain,(
% 2.67/0.76    ( ! [X12,X10,X11] : (k2_xboole_0(X10,k2_xboole_0(k4_xboole_0(X10,X11),X12)) = k2_xboole_0(X10,k4_xboole_0(X12,X10))) ) | (~spl2_4 | ~spl2_62)),
% 2.67/0.76    inference(superposition,[],[f44,f3200])).
% 2.67/0.76  fof(f3200,plain,(
% 2.67/0.76    ( ! [X28,X29,X27] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k4_xboole_0(X29,X27)) ) | ~spl2_62),
% 2.67/0.76    inference(avatar_component_clause,[],[f3199])).
% 2.67/0.76  fof(f3201,plain,(
% 2.67/0.76    spl2_62 | ~spl2_10 | ~spl2_24 | ~spl2_35),
% 2.67/0.76    inference(avatar_split_clause,[],[f1718,f773,f429,f105,f3199])).
% 2.67/0.76  fof(f105,plain,(
% 2.67/0.76    spl2_10 <=> ! [X1] : k2_xboole_0(k1_xboole_0,X1) = X1),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 2.67/0.76  fof(f429,plain,(
% 2.67/0.76    spl2_24 <=> ! [X15,X14] : k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),X14)),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 2.67/0.76  fof(f1718,plain,(
% 2.67/0.76    ( ! [X28,X29,X27] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k4_xboole_0(X29,X27)) ) | (~spl2_10 | ~spl2_24 | ~spl2_35)),
% 2.67/0.76    inference(forward_demodulation,[],[f1654,f106])).
% 2.67/0.76  fof(f106,plain,(
% 2.67/0.76    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | ~spl2_10),
% 2.67/0.76    inference(avatar_component_clause,[],[f105])).
% 2.67/0.76  fof(f1654,plain,(
% 2.67/0.76    ( ! [X28,X29,X27] : (k4_xboole_0(k2_xboole_0(k4_xboole_0(X27,X28),X29),X27) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X29,X27))) ) | (~spl2_24 | ~spl2_35)),
% 2.67/0.76    inference(superposition,[],[f774,f430])).
% 2.67/0.76  fof(f430,plain,(
% 2.67/0.76    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),X14)) ) | ~spl2_24),
% 2.67/0.76    inference(avatar_component_clause,[],[f429])).
% 2.67/0.76  fof(f2514,plain,(
% 2.67/0.76    ~spl2_58),
% 2.67/0.76    inference(avatar_split_clause,[],[f25,f2511])).
% 2.67/0.76  fof(f25,plain,(
% 2.67/0.76    k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0)) != k4_xboole_0(k2_xboole_0(sK0,sK1),k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)))),
% 2.67/0.76    inference(definition_unfolding,[],[f15,f20])).
% 2.67/0.76  fof(f15,plain,(
% 2.67/0.76    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 2.67/0.76    inference(cnf_transformation,[],[f14])).
% 2.67/0.76  fof(f14,plain,(
% 2.67/0.76    k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 2.67/0.76    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 2.67/0.76  fof(f13,plain,(
% 2.67/0.76    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) => k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) != k2_xboole_0(k4_xboole_0(sK0,sK1),k4_xboole_0(sK1,sK0))),
% 2.67/0.76    introduced(choice_axiom,[])).
% 2.67/0.76  fof(f12,plain,(
% 2.67/0.76    ? [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) != k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.67/0.76    inference(ennf_transformation,[],[f11])).
% 2.67/0.76  fof(f11,negated_conjecture,(
% 2.67/0.76    ~! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.67/0.76    inference(negated_conjecture,[],[f10])).
% 2.67/0.76  fof(f10,conjecture,(
% 2.67/0.76    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 2.67/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_xboole_1)).
% 2.67/0.76  fof(f775,plain,(
% 2.67/0.76    spl2_35),
% 2.67/0.76    inference(avatar_split_clause,[],[f24,f773])).
% 2.67/0.76  fof(f24,plain,(
% 2.67/0.76    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 2.67/0.76    inference(cnf_transformation,[],[f6])).
% 2.67/0.76  fof(f6,axiom,(
% 2.67/0.76    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 2.67/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).
% 2.67/0.76  fof(f435,plain,(
% 2.67/0.76    spl2_25 | ~spl2_3 | ~spl2_23),
% 2.67/0.76    inference(avatar_split_clause,[],[f407,f395,f39,f433])).
% 2.67/0.76  fof(f395,plain,(
% 2.67/0.76    spl2_23 <=> ! [X20,X21] : k2_xboole_0(k4_xboole_0(X20,X21),X20) = X20),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 2.67/0.76  fof(f407,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X2,X3)) = X2) ) | (~spl2_3 | ~spl2_23)),
% 2.67/0.76    inference(superposition,[],[f396,f40])).
% 2.67/0.76  fof(f396,plain,(
% 2.67/0.76    ( ! [X21,X20] : (k2_xboole_0(k4_xboole_0(X20,X21),X20) = X20) ) | ~spl2_23),
% 2.67/0.76    inference(avatar_component_clause,[],[f395])).
% 2.67/0.76  fof(f431,plain,(
% 2.67/0.76    spl2_24 | ~spl2_12 | ~spl2_18),
% 2.67/0.76    inference(avatar_split_clause,[],[f375,f206,f123,f429])).
% 2.67/0.76  fof(f206,plain,(
% 2.67/0.76    spl2_18 <=> ! [X1,X2] : k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 2.67/0.76  fof(f375,plain,(
% 2.67/0.76    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(k4_xboole_0(X14,X15),X14)) ) | (~spl2_12 | ~spl2_18)),
% 2.67/0.76    inference(superposition,[],[f207,f124])).
% 2.67/0.76  fof(f207,plain,(
% 2.67/0.76    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | ~spl2_18),
% 2.67/0.76    inference(avatar_component_clause,[],[f206])).
% 2.67/0.76  fof(f397,plain,(
% 2.67/0.76    spl2_23 | ~spl2_12 | ~spl2_20),
% 2.67/0.76    inference(avatar_split_clause,[],[f378,f257,f123,f395])).
% 2.67/0.76  fof(f257,plain,(
% 2.67/0.76    spl2_20 <=> ! [X1,X2] : k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 2.67/0.76  fof(f378,plain,(
% 2.67/0.76    ( ! [X21,X20] : (k2_xboole_0(k4_xboole_0(X20,X21),X20) = X20) ) | (~spl2_12 | ~spl2_20)),
% 2.67/0.76    inference(superposition,[],[f258,f124])).
% 2.67/0.76  fof(f258,plain,(
% 2.67/0.76    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) ) | ~spl2_20),
% 2.67/0.76    inference(avatar_component_clause,[],[f257])).
% 2.67/0.76  fof(f259,plain,(
% 2.67/0.76    spl2_20 | ~spl2_3 | ~spl2_16),
% 2.67/0.76    inference(avatar_split_clause,[],[f177,f167,f39,f257])).
% 2.67/0.76  fof(f167,plain,(
% 2.67/0.76    spl2_16 <=> ! [X3,X2] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 2.67/0.76  fof(f177,plain,(
% 2.67/0.76    ( ! [X2,X1] : (k2_xboole_0(X2,X1) = k2_xboole_0(X1,k2_xboole_0(X2,X1))) ) | (~spl2_3 | ~spl2_16)),
% 2.67/0.76    inference(superposition,[],[f168,f40])).
% 2.67/0.76  fof(f168,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) ) | ~spl2_16),
% 2.67/0.76    inference(avatar_component_clause,[],[f167])).
% 2.67/0.76  fof(f208,plain,(
% 2.67/0.76    spl2_18 | ~spl2_3 | ~spl2_17),
% 2.67/0.76    inference(avatar_split_clause,[],[f193,f189,f39,f206])).
% 2.67/0.76  fof(f189,plain,(
% 2.67/0.76    spl2_17 <=> ! [X5,X6] : k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 2.67/0.76  fof(f193,plain,(
% 2.67/0.76    ( ! [X2,X1] : (k1_xboole_0 = k4_xboole_0(X1,k2_xboole_0(X2,X1))) ) | (~spl2_3 | ~spl2_17)),
% 2.67/0.76    inference(superposition,[],[f190,f40])).
% 2.67/0.76  fof(f190,plain,(
% 2.67/0.76    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) ) | ~spl2_17),
% 2.67/0.76    inference(avatar_component_clause,[],[f189])).
% 2.67/0.76  fof(f191,plain,(
% 2.67/0.76    spl2_17 | ~spl2_2 | ~spl2_5 | ~spl2_16),
% 2.67/0.76    inference(avatar_split_clause,[],[f187,f167,f47,f35,f189])).
% 2.67/0.76  fof(f187,plain,(
% 2.67/0.76    ( ! [X6,X5] : (k1_xboole_0 = k4_xboole_0(X5,k2_xboole_0(X5,X6))) ) | (~spl2_2 | ~spl2_5 | ~spl2_16)),
% 2.67/0.76    inference(forward_demodulation,[],[f185,f36])).
% 2.67/0.76  fof(f185,plain,(
% 2.67/0.76    ( ! [X6,X5] : (k4_xboole_0(X5,k2_xboole_0(X5,X6)) = k4_xboole_0(k2_xboole_0(X5,X6),k2_xboole_0(X5,X6))) ) | (~spl2_5 | ~spl2_16)),
% 2.67/0.76    inference(superposition,[],[f48,f168])).
% 2.67/0.76  fof(f169,plain,(
% 2.67/0.76    spl2_16 | ~spl2_4 | ~spl2_13),
% 2.67/0.76    inference(avatar_split_clause,[],[f145,f127,f43,f167])).
% 2.67/0.76  fof(f145,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl2_4 | ~spl2_13)),
% 2.67/0.76    inference(forward_demodulation,[],[f140,f44])).
% 2.67/0.76  fof(f140,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) ) | (~spl2_4 | ~spl2_13)),
% 2.67/0.76    inference(superposition,[],[f44,f128])).
% 2.67/0.76  fof(f129,plain,(
% 2.67/0.76    spl2_13 | ~spl2_3 | ~spl2_5),
% 2.67/0.76    inference(avatar_split_clause,[],[f71,f47,f39,f127])).
% 2.67/0.76  fof(f71,plain,(
% 2.67/0.76    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k2_xboole_0(X3,X2),X3)) ) | (~spl2_3 | ~spl2_5)),
% 2.67/0.76    inference(superposition,[],[f48,f40])).
% 2.67/0.76  fof(f125,plain,(
% 2.67/0.76    spl2_12),
% 2.67/0.76    inference(avatar_split_clause,[],[f27,f123])).
% 2.67/0.76  fof(f27,plain,(
% 2.67/0.76    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 2.67/0.76    inference(definition_unfolding,[],[f22,f20])).
% 2.67/0.76  fof(f22,plain,(
% 2.67/0.76    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 2.67/0.76    inference(cnf_transformation,[],[f8])).
% 2.67/0.76  fof(f8,axiom,(
% 2.67/0.76    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.67/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).
% 2.67/0.76  fof(f107,plain,(
% 2.67/0.76    spl2_10 | ~spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_7),
% 2.67/0.76    inference(avatar_split_clause,[],[f87,f60,f52,f47,f31,f105])).
% 2.67/0.76  fof(f52,plain,(
% 2.67/0.76    spl2_6 <=> ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 2.67/0.76  fof(f60,plain,(
% 2.67/0.76    spl2_7 <=> ! [X1] : k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1)),
% 2.67/0.76    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 2.67/0.76  fof(f87,plain,(
% 2.67/0.76    ( ! [X1] : (k2_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl2_1 | ~spl2_5 | ~spl2_6 | ~spl2_7)),
% 2.67/0.76    inference(backward_demodulation,[],[f61,f84])).
% 2.67/0.76  fof(f84,plain,(
% 2.67/0.76    ( ! [X1] : (k2_xboole_0(X1,X1) = X1) ) | (~spl2_1 | ~spl2_5 | ~spl2_6)),
% 2.67/0.76    inference(backward_demodulation,[],[f53,f82])).
% 2.67/0.76  fof(f82,plain,(
% 2.67/0.76    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = X2) ) | (~spl2_1 | ~spl2_5)),
% 2.67/0.76    inference(forward_demodulation,[],[f76,f32])).
% 2.67/0.76  fof(f76,plain,(
% 2.67/0.76    ( ! [X2] : (k2_xboole_0(X2,k1_xboole_0) = k4_xboole_0(X2,k1_xboole_0)) ) | (~spl2_1 | ~spl2_5)),
% 2.67/0.76    inference(superposition,[],[f48,f32])).
% 2.67/0.76  fof(f53,plain,(
% 2.67/0.76    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) ) | ~spl2_6),
% 2.67/0.76    inference(avatar_component_clause,[],[f52])).
% 2.67/0.76  fof(f61,plain,(
% 2.67/0.76    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1)) ) | ~spl2_7),
% 2.67/0.76    inference(avatar_component_clause,[],[f60])).
% 2.67/0.76  fof(f62,plain,(
% 2.67/0.76    spl2_7 | ~spl2_3 | ~spl2_6),
% 2.67/0.76    inference(avatar_split_clause,[],[f55,f52,f39,f60])).
% 2.67/0.76  fof(f55,plain,(
% 2.67/0.76    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(k1_xboole_0,X1)) ) | (~spl2_3 | ~spl2_6)),
% 2.67/0.76    inference(superposition,[],[f53,f40])).
% 2.67/0.76  fof(f54,plain,(
% 2.67/0.76    spl2_6 | ~spl2_2 | ~spl2_4),
% 2.67/0.76    inference(avatar_split_clause,[],[f50,f43,f35,f52])).
% 2.67/0.76  fof(f50,plain,(
% 2.67/0.76    ( ! [X1] : (k2_xboole_0(X1,X1) = k2_xboole_0(X1,k1_xboole_0)) ) | (~spl2_2 | ~spl2_4)),
% 2.67/0.76    inference(superposition,[],[f44,f36])).
% 2.67/0.76  fof(f49,plain,(
% 2.67/0.76    spl2_5),
% 2.67/0.76    inference(avatar_split_clause,[],[f21,f47])).
% 3.20/0.76  fof(f21,plain,(
% 3.20/0.76    ( ! [X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)) )),
% 3.20/0.76    inference(cnf_transformation,[],[f5])).
% 3.20/0.76  fof(f5,axiom,(
% 3.20/0.76    ! [X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X1) = k4_xboole_0(X0,X1)),
% 3.20/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 3.20/0.76  fof(f45,plain,(
% 3.20/0.76    spl2_4),
% 3.20/0.76    inference(avatar_split_clause,[],[f19,f43])).
% 3.20/0.76  fof(f19,plain,(
% 3.20/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.20/0.76    inference(cnf_transformation,[],[f3])).
% 3.20/0.76  fof(f3,axiom,(
% 3.20/0.76    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 3.20/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 3.20/0.76  fof(f41,plain,(
% 3.20/0.76    spl2_3),
% 3.20/0.76    inference(avatar_split_clause,[],[f18,f39])).
% 3.20/0.76  fof(f18,plain,(
% 3.20/0.76    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 3.20/0.76    inference(cnf_transformation,[],[f1])).
% 3.20/0.76  fof(f1,axiom,(
% 3.20/0.76    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 3.20/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 3.20/0.76  fof(f37,plain,(
% 3.20/0.76    spl2_2),
% 3.20/0.76    inference(avatar_split_clause,[],[f29,f35])).
% 3.20/0.76  fof(f29,plain,(
% 3.20/0.76    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 3.20/0.76    inference(backward_demodulation,[],[f26,f17])).
% 3.20/0.76  fof(f17,plain,(
% 3.20/0.76    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 3.20/0.76    inference(cnf_transformation,[],[f4])).
% 3.20/0.76  fof(f4,axiom,(
% 3.20/0.76    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 3.20/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 3.20/0.76  fof(f26,plain,(
% 3.20/0.76    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 3.20/0.76    inference(definition_unfolding,[],[f16,f20])).
% 3.20/0.76  fof(f16,plain,(
% 3.20/0.76    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 3.20/0.76    inference(cnf_transformation,[],[f2])).
% 3.20/0.76  fof(f2,axiom,(
% 3.20/0.76    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 3.20/0.76    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).
% 3.20/0.76  fof(f33,plain,(
% 3.20/0.76    spl2_1),
% 3.20/0.76    inference(avatar_split_clause,[],[f17,f31])).
% 3.20/0.76  % SZS output end Proof for theBenchmark
% 3.20/0.76  % (5835)------------------------------
% 3.20/0.76  % (5835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.76  % (5835)Termination reason: Refutation
% 3.20/0.76  
% 3.20/0.76  % (5835)Memory used [KB]: 13944
% 3.20/0.76  % (5835)Time elapsed: 0.308 s
% 3.20/0.76  % (5835)------------------------------
% 3.20/0.76  % (5835)------------------------------
% 3.20/0.77  % (5827)Success in time 0.401 s
%------------------------------------------------------------------------------
