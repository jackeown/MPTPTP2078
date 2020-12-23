%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:10 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 201 expanded)
%              Number of leaves         :   32 ( 101 expanded)
%              Depth                    :    8
%              Number of atoms          :  268 ( 440 expanded)
%              Number of equality atoms :   92 ( 178 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f713,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f49,f53,f57,f61,f65,f90,f94,f149,f153,f164,f177,f452,f578,f592,f621,f626,f708,f712])).

fof(f712,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_32
    | ~ spl2_34 ),
    inference(avatar_contradiction_clause,[],[f711])).

fof(f711,plain,
    ( $false
    | spl2_1
    | ~ spl2_3
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_32
    | ~ spl2_34 ),
    inference(subsumption_resolution,[],[f28,f710])).

fof(f710,plain,
    ( ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X4))
    | ~ spl2_3
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_32
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f709,f36])).

fof(f36,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f35])).

fof(f35,plain,
    ( spl2_3
  <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f709,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0)
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_32
    | ~ spl2_34 ),
    inference(forward_demodulation,[],[f707,f638])).

fof(f638,plain,
    ( ! [X6,X7] : k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6)
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f631,f163])).

fof(f163,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f162])).

fof(f162,plain,
    ( spl2_15
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f631,plain,
    ( ! [X6,X7] : k4_xboole_0(X6,X6) = k4_xboole_0(k3_xboole_0(X6,X7),X6)
    | ~ spl2_17
    | ~ spl2_32 ),
    inference(superposition,[],[f176,f625])).

fof(f625,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f624])).

fof(f624,plain,
    ( spl2_32
  <=> ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f176,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl2_17
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f707,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k3_xboole_0(X3,X4),X3))
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f706])).

fof(f706,plain,
    ( spl2_34
  <=> ! [X3,X4] : k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k3_xboole_0(X3,X4),X3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f28,plain,
    ( k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f26])).

fof(f26,plain,
    ( spl2_1
  <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f708,plain,
    ( spl2_34
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f103,f88,f59,f706])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f88,plain,
    ( spl2_10
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f103,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k3_xboole_0(X3,X4),X3))
    | ~ spl2_8
    | ~ spl2_10 ),
    inference(superposition,[],[f89,f60])).

fof(f60,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f89,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f626,plain,
    ( spl2_32
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(avatar_split_clause,[],[f622,f619,f590,f151,f47,f624])).

fof(f47,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f151,plain,
    ( spl2_14
  <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f590,plain,
    ( spl2_30
  <=> ! [X1,X2] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f619,plain,
    ( spl2_31
  <=> ! [X1,X2] : k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f622,plain,
    ( ! [X2,X1] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_30
    | ~ spl2_31 ),
    inference(forward_demodulation,[],[f620,f611])).

fof(f611,plain,
    ( ! [X8,X7] : k5_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = X7
    | ~ spl2_5
    | ~ spl2_14
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f596,f152])).

fof(f152,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f151])).

fof(f596,plain,
    ( ! [X8,X7] : k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k4_xboole_0(X7,X8))) = X7
    | ~ spl2_5
    | ~ spl2_30 ),
    inference(superposition,[],[f591,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f591,plain,
    ( ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f590])).

fof(f620,plain,
    ( ! [X2,X1] : k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f619])).

fof(f621,plain,
    ( spl2_31
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f80,f59,f51,f39,f619])).

fof(f39,plain,
    ( spl2_4
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f51,plain,
    ( spl2_6
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f80,plain,
    ( ! [X2,X1] : k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f78,f40])).

fof(f40,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f39])).

fof(f78,plain,
    ( ! [X2,X1] : k2_xboole_0(k3_xboole_0(X1,X2),X1) = k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))
    | ~ spl2_6
    | ~ spl2_8 ),
    inference(superposition,[],[f52,f60])).

fof(f52,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f51])).

fof(f592,plain,
    ( spl2_30
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_26
    | ~ spl2_29 ),
    inference(avatar_split_clause,[],[f579,f576,f450,f175,f162,f147,f590])).

fof(f147,plain,
    ( spl2_13
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f450,plain,
    ( spl2_26
  <=> ! [X7,X8,X6] : k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f576,plain,
    ( spl2_29
  <=> ! [X1,X2] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f579,plain,
    ( ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_26
    | ~ spl2_29 ),
    inference(forward_demodulation,[],[f577,f481])).

fof(f481,plain,
    ( ! [X4,X3] : k2_xboole_0(X4,k4_xboole_0(X4,X3)) = X4
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_17
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f480,f176])).

fof(f480,plain,
    ( ! [X4,X3] : k2_xboole_0(X4,k4_xboole_0(k2_xboole_0(X3,X4),X3)) = X4
    | ~ spl2_13
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(forward_demodulation,[],[f463,f148])).

fof(f148,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f147])).

fof(f463,plain,
    ( ! [X4,X3] : k2_xboole_0(X4,k4_xboole_0(k2_xboole_0(X3,X4),X3)) = k5_xboole_0(X4,k1_xboole_0)
    | ~ spl2_15
    | ~ spl2_26 ),
    inference(superposition,[],[f451,f163])).

fof(f451,plain,
    ( ! [X6,X8,X7] : k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8)))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f450])).

fof(f577,plain,
    ( ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl2_29 ),
    inference(avatar_component_clause,[],[f576])).

fof(f578,plain,
    ( spl2_29
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f75,f51,f47,f39,f576])).

fof(f75,plain,
    ( ! [X2,X1] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f73,f40])).

fof(f73,plain,
    ( ! [X2,X1] : k2_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f52,f48])).

fof(f452,plain,
    ( spl2_26
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f127,f92,f51,f450])).

fof(f92,plain,
    ( spl2_11
  <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f127,plain,
    ( ! [X6,X8,X7] : k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8)))
    | ~ spl2_6
    | ~ spl2_11 ),
    inference(superposition,[],[f52,f93])).

fof(f93,plain,
    ( ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f92])).

fof(f177,plain,
    ( spl2_17
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f82,f63,f39,f175])).

fof(f63,plain,
    ( spl2_9
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f82,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)
    | ~ spl2_4
    | ~ spl2_9 ),
    inference(superposition,[],[f64,f40])).

fof(f64,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f164,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f100,f63,f55,f31,f162])).

fof(f31,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f100,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl2_2
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(forward_demodulation,[],[f97,f32])).

fof(f32,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f31])).

fof(f97,plain,
    ( ! [X0] : k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(superposition,[],[f64,f56])).

fof(f56,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f153,plain,
    ( spl2_14
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f71,f59,f47,f151])).

fof(f71,plain,
    ( ! [X2,X1] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f67,f60])).

fof(f67,plain,
    ( ! [X2,X1] : k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))
    | ~ spl2_5 ),
    inference(superposition,[],[f48,f48])).

fof(f149,plain,
    ( spl2_13
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f74,f51,f35,f31,f147])).

fof(f74,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f72,f36])).

fof(f72,plain,
    ( ! [X0] : k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(superposition,[],[f52,f32])).

fof(f94,plain,(
    spl2_11 ),
    inference(avatar_split_clause,[],[f24,f92])).

fof(f24,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f90,plain,(
    spl2_10 ),
    inference(avatar_split_clause,[],[f23,f88])).

fof(f23,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

fof(f65,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f22,f63])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f21,f59])).

fof(f21,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f57,plain,
    ( spl2_7
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f42,f39,f35,f55])).

fof(f42,plain,
    ( ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(superposition,[],[f40,f36])).

fof(f53,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f49,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f41,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f18,f39])).

fof(f18,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f37,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f17,f35])).

fof(f17,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f33,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f16,f31])).

fof(f16,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

fof(f29,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f15,f26])).

fof(f15,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).

fof(f13,plain,
    ( ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))
   => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 12:07:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.41  % (1149)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.42  % (1149)Refutation found. Thanks to Tanya!
% 0.21/0.42  % SZS status Theorem for theBenchmark
% 0.21/0.43  % (1162)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f713,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f29,f33,f37,f41,f49,f53,f57,f61,f65,f90,f94,f149,f153,f164,f177,f452,f578,f592,f621,f626,f708,f712])).
% 0.21/0.44  fof(f712,plain,(
% 0.21/0.44    spl2_1 | ~spl2_3 | ~spl2_15 | ~spl2_17 | ~spl2_32 | ~spl2_34),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f711])).
% 0.21/0.44  fof(f711,plain,(
% 0.21/0.44    $false | (spl2_1 | ~spl2_3 | ~spl2_15 | ~spl2_17 | ~spl2_32 | ~spl2_34)),
% 0.21/0.44    inference(subsumption_resolution,[],[f28,f710])).
% 0.21/0.44  fof(f710,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X3,X4))) ) | (~spl2_3 | ~spl2_15 | ~spl2_17 | ~spl2_32 | ~spl2_34)),
% 0.21/0.44    inference(forward_demodulation,[],[f709,f36])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    spl2_3 <=> ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.44  fof(f709,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k4_xboole_0(X3,X4),k1_xboole_0)) ) | (~spl2_15 | ~spl2_17 | ~spl2_32 | ~spl2_34)),
% 0.21/0.44    inference(forward_demodulation,[],[f707,f638])).
% 0.21/0.44  fof(f638,plain,(
% 0.21/0.44    ( ! [X6,X7] : (k1_xboole_0 = k4_xboole_0(k3_xboole_0(X6,X7),X6)) ) | (~spl2_15 | ~spl2_17 | ~spl2_32)),
% 0.21/0.44    inference(forward_demodulation,[],[f631,f163])).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl2_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f162])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    spl2_15 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.21/0.44  fof(f631,plain,(
% 0.21/0.44    ( ! [X6,X7] : (k4_xboole_0(X6,X6) = k4_xboole_0(k3_xboole_0(X6,X7),X6)) ) | (~spl2_17 | ~spl2_32)),
% 0.21/0.44    inference(superposition,[],[f176,f625])).
% 0.21/0.44  fof(f625,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1) ) | ~spl2_32),
% 0.21/0.44    inference(avatar_component_clause,[],[f624])).
% 0.21/0.44  fof(f624,plain,(
% 0.21/0.44    spl2_32 <=> ! [X1,X2] : k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.44  fof(f176,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) ) | ~spl2_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f175])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    spl2_17 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.21/0.44  fof(f707,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k3_xboole_0(X3,X4),X3))) ) | ~spl2_34),
% 0.21/0.44    inference(avatar_component_clause,[],[f706])).
% 0.21/0.44  fof(f706,plain,(
% 0.21/0.44    spl2_34 <=> ! [X3,X4] : k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k3_xboole_0(X3,X4),X3))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1)) | spl2_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    spl2_1 <=> k4_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.44  fof(f708,plain,(
% 0.21/0.44    spl2_34 | ~spl2_8 | ~spl2_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f103,f88,f59,f706])).
% 0.21/0.44  fof(f59,plain,(
% 0.21/0.44    spl2_8 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    spl2_10 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k5_xboole_0(X3,k3_xboole_0(X3,X4)) = k2_xboole_0(k4_xboole_0(X3,X4),k4_xboole_0(k3_xboole_0(X3,X4),X3))) ) | (~spl2_8 | ~spl2_10)),
% 0.21/0.44    inference(superposition,[],[f89,f60])).
% 0.21/0.44  fof(f60,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f59])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) ) | ~spl2_10),
% 0.21/0.44    inference(avatar_component_clause,[],[f88])).
% 0.21/0.44  fof(f626,plain,(
% 0.21/0.44    spl2_32 | ~spl2_5 | ~spl2_14 | ~spl2_30 | ~spl2_31),
% 0.21/0.44    inference(avatar_split_clause,[],[f622,f619,f590,f151,f47,f624])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    spl2_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.44  fof(f151,plain,(
% 0.21/0.44    spl2_14 <=> ! [X1,X2] : k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.21/0.44  fof(f590,plain,(
% 0.21/0.44    spl2_30 <=> ! [X1,X2] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 0.21/0.44  fof(f619,plain,(
% 0.21/0.44    spl2_31 <=> ! [X1,X2] : k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 0.21/0.44  fof(f622,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k2_xboole_0(X1,k3_xboole_0(X1,X2)) = X1) ) | (~spl2_5 | ~spl2_14 | ~spl2_30 | ~spl2_31)),
% 0.21/0.44    inference(forward_demodulation,[],[f620,f611])).
% 0.21/0.44  fof(f611,plain,(
% 0.21/0.44    ( ! [X8,X7] : (k5_xboole_0(k3_xboole_0(X7,X8),k4_xboole_0(X7,X8)) = X7) ) | (~spl2_5 | ~spl2_14 | ~spl2_30)),
% 0.21/0.44    inference(forward_demodulation,[],[f596,f152])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) ) | ~spl2_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f151])).
% 0.21/0.44  fof(f596,plain,(
% 0.21/0.44    ( ! [X8,X7] : (k5_xboole_0(k3_xboole_0(X7,X8),k3_xboole_0(X7,k4_xboole_0(X7,X8))) = X7) ) | (~spl2_5 | ~spl2_30)),
% 0.21/0.44    inference(superposition,[],[f591,f48])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f47])).
% 0.21/0.44  fof(f591,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) ) | ~spl2_30),
% 0.21/0.44    inference(avatar_component_clause,[],[f590])).
% 0.21/0.44  fof(f620,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2))) ) | ~spl2_31),
% 0.21/0.44    inference(avatar_component_clause,[],[f619])).
% 0.21/0.44  fof(f621,plain,(
% 0.21/0.44    spl2_31 | ~spl2_4 | ~spl2_6 | ~spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f80,f59,f51,f39,f619])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    spl2_4 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    spl2_6 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2)) = k2_xboole_0(X1,k3_xboole_0(X1,X2))) ) | (~spl2_4 | ~spl2_6 | ~spl2_8)),
% 0.21/0.44    inference(forward_demodulation,[],[f78,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl2_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f39])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k2_xboole_0(k3_xboole_0(X1,X2),X1) = k5_xboole_0(k3_xboole_0(X1,X2),k4_xboole_0(X1,X2))) ) | (~spl2_6 | ~spl2_8)),
% 0.21/0.44    inference(superposition,[],[f52,f60])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl2_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f51])).
% 0.21/0.44  fof(f592,plain,(
% 0.21/0.44    spl2_30 | ~spl2_13 | ~spl2_15 | ~spl2_17 | ~spl2_26 | ~spl2_29),
% 0.21/0.44    inference(avatar_split_clause,[],[f579,f576,f450,f175,f162,f147,f590])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    spl2_13 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.21/0.44  fof(f450,plain,(
% 0.21/0.44    spl2_26 <=> ! [X7,X8,X6] : k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.21/0.44  fof(f576,plain,(
% 0.21/0.44    spl2_29 <=> ! [X1,X2] : k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).
% 0.21/0.44  fof(f579,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = X1) ) | (~spl2_13 | ~spl2_15 | ~spl2_17 | ~spl2_26 | ~spl2_29)),
% 0.21/0.44    inference(forward_demodulation,[],[f577,f481])).
% 0.21/0.44  fof(f481,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k2_xboole_0(X4,k4_xboole_0(X4,X3)) = X4) ) | (~spl2_13 | ~spl2_15 | ~spl2_17 | ~spl2_26)),
% 0.21/0.44    inference(forward_demodulation,[],[f480,f176])).
% 0.21/0.44  fof(f480,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k2_xboole_0(X4,k4_xboole_0(k2_xboole_0(X3,X4),X3)) = X4) ) | (~spl2_13 | ~spl2_15 | ~spl2_26)),
% 0.21/0.44    inference(forward_demodulation,[],[f463,f148])).
% 0.21/0.44  fof(f148,plain,(
% 0.21/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f147])).
% 0.21/0.44  fof(f463,plain,(
% 0.21/0.44    ( ! [X4,X3] : (k2_xboole_0(X4,k4_xboole_0(k2_xboole_0(X3,X4),X3)) = k5_xboole_0(X4,k1_xboole_0)) ) | (~spl2_15 | ~spl2_26)),
% 0.21/0.44    inference(superposition,[],[f451,f163])).
% 0.21/0.44  fof(f451,plain,(
% 0.21/0.44    ( ! [X6,X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8)))) ) | ~spl2_26),
% 0.21/0.44    inference(avatar_component_clause,[],[f450])).
% 0.21/0.44  fof(f577,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2))) ) | ~spl2_29),
% 0.21/0.44    inference(avatar_component_clause,[],[f576])).
% 0.21/0.44  fof(f578,plain,(
% 0.21/0.44    spl2_29 | ~spl2_4 | ~spl2_5 | ~spl2_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f75,f51,f47,f39,f576])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2)) = k2_xboole_0(X1,k4_xboole_0(X1,X2))) ) | (~spl2_4 | ~spl2_5 | ~spl2_6)),
% 0.21/0.44    inference(forward_demodulation,[],[f73,f40])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k2_xboole_0(k4_xboole_0(X1,X2),X1) = k5_xboole_0(k4_xboole_0(X1,X2),k3_xboole_0(X1,X2))) ) | (~spl2_5 | ~spl2_6)),
% 0.21/0.44    inference(superposition,[],[f52,f48])).
% 0.21/0.44  fof(f452,plain,(
% 0.21/0.44    spl2_26 | ~spl2_6 | ~spl2_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f127,f92,f51,f450])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    spl2_11 <=> ! [X1,X0,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    ( ! [X6,X8,X7] : (k2_xboole_0(X8,k4_xboole_0(X6,X7)) = k5_xboole_0(X8,k4_xboole_0(X6,k2_xboole_0(X7,X8)))) ) | (~spl2_6 | ~spl2_11)),
% 0.21/0.44    inference(superposition,[],[f52,f93])).
% 0.21/0.44  fof(f93,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) ) | ~spl2_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f92])).
% 0.21/0.44  fof(f177,plain,(
% 0.21/0.44    spl2_17 | ~spl2_4 | ~spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f82,f63,f39,f175])).
% 0.21/0.44  fof(f63,plain,(
% 0.21/0.44    spl2_9 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k4_xboole_0(k2_xboole_0(X2,X1),X2)) ) | (~spl2_4 | ~spl2_9)),
% 0.21/0.44    inference(superposition,[],[f64,f40])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl2_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f63])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    spl2_15 | ~spl2_2 | ~spl2_7 | ~spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f100,f63,f55,f31,f162])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    spl2_2 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.44  fof(f55,plain,(
% 0.21/0.44    spl2_7 <=> ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | (~spl2_2 | ~spl2_7 | ~spl2_9)),
% 0.21/0.44    inference(forward_demodulation,[],[f97,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) ) | ~spl2_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f31])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    ( ! [X0] : (k4_xboole_0(k1_xboole_0,X0) = k4_xboole_0(X0,X0)) ) | (~spl2_7 | ~spl2_9)),
% 0.21/0.44    inference(superposition,[],[f64,f56])).
% 0.21/0.44  fof(f56,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | ~spl2_7),
% 0.21/0.44    inference(avatar_component_clause,[],[f55])).
% 0.21/0.44  fof(f153,plain,(
% 0.21/0.44    spl2_14 | ~spl2_5 | ~spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f71,f59,f47,f151])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k3_xboole_0(X1,k4_xboole_0(X1,X2))) ) | (~spl2_5 | ~spl2_8)),
% 0.21/0.44    inference(forward_demodulation,[],[f67,f60])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k3_xboole_0(X1,k4_xboole_0(X1,X2)) = k4_xboole_0(X1,k3_xboole_0(X1,X2))) ) | ~spl2_5),
% 0.21/0.44    inference(superposition,[],[f48,f48])).
% 0.21/0.44  fof(f149,plain,(
% 0.21/0.44    spl2_13 | ~spl2_2 | ~spl2_3 | ~spl2_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f74,f51,f35,f31,f147])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | (~spl2_2 | ~spl2_3 | ~spl2_6)),
% 0.21/0.44    inference(forward_demodulation,[],[f72,f36])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = k5_xboole_0(X0,k1_xboole_0)) ) | (~spl2_2 | ~spl2_6)),
% 0.21/0.44    inference(superposition,[],[f52,f32])).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    spl2_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f24,f92])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 0.21/0.44  fof(f90,plain,(
% 0.21/0.44    spl2_10),
% 0.21/0.44    inference(avatar_split_clause,[],[f23,f88])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : k5_xboole_0(X0,X1) = k2_xboole_0(k4_xboole_0(X0,X1),k4_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl2_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f22,f63])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.44  fof(f61,plain,(
% 0.21/0.44    spl2_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f21,f59])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f6])).
% 0.21/0.44  fof(f6,axiom,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    spl2_7 | ~spl2_3 | ~spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f42,f39,f35,f55])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) ) | (~spl2_3 | ~spl2_4)),
% 0.21/0.44    inference(superposition,[],[f40,f36])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    spl2_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f20,f51])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    spl2_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f19,f47])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    spl2_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f18,f39])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    spl2_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f17,f35])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    spl2_2),
% 0.21/0.44    inference(avatar_split_clause,[],[f16,f31])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : k1_xboole_0 = k4_xboole_0(k1_xboole_0,X0)),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ~spl2_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f15,f26])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f13])).
% 0.21/0.44  fof(f13,plain,(
% 0.21/0.44    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1)) => k4_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k3_xboole_0(sK0,sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f12,plain,(
% 0.21/0.44    ? [X0,X1] : k4_xboole_0(X0,X1) != k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    inference(negated_conjecture,[],[f10])).
% 0.21/0.44  fof(f10,conjecture,(
% 0.21/0.44    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.44    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (1149)------------------------------
% 0.21/0.44  % (1149)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (1149)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (1149)Memory used [KB]: 6780
% 0.21/0.44  % (1149)Time elapsed: 0.038 s
% 0.21/0.44  % (1149)------------------------------
% 0.21/0.44  % (1149)------------------------------
% 0.21/0.44  % (1143)Success in time 0.087 s
%------------------------------------------------------------------------------
