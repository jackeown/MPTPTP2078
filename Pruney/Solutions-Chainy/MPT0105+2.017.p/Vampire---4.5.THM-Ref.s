%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 127 expanded)
%              Number of leaves         :   25 (  61 expanded)
%              Depth                    :    9
%              Number of atoms          :  183 ( 269 expanded)
%              Number of equality atoms :   67 ( 110 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f962,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f43,f47,f57,f61,f65,f111,f213,f245,f260,f729,f958,f961])).

fof(f961,plain,
    ( spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_32
    | ~ spl2_38 ),
    inference(avatar_contradiction_clause,[],[f960])).

fof(f960,plain,
    ( $false
    | spl2_1
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_32
    | ~ spl2_38 ),
    inference(subsumption_resolution,[],[f26,f959])).

fof(f959,plain,
    ( ! [X4,X3] : k2_xboole_0(X3,X4) = k5_xboole_0(X3,k4_xboole_0(X4,X3))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_32
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f957,f746])).

fof(f746,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5))
    | ~ spl2_4
    | ~ spl2_6
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f745,f46])).

fof(f46,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f45])).

fof(f45,plain,
    ( spl2_6
  <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f745,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k5_xboole_0(X4,k3_xboole_0(X4,X5))
    | ~ spl2_4
    | ~ spl2_12
    | ~ spl2_19
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f744,f110])).

fof(f110,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl2_12
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f744,plain,
    ( ! [X4,X5] : k4_xboole_0(X4,k3_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(X4,k3_xboole_0(X4,X5))
    | ~ spl2_4
    | ~ spl2_19
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f738,f38])).

fof(f38,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f37])).

fof(f37,plain,
    ( spl2_4
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f738,plain,
    ( ! [X4,X5] : k5_xboole_0(X4,k3_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(k3_xboole_0(X4,X5),X4))
    | ~ spl2_19
    | ~ spl2_32 ),
    inference(superposition,[],[f244,f728])).

fof(f728,plain,
    ( ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl2_32
  <=> ! [X7,X6] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f244,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X1,X0))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f243])).

fof(f243,plain,
    ( spl2_19
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f957,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X3,X4)
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f956])).

fof(f956,plain,
    ( spl2_38
  <=> ! [X3,X4] : k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X3,X4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f26,plain,
    ( k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))
    | spl2_1 ),
    inference(avatar_component_clause,[],[f24])).

fof(f24,plain,
    ( spl2_1
  <=> k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f958,plain,
    ( spl2_38
    | ~ spl2_9
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f227,f211,f63,f956])).

fof(f63,plain,
    ( spl2_9
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f211,plain,
    ( spl2_18
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f227,plain,
    ( ! [X4,X3] : k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X3,X4)
    | ~ spl2_9
    | ~ spl2_18 ),
    inference(superposition,[],[f212,f64])).

fof(f64,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f63])).

fof(f212,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f211])).

fof(f729,plain,
    ( spl2_32
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f280,f258,f109,f33,f29,f727])).

fof(f29,plain,
    ( spl2_2
  <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f33,plain,
    ( spl2_3
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f258,plain,
    ( spl2_21
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f280,plain,
    ( ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_12
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f279,f34])).

fof(f34,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f279,plain,
    ( ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = k5_xboole_0(X6,k1_xboole_0)
    | ~ spl2_2
    | ~ spl2_12
    | ~ spl2_21 ),
    inference(forward_demodulation,[],[f264,f30])).

fof(f30,plain,
    ( ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f29])).

fof(f264,plain,
    ( ! [X6,X7] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)))
    | ~ spl2_12
    | ~ spl2_21 ),
    inference(superposition,[],[f259,f110])).

fof(f259,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f258])).

fof(f260,plain,
    ( spl2_21
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f80,f63,f55,f258])).

fof(f55,plain,
    ( spl2_7
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f80,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))
    | ~ spl2_7
    | ~ spl2_9 ),
    inference(superposition,[],[f64,f56])).

fof(f56,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f55])).

fof(f245,plain,
    ( spl2_19
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f72,f59,f37,f243])).

fof(f59,plain,
    ( spl2_8
  <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f72,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X1,X0))
    | ~ spl2_4
    | ~ spl2_8 ),
    inference(superposition,[],[f60,f38])).

fof(f60,plain,
    ( ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f59])).

fof(f213,plain,
    ( spl2_18
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f69,f55,f37,f211])).

fof(f69,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(superposition,[],[f56,f38])).

fof(f111,plain,
    ( spl2_12
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f53,f45,f41,f109])).

fof(f41,plain,
    ( spl2_5
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f53,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f52,f42])).

fof(f42,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f41])).

fof(f52,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(superposition,[],[f42,f46])).

fof(f65,plain,(
    spl2_9 ),
    inference(avatar_split_clause,[],[f22,f63])).

fof(f22,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f61,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f21,f59])).

fof(f21,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

fof(f57,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f20,f55])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

fof(f47,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f19,f45])).

fof(f19,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f43,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f18,f41])).

fof(f18,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f35,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

fof(f31,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f15,f29])).

fof(f15,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

fof(f27,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f14,f24])).

fof(f14,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).

fof(f12,plain,
    ( ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))
   => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n009.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:20:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.46  % (8409)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.47  % (8406)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.47  % (8404)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (8400)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.47  % (8415)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.47  % (8405)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (8411)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (8410)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (8411)Refutation not found, incomplete strategy% (8411)------------------------------
% 0.21/0.48  % (8411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8411)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8411)Memory used [KB]: 10490
% 0.21/0.48  % (8411)Time elapsed: 0.064 s
% 0.21/0.48  % (8411)------------------------------
% 0.21/0.48  % (8411)------------------------------
% 0.21/0.48  % (8402)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.48  % (8407)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.48  % (8417)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.49  % (8408)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (8403)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.49  % (8412)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (8414)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (8401)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.51  % (8413)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (8416)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.53  % (8405)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f962,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f27,f31,f35,f39,f43,f47,f57,f61,f65,f111,f213,f245,f260,f729,f958,f961])).
% 0.21/0.53  fof(f961,plain,(
% 0.21/0.53    spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_12 | ~spl2_19 | ~spl2_32 | ~spl2_38),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f960])).
% 0.21/0.53  fof(f960,plain,(
% 0.21/0.53    $false | (spl2_1 | ~spl2_4 | ~spl2_6 | ~spl2_12 | ~spl2_19 | ~spl2_32 | ~spl2_38)),
% 0.21/0.53    inference(subsumption_resolution,[],[f26,f959])).
% 0.21/0.53  fof(f959,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k2_xboole_0(X3,X4) = k5_xboole_0(X3,k4_xboole_0(X4,X3))) ) | (~spl2_4 | ~spl2_6 | ~spl2_12 | ~spl2_19 | ~spl2_32 | ~spl2_38)),
% 0.21/0.53    inference(forward_demodulation,[],[f957,f746])).
% 0.21/0.53  fof(f746,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k4_xboole_0(X4,X5) = k5_xboole_0(X4,k3_xboole_0(X4,X5))) ) | (~spl2_4 | ~spl2_6 | ~spl2_12 | ~spl2_19 | ~spl2_32)),
% 0.21/0.53    inference(forward_demodulation,[],[f745,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) ) | ~spl2_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    spl2_6 <=> ! [X1,X0] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.21/0.53  fof(f745,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k4_xboole_0(X4,k3_xboole_0(X4,X5)) = k5_xboole_0(X4,k3_xboole_0(X4,X5))) ) | (~spl2_4 | ~spl2_12 | ~spl2_19 | ~spl2_32)),
% 0.21/0.53    inference(forward_demodulation,[],[f744,f110])).
% 0.21/0.53  fof(f110,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f109])).
% 0.21/0.53  fof(f109,plain,(
% 0.21/0.53    spl2_12 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.21/0.53  fof(f744,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k4_xboole_0(X4,k3_xboole_0(X4,k3_xboole_0(X4,X5))) = k5_xboole_0(X4,k3_xboole_0(X4,X5))) ) | (~spl2_4 | ~spl2_19 | ~spl2_32)),
% 0.21/0.53    inference(forward_demodulation,[],[f738,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    spl2_4 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.21/0.53  fof(f738,plain,(
% 0.21/0.53    ( ! [X4,X5] : (k5_xboole_0(X4,k3_xboole_0(X4,X5)) = k4_xboole_0(X4,k3_xboole_0(k3_xboole_0(X4,X5),X4))) ) | (~spl2_19 | ~spl2_32)),
% 0.21/0.53    inference(superposition,[],[f244,f728])).
% 0.21/0.53  fof(f728,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6) ) | ~spl2_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f727])).
% 0.21/0.53  fof(f727,plain,(
% 0.21/0.53    spl2_32 <=> ! [X7,X6] : k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.21/0.53  fof(f244,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X1,X0))) ) | ~spl2_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f243])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    spl2_19 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X1,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.21/0.53  fof(f957,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X3,X4)) ) | ~spl2_38),
% 0.21/0.53    inference(avatar_component_clause,[],[f956])).
% 0.21/0.53  fof(f956,plain,(
% 0.21/0.53    spl2_38 <=> ! [X3,X4] : k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X3,X4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0)) | spl2_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    spl2_1 <=> k2_xboole_0(sK0,sK1) = k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.21/0.53  fof(f958,plain,(
% 0.21/0.53    spl2_38 | ~spl2_9 | ~spl2_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f227,f211,f63,f956])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl2_9 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    spl2_18 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.21/0.53  fof(f227,plain,(
% 0.21/0.53    ( ! [X4,X3] : (k5_xboole_0(X3,k5_xboole_0(X4,k3_xboole_0(X4,X3))) = k2_xboole_0(X3,X4)) ) | (~spl2_9 | ~spl2_18)),
% 0.21/0.53    inference(superposition,[],[f212,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))) ) | ~spl2_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f211])).
% 0.21/0.53  fof(f729,plain,(
% 0.21/0.53    spl2_32 | ~spl2_2 | ~spl2_3 | ~spl2_12 | ~spl2_21),
% 0.21/0.53    inference(avatar_split_clause,[],[f280,f258,f109,f33,f29,f727])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    spl2_2 <=> ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    spl2_3 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    spl2_21 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = X6) ) | (~spl2_2 | ~spl2_3 | ~spl2_12 | ~spl2_21)),
% 0.21/0.53    inference(forward_demodulation,[],[f279,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f33])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = k5_xboole_0(X6,k1_xboole_0)) ) | (~spl2_2 | ~spl2_12 | ~spl2_21)),
% 0.21/0.53    inference(forward_demodulation,[],[f264,f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) ) | ~spl2_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f29])).
% 0.21/0.53  fof(f264,plain,(
% 0.21/0.53    ( ! [X6,X7] : (k2_xboole_0(X6,k3_xboole_0(X6,X7)) = k5_xboole_0(X6,k5_xboole_0(k3_xboole_0(X6,X7),k3_xboole_0(X6,X7)))) ) | (~spl2_12 | ~spl2_21)),
% 0.21/0.53    inference(superposition,[],[f259,f110])).
% 0.21/0.53  fof(f259,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) ) | ~spl2_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f258])).
% 0.21/0.53  fof(f260,plain,(
% 0.21/0.53    spl2_21 | ~spl2_7 | ~spl2_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f80,f63,f55,f258])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    spl2_7 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) ) | (~spl2_7 | ~spl2_9)),
% 0.21/0.53    inference(superposition,[],[f64,f56])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f55])).
% 0.21/0.53  fof(f245,plain,(
% 0.21/0.53    spl2_19 | ~spl2_4 | ~spl2_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f72,f59,f37,f243])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    spl2_8 <=> ! [X1,X0] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X1,X0))) ) | (~spl2_4 | ~spl2_8)),
% 0.21/0.53    inference(superposition,[],[f60,f38])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) ) | ~spl2_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f59])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    spl2_18 | ~spl2_4 | ~spl2_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f69,f55,f37,f211])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X1,X0))) ) | (~spl2_4 | ~spl2_7)),
% 0.21/0.53    inference(superposition,[],[f56,f38])).
% 0.21/0.53  fof(f111,plain,(
% 0.21/0.53    spl2_12 | ~spl2_5 | ~spl2_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f53,f45,f41,f109])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    spl2_5 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) ) | (~spl2_5 | ~spl2_6)),
% 0.21/0.53    inference(forward_demodulation,[],[f52,f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) ) | ~spl2_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f41])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,k3_xboole_0(X0,X1))) ) | (~spl2_5 | ~spl2_6)),
% 0.21/0.53    inference(superposition,[],[f42,f46])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    spl2_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f22,f63])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl2_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f21,f59])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    spl2_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f20,f55])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    spl2_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f19,f45])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : k4_xboole_0(X0,k3_xboole_0(X0,X1)) = k4_xboole_0(X0,X1)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    spl2_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f18,f41])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    spl2_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f17,f37])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    spl2_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f16,f33])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.21/0.53    inference(cnf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    spl2_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f15,f29])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ~spl2_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f14,f24])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f11,f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0)) => k2_xboole_0(sK0,sK1) != k5_xboole_0(sK0,k4_xboole_0(sK1,sK0))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0,X1] : k2_xboole_0(X0,X1) != k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,negated_conjecture,(
% 0.21/0.53    ~! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    inference(negated_conjecture,[],[f9])).
% 0.21/0.53  fof(f9,conjecture,(
% 0.21/0.53    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (8405)------------------------------
% 0.21/0.53  % (8405)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (8405)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (8405)Memory used [KB]: 7036
% 0.21/0.53  % (8405)Time elapsed: 0.115 s
% 0.21/0.53  % (8405)------------------------------
% 0.21/0.53  % (8405)------------------------------
% 0.21/0.53  % (8399)Success in time 0.165 s
%------------------------------------------------------------------------------
