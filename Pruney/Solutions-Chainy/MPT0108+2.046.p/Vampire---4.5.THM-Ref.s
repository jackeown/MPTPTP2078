%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:24 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 191 expanded)
%              Number of leaves         :   29 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  238 ( 394 expanded)
%              Number of equality atoms :   82 ( 155 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    7 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3904,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f45,f53,f65,f71,f82,f142,f193,f250,f254,f514,f518,f589,f683,f707,f1480,f2272,f3022,f3034,f3742])).

fof(f3742,plain,
    ( ~ spl2_3
    | ~ spl2_20
    | ~ spl2_42
    | spl2_56
    | ~ spl2_67
    | ~ spl2_70 ),
    inference(avatar_contradiction_clause,[],[f3741])).

fof(f3741,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_20
    | ~ spl2_42
    | spl2_56
    | ~ spl2_67
    | ~ spl2_70 ),
    inference(subsumption_resolution,[],[f3740,f722])).

fof(f722,plain,
    ( ! [X10,X11,X9] : k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),X11)
    | ~ spl2_20
    | ~ spl2_42 ),
    inference(superposition,[],[f706,f249])).

fof(f249,plain,
    ( ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl2_20
  <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f706,plain,
    ( ! [X2,X3] : k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2
    | ~ spl2_42 ),
    inference(avatar_component_clause,[],[f705])).

fof(f705,plain,
    ( spl2_42
  <=> ! [X3,X2] : k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).

fof(f3740,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1))
    | ~ spl2_3
    | spl2_56
    | ~ spl2_67
    | ~ spl2_70 ),
    inference(forward_demodulation,[],[f3739,f52])).

fof(f52,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f51,plain,
    ( spl2_3
  <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f3739,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,sK0))
    | spl2_56
    | ~ spl2_67
    | ~ spl2_70 ),
    inference(backward_demodulation,[],[f1479,f3509])).

fof(f3509,plain,
    ( ! [X47,X48,X49] : k3_xboole_0(X49,X47) = k3_xboole_0(X47,k3_xboole_0(X49,k5_xboole_0(X47,k5_xboole_0(X48,k3_xboole_0(X47,X48)))))
    | ~ spl2_67
    | ~ spl2_70 ),
    inference(superposition,[],[f3033,f3021])).

fof(f3021,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0
    | ~ spl2_67 ),
    inference(avatar_component_clause,[],[f3020])).

fof(f3020,plain,
    ( spl2_67
  <=> ! [X1,X0] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).

fof(f3033,plain,
    ( ! [X12,X13,X11] : k3_xboole_0(X11,k3_xboole_0(X12,X13)) = k3_xboole_0(X12,k3_xboole_0(X11,X13))
    | ~ spl2_70 ),
    inference(avatar_component_clause,[],[f3032])).

fof(f3032,plain,
    ( spl2_70
  <=> ! [X11,X13,X12] : k3_xboole_0(X11,k3_xboole_0(X12,X13)) = k3_xboole_0(X12,k3_xboole_0(X11,X13)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).

fof(f1479,plain,
    ( k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))
    | spl2_56 ),
    inference(avatar_component_clause,[],[f1477])).

fof(f1477,plain,
    ( spl2_56
  <=> k5_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f3034,plain,
    ( spl2_70
    | ~ spl2_21
    | ~ spl2_63 ),
    inference(avatar_split_clause,[],[f2432,f2270,f252,f3032])).

fof(f252,plain,
    ( spl2_21
  <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f2270,plain,
    ( spl2_63
  <=> ! [X1,X0,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f2432,plain,
    ( ! [X12,X13,X11] : k3_xboole_0(X11,k3_xboole_0(X12,X13)) = k3_xboole_0(X12,k3_xboole_0(X11,X13))
    | ~ spl2_21
    | ~ spl2_63 ),
    inference(superposition,[],[f2271,f253])).

fof(f253,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f252])).

fof(f2271,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2)
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f2270])).

fof(f3022,plain,
    ( spl2_67
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f101,f80,f63,f3020])).

fof(f63,plain,
    ( spl2_5
  <=> ! [X1,X0] :
        ( k3_xboole_0(X0,X1) = X0
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f80,plain,
    ( spl2_8
  <=> ! [X1,X0] : r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f101,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0
    | ~ spl2_5
    | ~ spl2_8 ),
    inference(resolution,[],[f81,f64])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k3_xboole_0(X0,X1) = X0 )
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f63])).

fof(f81,plain,
    ( ! [X0,X1] : r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f2272,plain,
    ( spl2_63
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(avatar_split_clause,[],[f288,f252,f51,f2270])).

fof(f288,plain,
    ( ! [X2,X0,X1] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2)
    | ~ spl2_3
    | ~ spl2_21 ),
    inference(superposition,[],[f253,f52])).

fof(f1480,plain,(
    ~ spl2_56 ),
    inference(avatar_split_clause,[],[f40,f1477])).

fof(f40,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) ),
    inference(backward_demodulation,[],[f39,f31])).

fof(f31,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f39,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f38,f23])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f38,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))))) ),
    inference(backward_demodulation,[],[f33,f23])).

fof(f33,plain,(
    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1))) ),
    inference(definition_unfolding,[],[f19,f25,f32])).

fof(f32,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(definition_unfolding,[],[f24,f25])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

fof(f25,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f19,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))
   => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).

fof(f707,plain,
    ( spl2_42
    | ~ spl2_38
    | ~ spl2_41 ),
    inference(avatar_split_clause,[],[f686,f681,f587,f705])).

fof(f587,plain,
    ( spl2_38
  <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f681,plain,
    ( spl2_41
  <=> ! [X1,X2] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f686,plain,
    ( ! [X2,X3] : k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2
    | ~ spl2_38
    | ~ spl2_41 ),
    inference(superposition,[],[f682,f588])).

fof(f588,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3
    | ~ spl2_38 ),
    inference(avatar_component_clause,[],[f587])).

fof(f682,plain,
    ( ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1
    | ~ spl2_41 ),
    inference(avatar_component_clause,[],[f681])).

fof(f683,plain,
    ( spl2_41
    | ~ spl2_1
    | ~ spl2_31
    | ~ spl2_38 ),
    inference(avatar_split_clause,[],[f671,f587,f516,f43,f681])).

fof(f43,plain,
    ( spl2_1
  <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f516,plain,
    ( spl2_31
  <=> ! [X5,X6] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f671,plain,
    ( ! [X2,X1] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1
    | ~ spl2_1
    | ~ spl2_31
    | ~ spl2_38 ),
    inference(forward_demodulation,[],[f660,f44])).

fof(f44,plain,
    ( ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f43])).

fof(f660,plain,
    ( ! [X2,X1] : k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))
    | ~ spl2_31
    | ~ spl2_38 ),
    inference(superposition,[],[f588,f517])).

fof(f517,plain,
    ( ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))
    | ~ spl2_31 ),
    inference(avatar_component_clause,[],[f516])).

fof(f589,plain,
    ( spl2_38
    | ~ spl2_1
    | ~ spl2_16
    | ~ spl2_30 ),
    inference(avatar_split_clause,[],[f550,f512,f191,f43,f587])).

fof(f191,plain,
    ( spl2_16
  <=> ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f512,plain,
    ( spl2_30
  <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f550,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3
    | ~ spl2_1
    | ~ spl2_16
    | ~ spl2_30 ),
    inference(backward_demodulation,[],[f513,f549])).

fof(f549,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = X1
    | ~ spl2_1
    | ~ spl2_16
    | ~ spl2_30 ),
    inference(forward_demodulation,[],[f536,f44])).

fof(f536,plain,
    ( ! [X1] : k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0)
    | ~ spl2_16
    | ~ spl2_30 ),
    inference(superposition,[],[f513,f192])).

fof(f192,plain,
    ( ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6)
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f191])).

fof(f513,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)
    | ~ spl2_30 ),
    inference(avatar_component_clause,[],[f512])).

fof(f518,plain,
    ( spl2_31
    | ~ spl2_16
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f260,f248,f191,f516])).

fof(f260,plain,
    ( ! [X6,X5] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))
    | ~ spl2_16
    | ~ spl2_20 ),
    inference(superposition,[],[f249,f192])).

fof(f514,plain,
    ( spl2_30
    | ~ spl2_16
    | ~ spl2_20 ),
    inference(avatar_split_clause,[],[f256,f248,f191,f512])).

fof(f256,plain,
    ( ! [X2,X3] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)
    | ~ spl2_16
    | ~ spl2_20 ),
    inference(superposition,[],[f249,f192])).

fof(f254,plain,(
    spl2_21 ),
    inference(avatar_split_clause,[],[f31,f252])).

fof(f250,plain,(
    spl2_20 ),
    inference(avatar_split_clause,[],[f29,f248])).

fof(f29,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f193,plain,
    ( spl2_16
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f180,f140,f69,f63,f191])).

fof(f69,plain,
    ( spl2_6
  <=> ! [X1,X0] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f140,plain,
    ( spl2_12
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
        | ~ r1_tarski(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f180,plain,
    ( ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6)
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f168,f72])).

fof(f72,plain,
    ( ! [X0,X1] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(resolution,[],[f70,f64])).

fof(f70,plain,
    ( ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f69])).

fof(f168,plain,
    ( ! [X6,X7] : k1_xboole_0 = k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6)))))
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(resolution,[],[f141,f70])).

fof(f141,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X0,X1)
        | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) )
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f142,plain,(
    spl2_12 ),
    inference(avatar_split_clause,[],[f35,f140])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f28,f25])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f82,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f73,f69,f51,f80])).

fof(f73,plain,
    ( ! [X0,X1] : r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(superposition,[],[f70,f52])).

fof(f71,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f34,f69])).

fof(f34,plain,(
    ! [X0,X1] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) ),
    inference(definition_unfolding,[],[f21,f32])).

fof(f21,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f65,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f26,f63])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f23,f51])).

fof(f45,plain,(
    spl2_1 ),
    inference(avatar_split_clause,[],[f20,f43])).

fof(f20,plain,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n016.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:42:34 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (1935)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (1942)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.22/0.49  % (1943)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.49  % (1933)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.49  % (1943)Refutation not found, incomplete strategy% (1943)------------------------------
% 0.22/0.49  % (1943)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (1943)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (1943)Memory used [KB]: 10618
% 0.22/0.49  % (1943)Time elapsed: 0.038 s
% 0.22/0.49  % (1943)------------------------------
% 0.22/0.49  % (1943)------------------------------
% 0.22/0.49  % (1936)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (1939)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.50  % (1944)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.22/0.50  % (1932)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.22/0.50  % (1948)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.22/0.52  % (1940)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.22/0.52  % (1945)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.52  % (1937)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.22/0.53  % (1938)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.53  % (1934)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 1.32/0.54  % (1941)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 1.32/0.54  % (1947)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.32/0.55  % (1949)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 1.53/0.56  % (1946)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.53/0.61  % (1939)Refutation found. Thanks to Tanya!
% 1.53/0.61  % SZS status Theorem for theBenchmark
% 1.53/0.61  % SZS output start Proof for theBenchmark
% 1.53/0.61  fof(f3904,plain,(
% 1.53/0.61    $false),
% 1.53/0.61    inference(avatar_sat_refutation,[],[f45,f53,f65,f71,f82,f142,f193,f250,f254,f514,f518,f589,f683,f707,f1480,f2272,f3022,f3034,f3742])).
% 1.53/0.61  fof(f3742,plain,(
% 1.53/0.61    ~spl2_3 | ~spl2_20 | ~spl2_42 | spl2_56 | ~spl2_67 | ~spl2_70),
% 1.53/0.61    inference(avatar_contradiction_clause,[],[f3741])).
% 1.53/0.61  fof(f3741,plain,(
% 1.53/0.61    $false | (~spl2_3 | ~spl2_20 | ~spl2_42 | spl2_56 | ~spl2_67 | ~spl2_70)),
% 1.53/0.61    inference(subsumption_resolution,[],[f3740,f722])).
% 1.53/0.61  fof(f722,plain,(
% 1.53/0.61    ( ! [X10,X11,X9] : (k5_xboole_0(X9,X10) = k5_xboole_0(k5_xboole_0(X9,k5_xboole_0(X10,X11)),X11)) ) | (~spl2_20 | ~spl2_42)),
% 1.53/0.61    inference(superposition,[],[f706,f249])).
% 1.53/0.61  fof(f249,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) ) | ~spl2_20),
% 1.53/0.61    inference(avatar_component_clause,[],[f248])).
% 1.53/0.61  fof(f248,plain,(
% 1.53/0.61    spl2_20 <=> ! [X1,X0,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 1.53/0.61  fof(f706,plain,(
% 1.53/0.61    ( ! [X2,X3] : (k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2) ) | ~spl2_42),
% 1.53/0.61    inference(avatar_component_clause,[],[f705])).
% 1.53/0.61  fof(f705,plain,(
% 1.53/0.61    spl2_42 <=> ! [X3,X2] : k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_42])])).
% 1.53/0.61  fof(f3740,plain,(
% 1.53/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,sK1)) | (~spl2_3 | spl2_56 | ~spl2_67 | ~spl2_70)),
% 1.53/0.61    inference(forward_demodulation,[],[f3739,f52])).
% 1.53/0.61  fof(f52,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) ) | ~spl2_3),
% 1.53/0.61    inference(avatar_component_clause,[],[f51])).
% 1.53/0.61  fof(f51,plain,(
% 1.53/0.61    spl2_3 <=> ! [X1,X0] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 1.53/0.61  fof(f3739,plain,(
% 1.53/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK1,sK0)) | (spl2_56 | ~spl2_67 | ~spl2_70)),
% 1.53/0.61    inference(backward_demodulation,[],[f1479,f3509])).
% 1.53/0.61  fof(f3509,plain,(
% 1.53/0.61    ( ! [X47,X48,X49] : (k3_xboole_0(X49,X47) = k3_xboole_0(X47,k3_xboole_0(X49,k5_xboole_0(X47,k5_xboole_0(X48,k3_xboole_0(X47,X48)))))) ) | (~spl2_67 | ~spl2_70)),
% 1.53/0.61    inference(superposition,[],[f3033,f3021])).
% 1.53/0.61  fof(f3021,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0) ) | ~spl2_67),
% 1.53/0.61    inference(avatar_component_clause,[],[f3020])).
% 1.53/0.61  fof(f3020,plain,(
% 1.53/0.61    spl2_67 <=> ! [X1,X0] : k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_67])])).
% 1.53/0.61  fof(f3033,plain,(
% 1.53/0.61    ( ! [X12,X13,X11] : (k3_xboole_0(X11,k3_xboole_0(X12,X13)) = k3_xboole_0(X12,k3_xboole_0(X11,X13))) ) | ~spl2_70),
% 1.53/0.61    inference(avatar_component_clause,[],[f3032])).
% 1.53/0.61  fof(f3032,plain,(
% 1.53/0.61    spl2_70 <=> ! [X11,X13,X12] : k3_xboole_0(X11,k3_xboole_0(X12,X13)) = k3_xboole_0(X12,k3_xboole_0(X11,X13))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_70])])).
% 1.53/0.61  fof(f1479,plain,(
% 1.53/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))) | spl2_56),
% 1.53/0.61    inference(avatar_component_clause,[],[f1477])).
% 1.53/0.61  fof(f1477,plain,(
% 1.53/0.61    spl2_56 <=> k5_xboole_0(sK0,sK1) = k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 1.53/0.61  fof(f3034,plain,(
% 1.53/0.61    spl2_70 | ~spl2_21 | ~spl2_63),
% 1.53/0.61    inference(avatar_split_clause,[],[f2432,f2270,f252,f3032])).
% 1.53/0.61  fof(f252,plain,(
% 1.53/0.61    spl2_21 <=> ! [X1,X0,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 1.53/0.61  fof(f2270,plain,(
% 1.53/0.61    spl2_63 <=> ! [X1,X0,X2] : k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2)),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 1.53/0.61  fof(f2432,plain,(
% 1.53/0.61    ( ! [X12,X13,X11] : (k3_xboole_0(X11,k3_xboole_0(X12,X13)) = k3_xboole_0(X12,k3_xboole_0(X11,X13))) ) | (~spl2_21 | ~spl2_63)),
% 1.53/0.61    inference(superposition,[],[f2271,f253])).
% 1.53/0.61  fof(f253,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) ) | ~spl2_21),
% 1.53/0.61    inference(avatar_component_clause,[],[f252])).
% 1.53/0.61  fof(f2271,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2)) ) | ~spl2_63),
% 1.53/0.61    inference(avatar_component_clause,[],[f2270])).
% 1.53/0.61  fof(f3022,plain,(
% 1.53/0.61    spl2_67 | ~spl2_5 | ~spl2_8),
% 1.53/0.61    inference(avatar_split_clause,[],[f101,f80,f63,f3020])).
% 1.53/0.61  fof(f63,plain,(
% 1.53/0.61    spl2_5 <=> ! [X1,X0] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 1.53/0.61  fof(f80,plain,(
% 1.53/0.61    spl2_8 <=> ! [X1,X0] : r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 1.53/0.61  fof(f101,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X0,X1)))) = X0) ) | (~spl2_5 | ~spl2_8)),
% 1.53/0.61    inference(resolution,[],[f81,f64])).
% 1.53/0.61  fof(f64,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) ) | ~spl2_5),
% 1.53/0.61    inference(avatar_component_clause,[],[f63])).
% 1.53/0.61  fof(f81,plain,(
% 1.53/0.61    ( ! [X0,X1] : (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) ) | ~spl2_8),
% 1.53/0.61    inference(avatar_component_clause,[],[f80])).
% 1.53/0.61  fof(f2272,plain,(
% 1.53/0.61    spl2_63 | ~spl2_3 | ~spl2_21),
% 1.53/0.61    inference(avatar_split_clause,[],[f288,f252,f51,f2270])).
% 1.53/0.61  fof(f288,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(X0,k3_xboole_0(X1,X2)) = k3_xboole_0(k3_xboole_0(X1,X0),X2)) ) | (~spl2_3 | ~spl2_21)),
% 1.53/0.61    inference(superposition,[],[f253,f52])).
% 1.53/0.61  fof(f1480,plain,(
% 1.53/0.61    ~spl2_56),
% 1.53/0.61    inference(avatar_split_clause,[],[f40,f1477])).
% 1.53/0.61  fof(f40,plain,(
% 1.53/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(sK0,k3_xboole_0(sK1,k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))))))),
% 1.53/0.61    inference(backward_demodulation,[],[f39,f31])).
% 1.53/0.61  fof(f31,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f4])).
% 1.53/0.61  fof(f4,axiom,(
% 1.53/0.61    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).
% 1.53/0.61  fof(f39,plain,(
% 1.53/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK0,sK1)))))),
% 1.53/0.61    inference(forward_demodulation,[],[f38,f23])).
% 1.53/0.61  fof(f23,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f1])).
% 1.53/0.61  fof(f1,axiom,(
% 1.53/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.53/0.61  fof(f38,plain,(
% 1.53/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k3_xboole_0(sK0,sK1),k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0)))))),
% 1.53/0.61    inference(backward_demodulation,[],[f33,f23])).
% 1.53/0.61  fof(f33,plain,(
% 1.53/0.61    k5_xboole_0(sK0,sK1) != k5_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(k5_xboole_0(sK0,k5_xboole_0(sK1,k3_xboole_0(sK1,sK0))),k3_xboole_0(sK0,sK1)))),
% 1.53/0.61    inference(definition_unfolding,[],[f19,f25,f32])).
% 1.53/0.61  fof(f32,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 1.53/0.61    inference(definition_unfolding,[],[f24,f25])).
% 1.53/0.61  fof(f24,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f11])).
% 1.53/0.61  fof(f11,axiom,(
% 1.53/0.61    ! [X0,X1] : k2_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).
% 1.53/0.61  fof(f25,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f3])).
% 1.53/0.61  fof(f3,axiom,(
% 1.53/0.61    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 1.53/0.61  fof(f19,plain,(
% 1.53/0.61    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.53/0.61    inference(cnf_transformation,[],[f17])).
% 1.53/0.61  fof(f17,plain,(
% 1.53/0.61    k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.53/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f16])).
% 1.53/0.61  fof(f16,plain,(
% 1.53/0.61    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1)) => k5_xboole_0(sK0,sK1) != k4_xboole_0(k2_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))),
% 1.53/0.61    introduced(choice_axiom,[])).
% 1.53/0.61  fof(f14,plain,(
% 1.53/0.61    ? [X0,X1] : k5_xboole_0(X0,X1) != k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.53/0.61    inference(ennf_transformation,[],[f13])).
% 1.53/0.61  fof(f13,negated_conjecture,(
% 1.53/0.61    ~! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.53/0.61    inference(negated_conjecture,[],[f12])).
% 1.53/0.61  fof(f12,conjecture,(
% 1.53/0.61    ! [X0,X1] : k5_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),k3_xboole_0(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_xboole_1)).
% 1.53/0.61  fof(f707,plain,(
% 1.53/0.61    spl2_42 | ~spl2_38 | ~spl2_41),
% 1.53/0.61    inference(avatar_split_clause,[],[f686,f681,f587,f705])).
% 1.53/0.61  fof(f587,plain,(
% 1.53/0.61    spl2_38 <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).
% 1.53/0.61  fof(f681,plain,(
% 1.53/0.61    spl2_41 <=> ! [X1,X2] : k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).
% 1.53/0.61  fof(f686,plain,(
% 1.53/0.61    ( ! [X2,X3] : (k5_xboole_0(k5_xboole_0(X2,X3),X3) = X2) ) | (~spl2_38 | ~spl2_41)),
% 1.53/0.61    inference(superposition,[],[f682,f588])).
% 1.53/0.61  fof(f588,plain,(
% 1.53/0.61    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) ) | ~spl2_38),
% 1.53/0.61    inference(avatar_component_clause,[],[f587])).
% 1.53/0.61  fof(f682,plain,(
% 1.53/0.61    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) ) | ~spl2_41),
% 1.53/0.61    inference(avatar_component_clause,[],[f681])).
% 1.53/0.61  fof(f683,plain,(
% 1.53/0.61    spl2_41 | ~spl2_1 | ~spl2_31 | ~spl2_38),
% 1.53/0.61    inference(avatar_split_clause,[],[f671,f587,f516,f43,f681])).
% 1.53/0.61  fof(f43,plain,(
% 1.53/0.61    spl2_1 <=> ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 1.53/0.61  fof(f516,plain,(
% 1.53/0.61    spl2_31 <=> ! [X5,X6] : k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).
% 1.53/0.61  fof(f671,plain,(
% 1.53/0.61    ( ! [X2,X1] : (k5_xboole_0(X2,k5_xboole_0(X1,X2)) = X1) ) | (~spl2_1 | ~spl2_31 | ~spl2_38)),
% 1.53/0.61    inference(forward_demodulation,[],[f660,f44])).
% 1.53/0.61  fof(f44,plain,(
% 1.53/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) ) | ~spl2_1),
% 1.53/0.61    inference(avatar_component_clause,[],[f43])).
% 1.53/0.61  fof(f660,plain,(
% 1.53/0.61    ( ! [X2,X1] : (k5_xboole_0(X1,k1_xboole_0) = k5_xboole_0(X2,k5_xboole_0(X1,X2))) ) | (~spl2_31 | ~spl2_38)),
% 1.53/0.61    inference(superposition,[],[f588,f517])).
% 1.53/0.61  fof(f517,plain,(
% 1.53/0.61    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) ) | ~spl2_31),
% 1.53/0.61    inference(avatar_component_clause,[],[f516])).
% 1.53/0.61  fof(f589,plain,(
% 1.53/0.61    spl2_38 | ~spl2_1 | ~spl2_16 | ~spl2_30),
% 1.53/0.61    inference(avatar_split_clause,[],[f550,f512,f191,f43,f587])).
% 1.53/0.61  fof(f191,plain,(
% 1.53/0.61    spl2_16 <=> ! [X6] : k1_xboole_0 = k5_xboole_0(X6,X6)),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 1.53/0.61  fof(f512,plain,(
% 1.53/0.61    spl2_30 <=> ! [X3,X2] : k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).
% 1.53/0.61  fof(f550,plain,(
% 1.53/0.61    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = X3) ) | (~spl2_1 | ~spl2_16 | ~spl2_30)),
% 1.53/0.61    inference(backward_demodulation,[],[f513,f549])).
% 1.53/0.61  fof(f549,plain,(
% 1.53/0.61    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = X1) ) | (~spl2_1 | ~spl2_16 | ~spl2_30)),
% 1.53/0.61    inference(forward_demodulation,[],[f536,f44])).
% 1.53/0.61  fof(f536,plain,(
% 1.53/0.61    ( ! [X1] : (k5_xboole_0(k1_xboole_0,X1) = k5_xboole_0(X1,k1_xboole_0)) ) | (~spl2_16 | ~spl2_30)),
% 1.53/0.61    inference(superposition,[],[f513,f192])).
% 1.53/0.61  fof(f192,plain,(
% 1.53/0.61    ( ! [X6] : (k1_xboole_0 = k5_xboole_0(X6,X6)) ) | ~spl2_16),
% 1.53/0.61    inference(avatar_component_clause,[],[f191])).
% 1.53/0.61  fof(f513,plain,(
% 1.53/0.61    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) ) | ~spl2_30),
% 1.53/0.61    inference(avatar_component_clause,[],[f512])).
% 1.53/0.61  fof(f518,plain,(
% 1.53/0.61    spl2_31 | ~spl2_16 | ~spl2_20),
% 1.53/0.61    inference(avatar_split_clause,[],[f260,f248,f191,f516])).
% 1.53/0.61  fof(f260,plain,(
% 1.53/0.61    ( ! [X6,X5] : (k1_xboole_0 = k5_xboole_0(X5,k5_xboole_0(X6,k5_xboole_0(X5,X6)))) ) | (~spl2_16 | ~spl2_20)),
% 1.53/0.61    inference(superposition,[],[f249,f192])).
% 1.53/0.61  fof(f514,plain,(
% 1.53/0.61    spl2_30 | ~spl2_16 | ~spl2_20),
% 1.53/0.61    inference(avatar_split_clause,[],[f256,f248,f191,f512])).
% 1.53/0.61  fof(f256,plain,(
% 1.53/0.61    ( ! [X2,X3] : (k5_xboole_0(X2,k5_xboole_0(X2,X3)) = k5_xboole_0(k1_xboole_0,X3)) ) | (~spl2_16 | ~spl2_20)),
% 1.53/0.61    inference(superposition,[],[f249,f192])).
% 1.53/0.61  fof(f254,plain,(
% 1.53/0.61    spl2_21),
% 1.53/0.61    inference(avatar_split_clause,[],[f31,f252])).
% 1.53/0.61  fof(f250,plain,(
% 1.53/0.61    spl2_20),
% 1.53/0.61    inference(avatar_split_clause,[],[f29,f248])).
% 1.53/0.61  fof(f29,plain,(
% 1.53/0.61    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f10])).
% 1.53/0.61  fof(f10,axiom,(
% 1.53/0.61    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.53/0.61  fof(f193,plain,(
% 1.53/0.61    spl2_16 | ~spl2_5 | ~spl2_6 | ~spl2_12),
% 1.53/0.61    inference(avatar_split_clause,[],[f180,f140,f69,f63,f191])).
% 1.53/0.61  fof(f69,plain,(
% 1.53/0.61    spl2_6 <=> ! [X1,X0] : r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 1.53/0.61  fof(f140,plain,(
% 1.53/0.61    spl2_12 <=> ! [X1,X0] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1))),
% 1.53/0.61    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 1.53/0.61  fof(f180,plain,(
% 1.53/0.61    ( ! [X6] : (k1_xboole_0 = k5_xboole_0(X6,X6)) ) | (~spl2_5 | ~spl2_6 | ~spl2_12)),
% 1.53/0.61    inference(forward_demodulation,[],[f168,f72])).
% 1.53/0.61  fof(f72,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) = X0) ) | (~spl2_5 | ~spl2_6)),
% 1.53/0.61    inference(resolution,[],[f70,f64])).
% 1.53/0.61  fof(f70,plain,(
% 1.53/0.61    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) ) | ~spl2_6),
% 1.53/0.61    inference(avatar_component_clause,[],[f69])).
% 1.53/0.61  fof(f168,plain,(
% 1.53/0.61    ( ! [X6,X7] : (k1_xboole_0 = k5_xboole_0(X6,k3_xboole_0(X6,k5_xboole_0(X6,k5_xboole_0(X7,k3_xboole_0(X7,X6)))))) ) | (~spl2_6 | ~spl2_12)),
% 1.53/0.61    inference(resolution,[],[f141,f70])).
% 1.53/0.61  fof(f141,plain,(
% 1.53/0.61    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl2_12),
% 1.53/0.61    inference(avatar_component_clause,[],[f140])).
% 1.53/0.61  fof(f142,plain,(
% 1.53/0.61    spl2_12),
% 1.53/0.61    inference(avatar_split_clause,[],[f35,f140])).
% 1.53/0.61  fof(f35,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k1_xboole_0 = k5_xboole_0(X0,k3_xboole_0(X0,X1)) | ~r1_tarski(X0,X1)) )),
% 1.53/0.61    inference(definition_unfolding,[],[f28,f25])).
% 1.53/0.61  fof(f28,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f18])).
% 1.53/0.61  fof(f18,plain,(
% 1.53/0.61    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 1.53/0.61    inference(nnf_transformation,[],[f2])).
% 1.53/0.61  fof(f2,axiom,(
% 1.53/0.61    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 1.53/0.61  fof(f82,plain,(
% 1.53/0.61    spl2_8 | ~spl2_3 | ~spl2_6),
% 1.53/0.61    inference(avatar_split_clause,[],[f73,f69,f51,f80])).
% 1.53/0.61  fof(f73,plain,(
% 1.53/0.61    ( ! [X0,X1] : (r1_tarski(X1,k5_xboole_0(X1,k5_xboole_0(X0,k3_xboole_0(X1,X0))))) ) | (~spl2_3 | ~spl2_6)),
% 1.53/0.61    inference(superposition,[],[f70,f52])).
% 1.53/0.61  fof(f71,plain,(
% 1.53/0.61    spl2_6),
% 1.53/0.61    inference(avatar_split_clause,[],[f34,f69])).
% 1.53/0.61  fof(f34,plain,(
% 1.53/0.61    ( ! [X0,X1] : (r1_tarski(X0,k5_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))))) )),
% 1.53/0.61    inference(definition_unfolding,[],[f21,f32])).
% 1.53/0.61  fof(f21,plain,(
% 1.53/0.61    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.53/0.61    inference(cnf_transformation,[],[f9])).
% 1.53/0.61  fof(f9,axiom,(
% 1.53/0.61    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.53/0.61  fof(f65,plain,(
% 1.53/0.61    spl2_5),
% 1.53/0.61    inference(avatar_split_clause,[],[f26,f63])).
% 1.53/0.61  fof(f26,plain,(
% 1.53/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 1.53/0.61    inference(cnf_transformation,[],[f15])).
% 1.53/0.61  fof(f15,plain,(
% 1.53/0.61    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 1.53/0.61    inference(ennf_transformation,[],[f6])).
% 1.53/0.61  fof(f6,axiom,(
% 1.53/0.61    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 1.53/0.61  fof(f53,plain,(
% 1.53/0.61    spl2_3),
% 1.53/0.61    inference(avatar_split_clause,[],[f23,f51])).
% 1.53/0.61  fof(f45,plain,(
% 1.53/0.61    spl2_1),
% 1.53/0.61    inference(avatar_split_clause,[],[f20,f43])).
% 1.53/0.61  fof(f20,plain,(
% 1.53/0.61    ( ! [X0] : (k5_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.53/0.61    inference(cnf_transformation,[],[f8])).
% 1.53/0.61  fof(f8,axiom,(
% 1.53/0.61    ! [X0] : k5_xboole_0(X0,k1_xboole_0) = X0),
% 1.53/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).
% 1.53/0.61  % SZS output end Proof for theBenchmark
% 1.53/0.61  % (1939)------------------------------
% 1.53/0.61  % (1939)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.61  % (1939)Termination reason: Refutation
% 1.53/0.61  
% 1.53/0.61  % (1939)Memory used [KB]: 9338
% 1.53/0.61  % (1939)Time elapsed: 0.145 s
% 1.53/0.61  % (1939)------------------------------
% 1.53/0.61  % (1939)------------------------------
% 1.53/0.62  % (1931)Success in time 0.252 s
%------------------------------------------------------------------------------
