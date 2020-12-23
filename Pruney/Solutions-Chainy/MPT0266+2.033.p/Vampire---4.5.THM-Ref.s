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
% DateTime   : Thu Dec  3 12:40:32 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 288 expanded)
%              Number of leaves         :   24 ( 104 expanded)
%              Depth                    :   13
%              Number of atoms          :  128 ( 350 expanded)
%              Number of equality atoms :   60 ( 264 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f942,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f79,f151,f811,f841,f903,f941])).

fof(f941,plain,
    ( spl3_1
    | ~ spl3_22 ),
    inference(avatar_contradiction_clause,[],[f934])).

fof(f934,plain,
    ( $false
    | spl3_1
    | ~ spl3_22 ),
    inference(unit_resulting_resolution,[],[f73,f902,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f43,f56])).

fof(f56,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1) ),
    inference(definition_unfolding,[],[f38,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) ),
    inference(definition_unfolding,[],[f41,f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] : k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3) ),
    inference(definition_unfolding,[],[f46,f53])).

fof(f53,plain,(
    ! [X4,X2,X0,X3,X1] : k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4) ),
    inference(definition_unfolding,[],[f47,f52])).

fof(f52,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5) ),
    inference(definition_unfolding,[],[f48,f49])).

fof(f49,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).

fof(f48,plain,(
    ! [X4,X2,X0,X5,X3,X1] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

fof(f47,plain,(
    ! [X4,X2,X0,X3,X1] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

fof(f46,plain,(
    ! [X2,X0,X3,X1] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

fof(f41,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

fof(f38,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f902,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl3_22
  <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f73,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl3_1
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f903,plain,
    ( spl3_22
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f886,f836,f900])).

fof(f836,plain,
    ( spl3_15
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f886,plain,
    ( r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)
    | ~ spl3_15 ),
    inference(superposition,[],[f121,f838])).

fof(f838,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f836])).

fof(f121,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0) ),
    inference(forward_demodulation,[],[f64,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

fof(f64,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0) ),
    inference(definition_unfolding,[],[f35,f58])).

fof(f58,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) ),
    inference(definition_unfolding,[],[f39,f57])).

fof(f57,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) ),
    inference(definition_unfolding,[],[f37,f56])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

fof(f35,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f841,plain,
    ( spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f817,f808,f836])).

fof(f808,plain,
    ( spl3_13
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f817,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))
    | ~ spl3_13 ),
    inference(superposition,[],[f42,f810])).

fof(f810,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f808])).

fof(f811,plain,
    ( spl3_13
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f767,f148,f808])).

fof(f148,plain,
    ( spl3_3
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f767,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl3_3 ),
    inference(backward_demodulation,[],[f150,f176])).

fof(f176,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6) ),
    inference(superposition,[],[f69,f60])).

fof(f60,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7))) ),
    inference(definition_unfolding,[],[f51,f57,f52,f56])).

fof(f51,plain,(
    ! [X6,X4,X2,X0,X7,X5,X3,X1] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).

fof(f69,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6))) ),
    inference(definition_unfolding,[],[f50,f49,f57,f52,f59])).

fof(f59,plain,(
    ! [X0] : k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0) ),
    inference(definition_unfolding,[],[f32,f56])).

fof(f32,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f50,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

fof(f150,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f148])).

fof(f151,plain,
    ( spl3_3
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f146,f76,f148])).

fof(f76,plain,
    ( spl3_2
  <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f146,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f145,f36])).

fof(f36,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f145,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f78,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] : k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0) ),
    inference(definition_unfolding,[],[f40,f55,f55])).

fof(f40,plain,(
    ! [X2,X0,X1] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

fof(f78,plain,
    ( k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f79,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f61,f76])).

fof(f61,plain,(
    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) ),
    inference(definition_unfolding,[],[f29,f56,f58,f56])).

fof(f29,plain,(
    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,
    ( ~ r2_hidden(sK0,sK2)
    & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ~ r2_hidden(X0,X2)
        & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) )
   => ( ~ r2_hidden(sK0,sK2)
      & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
       => r2_hidden(X0,X2) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)
     => r2_hidden(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).

fof(f74,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    ~ r2_hidden(sK0,sK2) ),
    inference(cnf_transformation,[],[f26])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:08:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.43  % (2995)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.46  % (2981)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (2989)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.47  % (2989)Refutation not found, incomplete strategy% (2989)------------------------------
% 0.21/0.47  % (2989)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (2989)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (2989)Memory used [KB]: 10618
% 0.21/0.47  % (2989)Time elapsed: 0.063 s
% 0.21/0.47  % (2989)------------------------------
% 0.21/0.47  % (2989)------------------------------
% 0.21/0.47  % (2983)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.48  % (2978)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.48  % (2986)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (2993)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.49  % (2979)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.49  % (2980)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.49  % (2990)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.49  % (2984)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.49  % (2987)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (2982)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (2992)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.50  % (2988)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.50  % (2994)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.50  % (2985)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.51  % (2991)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 1.50/0.55  % (2984)Refutation found. Thanks to Tanya!
% 1.50/0.55  % SZS status Theorem for theBenchmark
% 1.50/0.55  % SZS output start Proof for theBenchmark
% 1.50/0.55  fof(f942,plain,(
% 1.50/0.55    $false),
% 1.50/0.55    inference(avatar_sat_refutation,[],[f74,f79,f151,f811,f841,f903,f941])).
% 1.50/0.55  fof(f941,plain,(
% 1.50/0.55    spl3_1 | ~spl3_22),
% 1.50/0.55    inference(avatar_contradiction_clause,[],[f934])).
% 1.50/0.55  fof(f934,plain,(
% 1.50/0.55    $false | (spl3_1 | ~spl3_22)),
% 1.50/0.55    inference(unit_resulting_resolution,[],[f73,f902,f68])).
% 1.50/0.55  fof(f68,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (~r1_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f43,f56])).
% 1.50/0.55  fof(f56,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k2_tarski(X0,X1) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f38,f55])).
% 1.50/0.55  fof(f55,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f41,f54])).
% 1.50/0.55  fof(f54,plain,(
% 1.50/0.55    ( ! [X2,X0,X3,X1] : (k2_enumset1(X0,X1,X2,X3) = k6_enumset1(X0,X0,X0,X0,X0,X1,X2,X3)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f46,f53])).
% 1.50/0.55  fof(f53,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X3,X1] : (k3_enumset1(X0,X1,X2,X3,X4) = k6_enumset1(X0,X0,X0,X0,X1,X2,X3,X4)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f47,f52])).
% 1.50/0.55  fof(f52,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f48,f49])).
% 1.50/0.55  fof(f49,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f17])).
% 1.50/0.55  fof(f17,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_enumset1)).
% 1.50/0.55  fof(f48,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X5,X3,X1] : (k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f16])).
% 1.50/0.55  fof(f16,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3,X4,X5] : k4_enumset1(X0,X1,X2,X3,X4,X5) = k5_enumset1(X0,X0,X1,X2,X3,X4,X5)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).
% 1.50/0.55  fof(f47,plain,(
% 1.50/0.55    ( ! [X4,X2,X0,X3,X1] : (k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f15])).
% 1.50/0.55  fof(f15,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3,X4] : k4_enumset1(X0,X0,X1,X2,X3,X4) = k3_enumset1(X0,X1,X2,X3,X4)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).
% 1.50/0.55  fof(f46,plain,(
% 1.50/0.55    ( ! [X2,X0,X3,X1] : (k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f14])).
% 1.50/0.55  fof(f14,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3] : k3_enumset1(X0,X0,X1,X2,X3) = k2_enumset1(X0,X1,X2,X3)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).
% 1.50/0.55  fof(f41,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f13])).
% 1.50/0.55  fof(f13,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k2_enumset1(X0,X0,X1,X2)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).
% 1.50/0.55  fof(f38,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f12])).
% 1.50/0.55  fof(f12,axiom,(
% 1.50/0.55    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 1.50/0.55  fof(f43,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f28])).
% 1.50/0.55  fof(f28,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.50/0.55    inference(flattening,[],[f27])).
% 1.50/0.55  fof(f27,plain,(
% 1.50/0.55    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 1.50/0.55    inference(nnf_transformation,[],[f19])).
% 1.50/0.55  fof(f19,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 1.50/0.55  fof(f902,plain,(
% 1.50/0.55    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_22),
% 1.50/0.55    inference(avatar_component_clause,[],[f900])).
% 1.50/0.55  fof(f900,plain,(
% 1.50/0.55    spl3_22 <=> r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.50/0.55  fof(f73,plain,(
% 1.50/0.55    ~r2_hidden(sK0,sK2) | spl3_1),
% 1.50/0.55    inference(avatar_component_clause,[],[f71])).
% 1.50/0.55  fof(f71,plain,(
% 1.50/0.55    spl3_1 <=> r2_hidden(sK0,sK2)),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.50/0.55  fof(f903,plain,(
% 1.50/0.55    spl3_22 | ~spl3_15),
% 1.50/0.55    inference(avatar_split_clause,[],[f886,f836,f900])).
% 1.50/0.55  fof(f836,plain,(
% 1.50/0.55    spl3_15 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.50/0.55  fof(f886,plain,(
% 1.50/0.55    r1_tarski(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2) | ~spl3_15),
% 1.50/0.55    inference(superposition,[],[f121,f838])).
% 1.50/0.55  fof(f838,plain,(
% 1.50/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | ~spl3_15),
% 1.50/0.55    inference(avatar_component_clause,[],[f836])).
% 1.50/0.55  fof(f121,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k5_xboole_0(X1,k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))),X0)) )),
% 1.50/0.55    inference(forward_demodulation,[],[f64,f42])).
% 1.50/0.55  fof(f42,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f5])).
% 1.50/0.55  fof(f5,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : k5_xboole_0(k5_xboole_0(X0,X1),X2) = k5_xboole_0(X0,k5_xboole_0(X1,X2))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).
% 1.50/0.55  fof(f64,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))),X0)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f35,f58])).
% 1.50/0.55  fof(f58,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1)))) )),
% 1.50/0.55    inference(definition_unfolding,[],[f39,f57])).
% 1.50/0.55  fof(f57,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X1))) )),
% 1.50/0.55    inference(definition_unfolding,[],[f37,f56])).
% 1.50/0.55  fof(f37,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f18])).
% 1.50/0.55  fof(f18,axiom,(
% 1.50/0.55    ! [X0,X1] : k2_xboole_0(X0,X1) = k3_tarski(k2_tarski(X0,X1))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).
% 1.50/0.55  fof(f39,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f7])).
% 1.50/0.55  fof(f7,axiom,(
% 1.50/0.55    ! [X0,X1] : k3_xboole_0(X0,X1) = k5_xboole_0(k5_xboole_0(X0,X1),k2_xboole_0(X0,X1))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).
% 1.50/0.55  fof(f35,plain,(
% 1.50/0.55    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f4])).
% 1.50/0.55  fof(f4,axiom,(
% 1.50/0.55    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).
% 1.50/0.55  fof(f841,plain,(
% 1.50/0.55    spl3_15 | ~spl3_13),
% 1.50/0.55    inference(avatar_split_clause,[],[f817,f808,f836])).
% 1.50/0.55  fof(f808,plain,(
% 1.50/0.55    spl3_13 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.50/0.55  fof(f817,plain,(
% 1.50/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(sK2,k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))) | ~spl3_13),
% 1.50/0.55    inference(superposition,[],[f42,f810])).
% 1.50/0.55  fof(f810,plain,(
% 1.50/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl3_13),
% 1.50/0.55    inference(avatar_component_clause,[],[f808])).
% 1.50/0.55  fof(f811,plain,(
% 1.50/0.55    spl3_13 | ~spl3_3),
% 1.50/0.55    inference(avatar_split_clause,[],[f767,f148,f808])).
% 1.50/0.55  fof(f148,plain,(
% 1.50/0.55    spl3_3 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1))))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.50/0.55  fof(f767,plain,(
% 1.50/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl3_3),
% 1.50/0.55    inference(backward_demodulation,[],[f150,f176])).
% 1.50/0.55  fof(f176,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X6)) )),
% 1.50/0.55    inference(superposition,[],[f69,f60])).
% 1.50/0.55  fof(f60,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X7)))) )),
% 1.50/0.55    inference(definition_unfolding,[],[f51,f57,f52,f56])).
% 1.50/0.55  fof(f51,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X7,X5,X3,X1] : (k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f10])).
% 1.50/0.55  fof(f10,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3,X4,X5,X6,X7] : k6_enumset1(X0,X1,X2,X3,X4,X5,X6,X7) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k2_tarski(X6,X7))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_enumset1)).
% 1.50/0.55  fof(f69,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k6_enumset1(X0,X0,X1,X2,X3,X4,X5,X6) = k3_tarski(k6_enumset1(k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X0,X0,X0,X1,X2,X3,X4,X5),k6_enumset1(X6,X6,X6,X6,X6,X6,X6,X6)))) )),
% 1.50/0.55    inference(definition_unfolding,[],[f50,f49,f57,f52,f59])).
% 1.50/0.55  fof(f59,plain,(
% 1.50/0.55    ( ! [X0] : (k1_tarski(X0) = k6_enumset1(X0,X0,X0,X0,X0,X0,X0,X0)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f32,f56])).
% 1.50/0.55  fof(f32,plain,(
% 1.50/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f11])).
% 1.50/0.55  fof(f11,axiom,(
% 1.50/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.50/0.55  fof(f50,plain,(
% 1.50/0.55    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))) )),
% 1.50/0.55    inference(cnf_transformation,[],[f9])).
% 1.50/0.55  fof(f9,axiom,(
% 1.50/0.55    ! [X0,X1,X2,X3,X4,X5,X6] : k5_enumset1(X0,X1,X2,X3,X4,X5,X6) = k2_xboole_0(k4_enumset1(X0,X1,X2,X3,X4,X5),k1_tarski(X6))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).
% 1.50/0.55  fof(f150,plain,(
% 1.50/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl3_3),
% 1.50/0.55    inference(avatar_component_clause,[],[f148])).
% 1.50/0.55  fof(f151,plain,(
% 1.50/0.55    spl3_3 | ~spl3_2),
% 1.50/0.55    inference(avatar_split_clause,[],[f146,f76,f148])).
% 1.50/0.55  fof(f76,plain,(
% 1.50/0.55    spl3_2 <=> k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))),
% 1.50/0.55    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.50/0.55  fof(f146,plain,(
% 1.50/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl3_2),
% 1.50/0.55    inference(forward_demodulation,[],[f145,f36])).
% 1.50/0.55  fof(f36,plain,(
% 1.50/0.55    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f1])).
% 1.50/0.55  fof(f1,axiom,(
% 1.50/0.55    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 1.50/0.55  fof(f145,plain,(
% 1.50/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(sK2,sK2,sK2,sK2,sK2,sK2,k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1)))) | ~spl3_2),
% 1.50/0.55    inference(forward_demodulation,[],[f78,f65])).
% 1.50/0.55  fof(f65,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (k6_enumset1(X0,X0,X0,X0,X0,X0,X1,X2) = k6_enumset1(X2,X2,X2,X2,X2,X2,X1,X0)) )),
% 1.50/0.55    inference(definition_unfolding,[],[f40,f55,f55])).
% 1.50/0.55  fof(f40,plain,(
% 1.50/0.55    ( ! [X2,X0,X1] : (k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)) )),
% 1.50/0.55    inference(cnf_transformation,[],[f8])).
% 1.50/0.55  fof(f8,axiom,(
% 1.50/0.55    ! [X0,X1,X2] : k1_enumset1(X0,X1,X2) = k1_enumset1(X2,X1,X0)),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).
% 1.50/0.55  fof(f78,plain,(
% 1.50/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2))) | ~spl3_2),
% 1.50/0.55    inference(avatar_component_clause,[],[f76])).
% 1.50/0.55  fof(f79,plain,(
% 1.50/0.55    spl3_2),
% 1.50/0.55    inference(avatar_split_clause,[],[f61,f76])).
% 1.50/0.55  fof(f61,plain,(
% 1.50/0.55    k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1) = k5_xboole_0(k5_xboole_0(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2),k3_tarski(k6_enumset1(k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),k6_enumset1(sK0,sK0,sK0,sK0,sK0,sK0,sK0,sK1),sK2)))),
% 1.50/0.55    inference(definition_unfolding,[],[f29,f56,f58,f56])).
% 1.50/0.55  fof(f29,plain,(
% 1.50/0.55    k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  fof(f26,plain,(
% 1.50/0.55    ~r2_hidden(sK0,sK2) & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 1.50/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f25])).
% 1.50/0.55  fof(f25,plain,(
% 1.50/0.55    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2)) => (~r2_hidden(sK0,sK2) & k2_tarski(sK0,sK1) = k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 1.50/0.55    introduced(choice_axiom,[])).
% 1.50/0.55  fof(f24,plain,(
% 1.50/0.55    ? [X0,X1,X2] : (~r2_hidden(X0,X2) & k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2))),
% 1.50/0.55    inference(ennf_transformation,[],[f21])).
% 1.50/0.55  fof(f21,negated_conjecture,(
% 1.50/0.55    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 1.50/0.55    inference(negated_conjecture,[],[f20])).
% 1.50/0.55  fof(f20,conjecture,(
% 1.50/0.55    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k3_xboole_0(k2_tarski(X0,X1),X2) => r2_hidden(X0,X2))),
% 1.50/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_zfmisc_1)).
% 1.50/0.55  fof(f74,plain,(
% 1.50/0.55    ~spl3_1),
% 1.50/0.55    inference(avatar_split_clause,[],[f30,f71])).
% 1.50/0.55  fof(f30,plain,(
% 1.50/0.55    ~r2_hidden(sK0,sK2)),
% 1.50/0.55    inference(cnf_transformation,[],[f26])).
% 1.50/0.55  % SZS output end Proof for theBenchmark
% 1.50/0.55  % (2984)------------------------------
% 1.50/0.55  % (2984)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.55  % (2984)Termination reason: Refutation
% 1.50/0.55  
% 1.50/0.55  % (2984)Memory used [KB]: 6908
% 1.50/0.55  % (2984)Time elapsed: 0.101 s
% 1.50/0.55  % (2984)------------------------------
% 1.50/0.55  % (2984)------------------------------
% 1.50/0.55  % (2977)Success in time 0.194 s
%------------------------------------------------------------------------------
