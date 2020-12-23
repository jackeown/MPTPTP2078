%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:20 EST 2020

% Result     : Theorem 2.72s
% Output     : Refutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :  240 ( 754 expanded)
%              Number of leaves         :   42 ( 300 expanded)
%              Depth                    :    9
%              Number of atoms          :  503 (1406 expanded)
%              Number of equality atoms :   52 ( 265 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f660,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f83,f84,f105,f176,f178,f426,f434,f446,f450,f451,f454,f455,f469,f471,f478,f479,f481,f494,f495,f502,f515,f536,f537,f542,f547,f552,f553,f554,f556,f561,f566,f568,f579,f584,f590,f592,f596,f616,f618,f627,f632,f633,f634,f639,f644,f649,f650,f652,f653,f654,f655,f656,f659])).

fof(f659,plain,
    ( ~ spl3_4
    | spl3_6 ),
    inference(avatar_contradiction_clause,[],[f658])).

fof(f658,plain,
    ( $false
    | ~ spl3_4
    | spl3_6 ),
    inference(subsumption_resolution,[],[f657,f146])).

fof(f146,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f56,f68])).

fof(f68,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f657,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | ~ spl3_4
    | spl3_6 ),
    inference(forward_demodulation,[],[f421,f103])).

fof(f103,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl3_4
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f421,plain,
    ( ~ r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl3_6 ),
    inference(avatar_component_clause,[],[f419])).

fof(f419,plain,
    ( spl3_6
  <=> r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f656,plain,
    ( spl3_16
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f597,f544,f539])).

fof(f539,plain,
    ( spl3_16
  <=> r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f544,plain,
    ( spl3_17
  <=> r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f597,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ spl3_17 ),
    inference(resolution,[],[f546,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f546,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f544])).

fof(f655,plain,
    ( ~ spl3_3
    | spl3_13 ),
    inference(avatar_split_clause,[],[f503,f499,f80])).

fof(f80,plain,
    ( spl3_3
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f499,plain,
    ( spl3_13
  <=> r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f503,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_13 ),
    inference(resolution,[],[f501,f259])).

fof(f259,plain,(
    ! [X6,X8,X7] :
      ( r2_hidden(X6,k3_xboole_0(X7,k2_tarski(X6,X8)))
      | ~ r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f43,f111])).

fof(f111,plain,(
    ! [X4,X2,X3] : ~ r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k2_tarski(X2,X4)))) ),
    inference(resolution,[],[f39,f85])).

fof(f85,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0))) ),
    inference(resolution,[],[f66,f49])).

fof(f66,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1) ),
    inference(definition_unfolding,[],[f46,f45])).

fof(f45,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f46,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | ~ r2_hidden(X0,X1)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f501,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f499])).

fof(f654,plain,
    ( ~ spl3_3
    | spl3_13 ),
    inference(avatar_split_clause,[],[f504,f499,f80])).

fof(f504,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_13 ),
    inference(resolution,[],[f501,f260])).

fof(f260,plain,(
    ! [X10,X11,X9] :
      ( r2_hidden(X9,k3_xboole_0(X10,k2_tarski(X11,X9)))
      | ~ r2_hidden(X9,X10) ) ),
    inference(resolution,[],[f43,f161])).

fof(f161,plain,(
    ! [X4,X2,X3] : ~ r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k2_tarski(X4,X2)))) ),
    inference(resolution,[],[f112,f85])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X1,X0),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f39,f48])).

fof(f48,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f653,plain,
    ( ~ spl3_3
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f646,f636,f80])).

fof(f636,plain,
    ( spl3_26
  <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f646,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_26 ),
    inference(resolution,[],[f638,f39])).

fof(f638,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f636])).

fof(f652,plain,
    ( spl3_2
    | spl3_15 ),
    inference(avatar_split_clause,[],[f651,f533,f75])).

fof(f75,plain,
    ( spl3_2
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f533,plain,
    ( spl3_15
  <=> r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f651,plain,
    ( r2_hidden(sK1,sK2)
    | spl3_15 ),
    inference(subsumption_resolution,[],[f586,f146])).

fof(f586,plain,
    ( r2_hidden(sK1,sK2)
    | ~ r2_hidden(sK1,k2_tarski(sK1,sK1))
    | spl3_15 ),
    inference(resolution,[],[f535,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f535,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | spl3_15 ),
    inference(avatar_component_clause,[],[f533])).

fof(f650,plain,
    ( ~ spl3_2
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f645,f636,f75])).

fof(f645,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_26 ),
    inference(resolution,[],[f638,f112])).

fof(f649,plain,
    ( ~ spl3_2
    | ~ spl3_26 ),
    inference(avatar_contradiction_clause,[],[f648])).

fof(f648,plain,
    ( $false
    | ~ spl3_2
    | ~ spl3_26 ),
    inference(subsumption_resolution,[],[f645,f76])).

fof(f76,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f644,plain,
    ( spl3_27
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f601,f102,f641])).

fof(f641,plain,
    ( spl3_27
  <=> r1_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f601,plain,
    ( r1_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl3_4 ),
    inference(superposition,[],[f108,f103])).

fof(f108,plain,(
    ! [X2,X1] : r1_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1))) ),
    inference(superposition,[],[f85,f54])).

fof(f54,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f639,plain,
    ( spl3_26
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f602,f102,f636])).

fof(f602,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_4 ),
    inference(superposition,[],[f97,f103])).

fof(f97,plain,(
    ! [X6,X5] : r1_xboole_0(k5_xboole_0(X5,k3_xboole_0(X6,X5)),X6) ),
    inference(superposition,[],[f66,f54])).

fof(f634,plain,
    ( spl3_25
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f608,f102,f629])).

fof(f629,plain,
    ( spl3_25
  <=> r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f608,plain,
    ( r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))
    | ~ spl3_4 ),
    inference(superposition,[],[f50,f103])).

fof(f50,plain,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

fof(f633,plain,
    ( spl3_24
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f610,f102,f624])).

fof(f624,plain,
    ( spl3_24
  <=> r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f610,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | ~ spl3_4 ),
    inference(superposition,[],[f90,f103])).

fof(f90,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1)) ),
    inference(resolution,[],[f50,f49])).

fof(f632,plain,
    ( spl3_25
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f619,f102,f629])).

fof(f619,plain,
    ( r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f611,f54])).

fof(f611,plain,
    ( r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ spl3_4 ),
    inference(superposition,[],[f92,f103])).

fof(f92,plain,(
    ! [X8,X7] : r1_xboole_0(k3_xboole_0(X7,X8),k5_xboole_0(X8,X7)) ),
    inference(superposition,[],[f50,f53])).

fof(f53,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f627,plain,
    ( spl3_24
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f620,f102,f624])).

fof(f620,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | ~ spl3_4 ),
    inference(forward_demodulation,[],[f612,f54])).

fof(f612,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)))
    | ~ spl3_4 ),
    inference(superposition,[],[f115,f103])).

fof(f115,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1)) ),
    inference(superposition,[],[f90,f53])).

fof(f618,plain,
    ( ~ spl3_4
    | spl3_5 ),
    inference(avatar_contradiction_clause,[],[f617])).

fof(f617,plain,
    ( $false
    | ~ spl3_4
    | spl3_5 ),
    inference(subsumption_resolution,[],[f600,f68])).

fof(f600,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1))
    | ~ spl3_4
    | spl3_5 ),
    inference(backward_demodulation,[],[f175,f103])).

fof(f175,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl3_5 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl3_5
  <=> r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f616,plain,
    ( ~ spl3_4
    | spl3_7 ),
    inference(avatar_contradiction_clause,[],[f615])).

fof(f615,plain,
    ( $false
    | ~ spl3_4
    | spl3_7 ),
    inference(subsumption_resolution,[],[f598,f149])).

fof(f149,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(superposition,[],[f146,f48])).

fof(f598,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | ~ spl3_4
    | spl3_7 ),
    inference(backward_demodulation,[],[f425,f103])).

fof(f425,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f423])).

fof(f423,plain,
    ( spl3_7
  <=> r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f596,plain,
    ( spl3_17
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f595,f539,f544])).

fof(f595,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | ~ spl3_16 ),
    inference(resolution,[],[f541,f49])).

fof(f541,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f539])).

fof(f592,plain,
    ( ~ spl3_22
    | ~ spl3_18
    | spl3_21 ),
    inference(avatar_split_clause,[],[f591,f572,f549,f576])).

fof(f576,plain,
    ( spl3_22
  <=> r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f549,plain,
    ( spl3_18
  <=> r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f572,plain,
    ( spl3_21
  <=> sK2 = k5_xboole_0(sK2,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f591,plain,
    ( ~ r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ spl3_18
    | spl3_21 ),
    inference(subsumption_resolution,[],[f588,f551])).

fof(f551,plain,
    ( r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2)
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f549])).

fof(f588,plain,
    ( ~ r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2)
    | spl3_21 ),
    inference(extensionality_resolution,[],[f61,f573])).

fof(f573,plain,
    ( sK2 != k5_xboole_0(sK2,k2_tarski(sK1,sK1))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f572])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f7])).

fof(f590,plain,
    ( ~ spl3_22
    | ~ spl3_18
    | spl3_21 ),
    inference(avatar_split_clause,[],[f589,f572,f549,f576])).

fof(f589,plain,
    ( ~ r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ spl3_18
    | spl3_21 ),
    inference(subsumption_resolution,[],[f587,f551])).

fof(f587,plain,
    ( ~ r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2)
    | ~ r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | spl3_21 ),
    inference(extensionality_resolution,[],[f61,f573])).

fof(f584,plain,
    ( spl3_23
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f570,f549,f581])).

fof(f581,plain,
    ( spl3_23
  <=> k5_xboole_0(sK2,k2_tarski(sK1,sK1)) = k3_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f570,plain,
    ( k5_xboole_0(sK2,k2_tarski(sK1,sK1)) = k3_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2)
    | ~ spl3_18 ),
    inference(resolution,[],[f551,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f579,plain,
    ( spl3_21
    | ~ spl3_22
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f569,f549,f576,f572])).

fof(f569,plain,
    ( ~ r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | sK2 = k5_xboole_0(sK2,k2_tarski(sK1,sK1))
    | ~ spl3_18 ),
    inference(resolution,[],[f551,f61])).

fof(f568,plain,
    ( spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f567,f512,f544])).

fof(f512,plain,
    ( spl3_14
  <=> k2_tarski(sK1,sK1) = k3_xboole_0(sK2,k2_tarski(sK1,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f567,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f531,f53])).

fof(f531,plain,
    ( r1_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),sK2),k2_tarski(sK1,sK1))
    | ~ spl3_14 ),
    inference(superposition,[],[f115,f514])).

fof(f514,plain,
    ( k2_tarski(sK1,sK1) = k3_xboole_0(sK2,k2_tarski(sK1,sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f512])).

fof(f566,plain,
    ( spl3_20
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f530,f512,f563])).

fof(f563,plain,
    ( spl3_20
  <=> r1_xboole_0(sK2,k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f530,plain,
    ( r1_xboole_0(sK2,k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))
    | ~ spl3_14 ),
    inference(superposition,[],[f108,f514])).

fof(f561,plain,
    ( spl3_19
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f529,f512,f558])).

fof(f558,plain,
    ( spl3_19
  <=> r1_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f529,plain,
    ( r1_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)),sK2)
    | ~ spl3_14 ),
    inference(superposition,[],[f97,f514])).

fof(f556,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f555,f512,f539])).

fof(f555,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f527,f53])).

fof(f527,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),sK2))
    | ~ spl3_14 ),
    inference(superposition,[],[f92,f514])).

fof(f554,plain,
    ( spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f526,f512,f544])).

fof(f526,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | ~ spl3_14 ),
    inference(superposition,[],[f90,f514])).

fof(f553,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f525,f512,f539])).

fof(f525,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ spl3_14 ),
    inference(superposition,[],[f85,f514])).

fof(f552,plain,
    ( spl3_18
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f524,f512,f549])).

fof(f524,plain,
    ( r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2)
    | ~ spl3_14 ),
    inference(superposition,[],[f67,f514])).

fof(f67,plain,(
    ! [X0,X1] : r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f47,f45])).

fof(f47,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f547,plain,
    ( spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f523,f512,f544])).

fof(f523,plain,
    ( r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))
    | ~ spl3_14 ),
    inference(superposition,[],[f66,f514])).

fof(f542,plain,
    ( spl3_16
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f522,f512,f539])).

fof(f522,plain,
    ( r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ spl3_14 ),
    inference(superposition,[],[f50,f514])).

fof(f537,plain,
    ( ~ spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f521,f512,f533])).

fof(f521,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ spl3_14 ),
    inference(superposition,[],[f111,f514])).

fof(f536,plain,
    ( ~ spl3_15
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f520,f512,f533])).

fof(f520,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))
    | ~ spl3_14 ),
    inference(superposition,[],[f161,f514])).

fof(f515,plain,
    ( spl3_14
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f510,f75,f512])).

fof(f510,plain,
    ( k2_tarski(sK1,sK1) = k3_xboole_0(sK2,k2_tarski(sK1,sK1))
    | ~ spl3_2 ),
    inference(resolution,[],[f483,f76])).

fof(f483,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k2_tarski(X0,sK1) = k3_xboole_0(sK2,k2_tarski(X0,sK1)) )
    | ~ spl3_2 ),
    inference(forward_demodulation,[],[f482,f54])).

fof(f482,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k2_tarski(X0,sK1) = k3_xboole_0(k2_tarski(X0,sK1),sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f76,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1)
      | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X1)
        & r2_hidden(X0,X1) )
     => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

fof(f502,plain,
    ( ~ spl3_13
    | spl3_11 ),
    inference(avatar_split_clause,[],[f497,f487,f499])).

fof(f487,plain,
    ( spl3_11
  <=> r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(sK2,k2_tarski(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f497,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | spl3_11 ),
    inference(duplicate_literal_removal,[],[f496])).

fof(f496,plain,
    ( ~ r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | ~ r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | spl3_11 ),
    inference(resolution,[],[f489,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f489,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f487])).

fof(f495,plain,
    ( ~ spl3_12
    | ~ spl3_11
    | spl3_10 ),
    inference(avatar_split_clause,[],[f485,f466,f487,f491])).

fof(f491,plain,
    ( spl3_12
  <=> r1_tarski(k3_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f466,plain,
    ( spl3_10
  <=> k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f485,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | ~ r1_tarski(k3_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | spl3_10 ),
    inference(extensionality_resolution,[],[f61,f467])).

fof(f467,plain,
    ( k2_tarski(sK0,sK0) != k3_xboole_0(sK2,k2_tarski(sK0,sK0))
    | spl3_10 ),
    inference(avatar_component_clause,[],[f466])).

fof(f494,plain,
    ( ~ spl3_11
    | ~ spl3_12
    | spl3_10 ),
    inference(avatar_split_clause,[],[f484,f466,f491,f487])).

fof(f484,plain,
    ( ~ r1_tarski(k3_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))
    | ~ r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(sK2,k2_tarski(sK0,sK0)))
    | spl3_10 ),
    inference(extensionality_resolution,[],[f61,f467])).

fof(f481,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f480,f71,f102])).

fof(f71,plain,
    ( spl3_1
  <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f480,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f73,f54])).

fof(f73,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f479,plain,
    ( spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f475,f443,f75])).

fof(f443,plain,
    ( spl3_9
  <=> r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f475,plain,
    ( r2_hidden(sK1,sK2)
    | ~ spl3_9 ),
    inference(resolution,[],[f445,f246])).

fof(f246,plain,(
    ! [X10,X11,X9] :
      ( ~ r2_hidden(X9,k3_xboole_0(X10,k2_tarski(X11,X9)))
      | r2_hidden(X9,X10) ) ),
    inference(resolution,[],[f42,f161])).

fof(f445,plain,
    ( r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f443])).

fof(f478,plain,
    ( spl3_2
    | ~ spl3_9 ),
    inference(avatar_contradiction_clause,[],[f477])).

fof(f477,plain,
    ( $false
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f475,f77])).

fof(f77,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f471,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f470,f71,f102])).

fof(f470,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_1 ),
    inference(forward_demodulation,[],[f72,f54])).

fof(f72,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f469,plain,
    ( spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f464,f80,f466])).

fof(f464,plain,
    ( k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f457,f81])).

fof(f81,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f457,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k2_tarski(X0,sK0) = k3_xboole_0(sK2,k2_tarski(X0,sK0)) )
    | ~ spl3_3 ),
    inference(forward_demodulation,[],[f456,f54])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK2)
        | k2_tarski(X0,sK0) = k3_xboole_0(k2_tarski(X0,sK0),sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f81,f44])).

fof(f455,plain,
    ( spl3_4
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f452,f71,f102])).

fof(f452,plain,
    ( k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f73,f54])).

fof(f454,plain,
    ( ~ spl3_1
    | spl3_4 ),
    inference(avatar_contradiction_clause,[],[f453])).

fof(f453,plain,
    ( $false
    | ~ spl3_1
    | spl3_4 ),
    inference(subsumption_resolution,[],[f452,f104])).

fof(f104,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f102])).

fof(f451,plain,
    ( spl3_3
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f447,f431,f80])).

fof(f431,plain,
    ( spl3_8
  <=> r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f447,plain,
    ( r2_hidden(sK0,sK2)
    | ~ spl3_8 ),
    inference(resolution,[],[f433,f245])).

fof(f245,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X6,k3_xboole_0(X7,k2_tarski(X6,X8)))
      | r2_hidden(X6,X7) ) ),
    inference(resolution,[],[f42,f111])).

fof(f433,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f431])).

fof(f450,plain,
    ( spl3_3
    | ~ spl3_8 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | spl3_3
    | ~ spl3_8 ),
    inference(subsumption_resolution,[],[f447,f82])).

fof(f82,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f446,plain,
    ( spl3_9
    | spl3_7 ),
    inference(avatar_split_clause,[],[f441,f423,f443])).

fof(f441,plain,
    ( r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_7 ),
    inference(subsumption_resolution,[],[f439,f149])).

fof(f439,plain,
    ( ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_7 ),
    inference(resolution,[],[f425,f43])).

fof(f434,plain,
    ( spl3_8
    | spl3_6 ),
    inference(avatar_split_clause,[],[f429,f419,f431])).

fof(f429,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_6 ),
    inference(subsumption_resolution,[],[f427,f146])).

fof(f427,plain,
    ( ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_6 ),
    inference(resolution,[],[f421,f43])).

fof(f426,plain,
    ( ~ spl3_6
    | ~ spl3_7
    | spl3_5 ),
    inference(avatar_split_clause,[],[f412,f173,f423,f419])).

fof(f412,plain,
    ( ~ r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | ~ r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl3_5 ),
    inference(resolution,[],[f58,f175])).

fof(f178,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f177,f102,f173])).

fof(f177,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl3_4 ),
    inference(subsumption_resolution,[],[f166,f96])).

fof(f96,plain,(
    ! [X4,X3] : r1_tarski(k5_xboole_0(X3,k3_xboole_0(X4,X3)),X3) ),
    inference(superposition,[],[f67,f54])).

fof(f166,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | ~ r1_tarski(k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))
    | spl3_4 ),
    inference(extensionality_resolution,[],[f61,f104])).

fof(f176,plain,
    ( ~ spl3_5
    | spl3_4 ),
    inference(avatar_split_clause,[],[f171,f102,f173])).

fof(f171,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl3_4 ),
    inference(subsumption_resolution,[],[f165,f96])).

fof(f165,plain,
    ( ~ r1_tarski(k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))
    | ~ r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))
    | spl3_4 ),
    inference(extensionality_resolution,[],[f61,f104])).

fof(f105,plain,
    ( ~ spl3_4
    | spl3_1 ),
    inference(avatar_split_clause,[],[f94,f71,f102])).

fof(f94,plain,
    ( k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_1 ),
    inference(backward_demodulation,[],[f72,f54])).

fof(f84,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f65,f80,f75,f71])).

fof(f65,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f36,f45])).

fof(f36,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f83,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f64,f80,f71])).

fof(f64,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f37,f45])).

fof(f37,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f78,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f63,f75,f71])).

fof(f63,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    inference(definition_unfolding,[],[f38,f45])).

fof(f38,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:02:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (300)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.51  % (32764)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (307)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.51  % (307)Refutation not found, incomplete strategy% (307)------------------------------
% 0.22/0.51  % (307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (307)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (307)Memory used [KB]: 6140
% 0.22/0.51  % (307)Time elapsed: 0.090 s
% 0.22/0.51  % (307)------------------------------
% 0.22/0.51  % (307)------------------------------
% 0.22/0.52  % (302)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.53  % (315)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.53  % (306)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.53  % (306)Refutation not found, incomplete strategy% (306)------------------------------
% 0.22/0.53  % (306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (306)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (306)Memory used [KB]: 10746
% 0.22/0.53  % (306)Time elapsed: 0.107 s
% 0.22/0.53  % (306)------------------------------
% 0.22/0.53  % (306)------------------------------
% 0.22/0.53  % (308)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.38/0.54  % (324)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.38/0.54  % (304)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.54  % (314)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.38/0.54  % (316)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.54  % (303)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.54  % (309)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.38/0.55  % (324)Refutation not found, incomplete strategy% (324)------------------------------
% 1.38/0.55  % (324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (324)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.55  
% 1.38/0.55  % (324)Memory used [KB]: 10746
% 1.38/0.55  % (324)Time elapsed: 0.119 s
% 1.38/0.55  % (324)------------------------------
% 1.38/0.55  % (324)------------------------------
% 1.38/0.55  % (32766)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.38/0.55  % (301)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.38/0.55  % (32765)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.38/0.55  % (305)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.51/0.56  % (325)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.51/0.56  % (325)Refutation not found, incomplete strategy% (325)------------------------------
% 1.51/0.56  % (325)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (325)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (325)Memory used [KB]: 1663
% 1.51/0.56  % (325)Time elapsed: 0.104 s
% 1.51/0.56  % (325)------------------------------
% 1.51/0.56  % (325)------------------------------
% 1.51/0.56  % (321)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.51/0.56  % (32767)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.51/0.56  % (322)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.51/0.56  % (322)Refutation not found, incomplete strategy% (322)------------------------------
% 1.51/0.56  % (322)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (322)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (322)Memory used [KB]: 6268
% 1.51/0.56  % (322)Time elapsed: 0.124 s
% 1.51/0.56  % (322)------------------------------
% 1.51/0.56  % (322)------------------------------
% 1.51/0.56  % (313)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.51/0.56  % (317)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.51/0.56  % (313)Refutation not found, incomplete strategy% (313)------------------------------
% 1.51/0.56  % (313)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (313)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (313)Memory used [KB]: 1663
% 1.51/0.56  % (313)Time elapsed: 0.151 s
% 1.51/0.56  % (313)------------------------------
% 1.51/0.56  % (313)------------------------------
% 1.51/0.56  % (312)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.51/0.56  % (312)Refutation not found, incomplete strategy% (312)------------------------------
% 1.51/0.56  % (312)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (312)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.56  
% 1.51/0.56  % (312)Memory used [KB]: 10618
% 1.51/0.56  % (312)Time elapsed: 0.150 s
% 1.51/0.56  % (312)------------------------------
% 1.51/0.56  % (312)------------------------------
% 1.51/0.56  % (320)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.51/0.57  % (319)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.51/0.57  % (318)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.51/0.57  % (323)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.51/0.57  % (32765)Refutation not found, incomplete strategy% (32765)------------------------------
% 1.51/0.57  % (32765)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.57  % (32765)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.57  
% 1.51/0.57  % (32765)Memory used [KB]: 1663
% 1.51/0.57  % (32765)Time elapsed: 0.156 s
% 1.51/0.57  % (32765)------------------------------
% 1.51/0.57  % (32765)------------------------------
% 1.51/0.58  % (311)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.51/0.58  % (310)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.51/0.58  % (310)Refutation not found, incomplete strategy% (310)------------------------------
% 1.51/0.58  % (310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.58  % (310)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.58  
% 1.51/0.58  % (310)Memory used [KB]: 1663
% 1.51/0.58  % (310)Time elapsed: 0.171 s
% 1.51/0.58  % (310)------------------------------
% 1.51/0.58  % (310)------------------------------
% 2.00/0.65  % (326)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.00/0.67  % (327)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.20/0.68  % (328)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.20/0.68  % (328)Refutation not found, incomplete strategy% (328)------------------------------
% 2.20/0.68  % (328)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.68  % (328)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.68  
% 2.20/0.68  % (328)Memory used [KB]: 6140
% 2.20/0.68  % (328)Time elapsed: 0.006 s
% 2.20/0.68  % (328)------------------------------
% 2.20/0.68  % (328)------------------------------
% 2.20/0.69  % (32767)Refutation not found, incomplete strategy% (32767)------------------------------
% 2.20/0.69  % (32767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.69  % (32767)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.69  
% 2.20/0.69  % (32767)Memory used [KB]: 6140
% 2.20/0.69  % (32767)Time elapsed: 0.266 s
% 2.20/0.69  % (32767)------------------------------
% 2.20/0.69  % (32767)------------------------------
% 2.20/0.69  % (332)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.20/0.70  % (329)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.20/0.71  % (333)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.20/0.71  % (330)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.20/0.72  % (330)Refutation not found, incomplete strategy% (330)------------------------------
% 2.20/0.72  % (330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.20/0.72  % (330)Termination reason: Refutation not found, incomplete strategy
% 2.20/0.72  
% 2.20/0.72  % (330)Memory used [KB]: 10618
% 2.20/0.72  % (330)Time elapsed: 0.117 s
% 2.20/0.72  % (330)------------------------------
% 2.20/0.72  % (330)------------------------------
% 2.20/0.73  % (331)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.72/0.74  % (32764)Refutation found. Thanks to Tanya!
% 2.72/0.74  % SZS status Theorem for theBenchmark
% 2.72/0.74  % SZS output start Proof for theBenchmark
% 2.72/0.74  fof(f660,plain,(
% 2.72/0.74    $false),
% 2.72/0.74    inference(avatar_sat_refutation,[],[f78,f83,f84,f105,f176,f178,f426,f434,f446,f450,f451,f454,f455,f469,f471,f478,f479,f481,f494,f495,f502,f515,f536,f537,f542,f547,f552,f553,f554,f556,f561,f566,f568,f579,f584,f590,f592,f596,f616,f618,f627,f632,f633,f634,f639,f644,f649,f650,f652,f653,f654,f655,f656,f659])).
% 2.72/0.74  fof(f659,plain,(
% 2.72/0.74    ~spl3_4 | spl3_6),
% 2.72/0.74    inference(avatar_contradiction_clause,[],[f658])).
% 2.72/0.74  fof(f658,plain,(
% 2.72/0.74    $false | (~spl3_4 | spl3_6)),
% 2.72/0.74    inference(subsumption_resolution,[],[f657,f146])).
% 2.72/0.74  fof(f146,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.72/0.74    inference(resolution,[],[f56,f68])).
% 2.72/0.74  fof(f68,plain,(
% 2.72/0.74    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.72/0.74    inference(equality_resolution,[],[f60])).
% 2.72/0.74  fof(f60,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.72/0.74    inference(cnf_transformation,[],[f7])).
% 2.72/0.74  fof(f7,axiom,(
% 2.72/0.74    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.72/0.74  fof(f56,plain,(
% 2.72/0.74    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f23])).
% 2.72/0.74  fof(f23,axiom,(
% 2.72/0.74    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.72/0.74  fof(f657,plain,(
% 2.72/0.74    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | (~spl3_4 | spl3_6)),
% 2.72/0.74    inference(forward_demodulation,[],[f421,f103])).
% 2.72/0.74  fof(f103,plain,(
% 2.72/0.74    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_4),
% 2.72/0.74    inference(avatar_component_clause,[],[f102])).
% 2.72/0.74  fof(f102,plain,(
% 2.72/0.74    spl3_4 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.72/0.74  fof(f421,plain,(
% 2.72/0.74    ~r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl3_6),
% 2.72/0.74    inference(avatar_component_clause,[],[f419])).
% 2.72/0.74  fof(f419,plain,(
% 2.72/0.74    spl3_6 <=> r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.72/0.74  fof(f656,plain,(
% 2.72/0.74    spl3_16 | ~spl3_17),
% 2.72/0.74    inference(avatar_split_clause,[],[f597,f544,f539])).
% 2.72/0.74  fof(f539,plain,(
% 2.72/0.74    spl3_16 <=> r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1)))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.72/0.74  fof(f544,plain,(
% 2.72/0.74    spl3_17 <=> r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 2.72/0.74  fof(f597,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | ~spl3_17),
% 2.72/0.74    inference(resolution,[],[f546,f49])).
% 2.72/0.74  fof(f49,plain,(
% 2.72/0.74    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f34])).
% 2.72/0.74  fof(f34,plain,(
% 2.72/0.74    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.72/0.74    inference(ennf_transformation,[],[f5])).
% 2.72/0.74  fof(f5,axiom,(
% 2.72/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.72/0.74  fof(f546,plain,(
% 2.72/0.74    r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | ~spl3_17),
% 2.72/0.74    inference(avatar_component_clause,[],[f544])).
% 2.72/0.74  fof(f655,plain,(
% 2.72/0.74    ~spl3_3 | spl3_13),
% 2.72/0.74    inference(avatar_split_clause,[],[f503,f499,f80])).
% 2.72/0.74  fof(f80,plain,(
% 2.72/0.74    spl3_3 <=> r2_hidden(sK0,sK2)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.72/0.74  fof(f499,plain,(
% 2.72/0.74    spl3_13 <=> r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0)))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.72/0.74  fof(f503,plain,(
% 2.72/0.74    ~r2_hidden(sK0,sK2) | spl3_13),
% 2.72/0.74    inference(resolution,[],[f501,f259])).
% 2.72/0.74  fof(f259,plain,(
% 2.72/0.74    ( ! [X6,X8,X7] : (r2_hidden(X6,k3_xboole_0(X7,k2_tarski(X6,X8))) | ~r2_hidden(X6,X7)) )),
% 2.72/0.74    inference(resolution,[],[f43,f111])).
% 2.72/0.74  fof(f111,plain,(
% 2.72/0.74    ( ! [X4,X2,X3] : (~r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k2_tarski(X2,X4))))) )),
% 2.72/0.74    inference(resolution,[],[f39,f85])).
% 2.72/0.74  fof(f85,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r1_xboole_0(X0,k5_xboole_0(X1,k3_xboole_0(X1,X0)))) )),
% 2.72/0.74    inference(resolution,[],[f66,f49])).
% 2.72/0.74  fof(f66,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X1)) )),
% 2.72/0.74    inference(definition_unfolding,[],[f46,f45])).
% 2.72/0.74  fof(f45,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.72/0.74    inference(cnf_transformation,[],[f9])).
% 2.72/0.74  fof(f9,axiom,(
% 2.72/0.74    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.72/0.74  fof(f46,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f14])).
% 2.72/0.74  fof(f14,axiom,(
% 2.72/0.74    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.72/0.74  fof(f39,plain,(
% 2.72/0.74    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f30])).
% 2.72/0.74  fof(f30,plain,(
% 2.72/0.74    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.72/0.74    inference(ennf_transformation,[],[f25])).
% 2.72/0.74  fof(f25,axiom,(
% 2.72/0.74    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 2.72/0.74  fof(f43,plain,(
% 2.72/0.74    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | ~r2_hidden(X0,X1) | r2_hidden(X0,X2)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f31])).
% 2.72/0.74  fof(f31,plain,(
% 2.72/0.74    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.72/0.74    inference(ennf_transformation,[],[f6])).
% 2.72/0.74  fof(f6,axiom,(
% 2.72/0.74    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.72/0.74  fof(f501,plain,(
% 2.72/0.74    ~r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0))) | spl3_13),
% 2.72/0.74    inference(avatar_component_clause,[],[f499])).
% 2.72/0.74  fof(f654,plain,(
% 2.72/0.74    ~spl3_3 | spl3_13),
% 2.72/0.74    inference(avatar_split_clause,[],[f504,f499,f80])).
% 2.72/0.74  fof(f504,plain,(
% 2.72/0.74    ~r2_hidden(sK0,sK2) | spl3_13),
% 2.72/0.74    inference(resolution,[],[f501,f260])).
% 2.72/0.74  fof(f260,plain,(
% 2.72/0.74    ( ! [X10,X11,X9] : (r2_hidden(X9,k3_xboole_0(X10,k2_tarski(X11,X9))) | ~r2_hidden(X9,X10)) )),
% 2.72/0.74    inference(resolution,[],[f43,f161])).
% 2.72/0.74  fof(f161,plain,(
% 2.72/0.74    ( ! [X4,X2,X3] : (~r2_hidden(X2,k5_xboole_0(X3,k3_xboole_0(X3,k2_tarski(X4,X2))))) )),
% 2.72/0.74    inference(resolution,[],[f112,f85])).
% 2.72/0.74  fof(f112,plain,(
% 2.72/0.74    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X1,X0),X2) | ~r2_hidden(X0,X2)) )),
% 2.72/0.74    inference(superposition,[],[f39,f48])).
% 2.72/0.74  fof(f48,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f16])).
% 2.72/0.74  fof(f16,axiom,(
% 2.72/0.74    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.72/0.74  fof(f653,plain,(
% 2.72/0.74    ~spl3_3 | ~spl3_26),
% 2.72/0.74    inference(avatar_split_clause,[],[f646,f636,f80])).
% 2.72/0.74  fof(f636,plain,(
% 2.72/0.74    spl3_26 <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 2.72/0.74  fof(f646,plain,(
% 2.72/0.74    ~r2_hidden(sK0,sK2) | ~spl3_26),
% 2.72/0.74    inference(resolution,[],[f638,f39])).
% 2.72/0.74  fof(f638,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_26),
% 2.72/0.74    inference(avatar_component_clause,[],[f636])).
% 2.72/0.74  fof(f652,plain,(
% 2.72/0.74    spl3_2 | spl3_15),
% 2.72/0.74    inference(avatar_split_clause,[],[f651,f533,f75])).
% 2.72/0.74  fof(f75,plain,(
% 2.72/0.74    spl3_2 <=> r2_hidden(sK1,sK2)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.72/0.74  fof(f533,plain,(
% 2.72/0.74    spl3_15 <=> r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.72/0.74  fof(f651,plain,(
% 2.72/0.74    r2_hidden(sK1,sK2) | spl3_15),
% 2.72/0.74    inference(subsumption_resolution,[],[f586,f146])).
% 2.72/0.74  fof(f586,plain,(
% 2.72/0.74    r2_hidden(sK1,sK2) | ~r2_hidden(sK1,k2_tarski(sK1,sK1)) | spl3_15),
% 2.72/0.74    inference(resolution,[],[f535,f42])).
% 2.72/0.74  fof(f42,plain,(
% 2.72/0.74    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f31])).
% 2.72/0.74  fof(f535,plain,(
% 2.72/0.74    ~r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | spl3_15),
% 2.72/0.74    inference(avatar_component_clause,[],[f533])).
% 2.72/0.74  fof(f650,plain,(
% 2.72/0.74    ~spl3_2 | ~spl3_26),
% 2.72/0.74    inference(avatar_split_clause,[],[f645,f636,f75])).
% 2.72/0.74  fof(f645,plain,(
% 2.72/0.74    ~r2_hidden(sK1,sK2) | ~spl3_26),
% 2.72/0.74    inference(resolution,[],[f638,f112])).
% 2.72/0.74  fof(f649,plain,(
% 2.72/0.74    ~spl3_2 | ~spl3_26),
% 2.72/0.74    inference(avatar_contradiction_clause,[],[f648])).
% 2.72/0.74  fof(f648,plain,(
% 2.72/0.74    $false | (~spl3_2 | ~spl3_26)),
% 2.72/0.74    inference(subsumption_resolution,[],[f645,f76])).
% 2.72/0.74  fof(f76,plain,(
% 2.72/0.74    r2_hidden(sK1,sK2) | ~spl3_2),
% 2.72/0.74    inference(avatar_component_clause,[],[f75])).
% 2.72/0.74  fof(f644,plain,(
% 2.72/0.74    spl3_27 | ~spl3_4),
% 2.72/0.74    inference(avatar_split_clause,[],[f601,f102,f641])).
% 2.72/0.74  fof(f641,plain,(
% 2.72/0.74    spl3_27 <=> r1_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 2.72/0.74  fof(f601,plain,(
% 2.72/0.74    r1_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl3_4),
% 2.72/0.74    inference(superposition,[],[f108,f103])).
% 2.72/0.74  fof(f108,plain,(
% 2.72/0.74    ( ! [X2,X1] : (r1_xboole_0(X2,k5_xboole_0(X1,k3_xboole_0(X2,X1)))) )),
% 2.72/0.74    inference(superposition,[],[f85,f54])).
% 2.72/0.74  fof(f54,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f1])).
% 2.72/0.74  fof(f1,axiom,(
% 2.72/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.72/0.74  fof(f639,plain,(
% 2.72/0.74    spl3_26 | ~spl3_4),
% 2.72/0.74    inference(avatar_split_clause,[],[f602,f102,f636])).
% 2.72/0.74  fof(f602,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_4),
% 2.72/0.74    inference(superposition,[],[f97,f103])).
% 2.72/0.74  fof(f97,plain,(
% 2.72/0.74    ( ! [X6,X5] : (r1_xboole_0(k5_xboole_0(X5,k3_xboole_0(X6,X5)),X6)) )),
% 2.72/0.74    inference(superposition,[],[f66,f54])).
% 2.72/0.74  fof(f634,plain,(
% 2.72/0.74    spl3_25 | ~spl3_4),
% 2.72/0.74    inference(avatar_split_clause,[],[f608,f102,f629])).
% 2.72/0.74  fof(f629,plain,(
% 2.72/0.74    spl3_25 <=> r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.72/0.74  fof(f608,plain,(
% 2.72/0.74    r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) | ~spl3_4),
% 2.72/0.74    inference(superposition,[],[f50,f103])).
% 2.72/0.74  fof(f50,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))) )),
% 2.72/0.74    inference(cnf_transformation,[],[f8])).
% 2.72/0.74  fof(f8,axiom,(
% 2.72/0.74    ! [X0,X1] : r1_xboole_0(k3_xboole_0(X0,X1),k5_xboole_0(X0,X1))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).
% 2.72/0.74  fof(f633,plain,(
% 2.72/0.74    spl3_24 | ~spl3_4),
% 2.72/0.74    inference(avatar_split_clause,[],[f610,f102,f624])).
% 2.72/0.74  fof(f624,plain,(
% 2.72/0.74    spl3_24 <=> r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.72/0.74  fof(f610,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | ~spl3_4),
% 2.72/0.74    inference(superposition,[],[f90,f103])).
% 2.72/0.74  fof(f90,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,X1),k3_xboole_0(X0,X1))) )),
% 2.72/0.74    inference(resolution,[],[f50,f49])).
% 2.72/0.74  fof(f632,plain,(
% 2.72/0.74    spl3_25 | ~spl3_4),
% 2.72/0.74    inference(avatar_split_clause,[],[f619,f102,f629])).
% 2.72/0.74  fof(f619,plain,(
% 2.72/0.74    r1_xboole_0(k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) | ~spl3_4),
% 2.72/0.74    inference(forward_demodulation,[],[f611,f54])).
% 2.72/0.74  fof(f611,plain,(
% 2.72/0.74    r1_xboole_0(k3_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | ~spl3_4),
% 2.72/0.74    inference(superposition,[],[f92,f103])).
% 2.72/0.74  fof(f92,plain,(
% 2.72/0.74    ( ! [X8,X7] : (r1_xboole_0(k3_xboole_0(X7,X8),k5_xboole_0(X8,X7))) )),
% 2.72/0.74    inference(superposition,[],[f50,f53])).
% 2.72/0.74  fof(f53,plain,(
% 2.72/0.74    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f2])).
% 2.72/0.74  fof(f2,axiom,(
% 2.72/0.74    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.72/0.74  fof(f627,plain,(
% 2.72/0.74    spl3_24 | ~spl3_4),
% 2.72/0.74    inference(avatar_split_clause,[],[f620,f102,f624])).
% 2.72/0.74  fof(f620,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | ~spl3_4),
% 2.72/0.74    inference(forward_demodulation,[],[f612,f54])).
% 2.72/0.74  fof(f612,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))) | ~spl3_4),
% 2.72/0.74    inference(superposition,[],[f115,f103])).
% 2.72/0.74  fof(f115,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X1,X0),k3_xboole_0(X0,X1))) )),
% 2.72/0.74    inference(superposition,[],[f90,f53])).
% 2.72/0.74  fof(f618,plain,(
% 2.72/0.74    ~spl3_4 | spl3_5),
% 2.72/0.74    inference(avatar_contradiction_clause,[],[f617])).
% 2.72/0.74  fof(f617,plain,(
% 2.72/0.74    $false | (~spl3_4 | spl3_5)),
% 2.72/0.74    inference(subsumption_resolution,[],[f600,f68])).
% 2.72/0.74  fof(f600,plain,(
% 2.72/0.74    ~r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) | (~spl3_4 | spl3_5)),
% 2.72/0.74    inference(backward_demodulation,[],[f175,f103])).
% 2.72/0.74  fof(f175,plain,(
% 2.72/0.74    ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl3_5),
% 2.72/0.74    inference(avatar_component_clause,[],[f173])).
% 2.72/0.74  fof(f173,plain,(
% 2.72/0.74    spl3_5 <=> r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.72/0.74  fof(f616,plain,(
% 2.72/0.74    ~spl3_4 | spl3_7),
% 2.72/0.74    inference(avatar_contradiction_clause,[],[f615])).
% 2.72/0.74  fof(f615,plain,(
% 2.72/0.74    $false | (~spl3_4 | spl3_7)),
% 2.72/0.74    inference(subsumption_resolution,[],[f598,f149])).
% 2.72/0.74  fof(f149,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 2.72/0.74    inference(superposition,[],[f146,f48])).
% 2.72/0.74  fof(f598,plain,(
% 2.72/0.74    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | (~spl3_4 | spl3_7)),
% 2.72/0.74    inference(backward_demodulation,[],[f425,f103])).
% 2.72/0.74  fof(f425,plain,(
% 2.72/0.74    ~r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl3_7),
% 2.72/0.74    inference(avatar_component_clause,[],[f423])).
% 2.72/0.74  fof(f423,plain,(
% 2.72/0.74    spl3_7 <=> r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.72/0.74  fof(f596,plain,(
% 2.72/0.74    spl3_17 | ~spl3_16),
% 2.72/0.74    inference(avatar_split_clause,[],[f595,f539,f544])).
% 2.72/0.74  fof(f595,plain,(
% 2.72/0.74    r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | ~spl3_16),
% 2.72/0.74    inference(resolution,[],[f541,f49])).
% 2.72/0.74  fof(f541,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | ~spl3_16),
% 2.72/0.74    inference(avatar_component_clause,[],[f539])).
% 2.72/0.74  fof(f592,plain,(
% 2.72/0.74    ~spl3_22 | ~spl3_18 | spl3_21),
% 2.72/0.74    inference(avatar_split_clause,[],[f591,f572,f549,f576])).
% 2.72/0.74  fof(f576,plain,(
% 2.72/0.74    spl3_22 <=> r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1)))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 2.72/0.74  fof(f549,plain,(
% 2.72/0.74    spl3_18 <=> r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 2.72/0.74  fof(f572,plain,(
% 2.72/0.74    spl3_21 <=> sK2 = k5_xboole_0(sK2,k2_tarski(sK1,sK1))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 2.72/0.74  fof(f591,plain,(
% 2.72/0.74    ~r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | (~spl3_18 | spl3_21)),
% 2.72/0.74    inference(subsumption_resolution,[],[f588,f551])).
% 2.72/0.74  fof(f551,plain,(
% 2.72/0.74    r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2) | ~spl3_18),
% 2.72/0.74    inference(avatar_component_clause,[],[f549])).
% 2.72/0.74  fof(f588,plain,(
% 2.72/0.74    ~r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | ~r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2) | spl3_21),
% 2.72/0.74    inference(extensionality_resolution,[],[f61,f573])).
% 2.72/0.74  fof(f573,plain,(
% 2.72/0.74    sK2 != k5_xboole_0(sK2,k2_tarski(sK1,sK1)) | spl3_21),
% 2.72/0.74    inference(avatar_component_clause,[],[f572])).
% 2.72/0.74  fof(f61,plain,(
% 2.72/0.74    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 2.72/0.74    inference(cnf_transformation,[],[f7])).
% 2.72/0.74  fof(f590,plain,(
% 2.72/0.74    ~spl3_22 | ~spl3_18 | spl3_21),
% 2.72/0.74    inference(avatar_split_clause,[],[f589,f572,f549,f576])).
% 2.72/0.74  fof(f589,plain,(
% 2.72/0.74    ~r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | (~spl3_18 | spl3_21)),
% 2.72/0.74    inference(subsumption_resolution,[],[f587,f551])).
% 2.72/0.74  fof(f587,plain,(
% 2.72/0.74    ~r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2) | ~r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | spl3_21),
% 2.72/0.74    inference(extensionality_resolution,[],[f61,f573])).
% 2.72/0.74  fof(f584,plain,(
% 2.72/0.74    spl3_23 | ~spl3_18),
% 2.72/0.74    inference(avatar_split_clause,[],[f570,f549,f581])).
% 2.72/0.74  fof(f581,plain,(
% 2.72/0.74    spl3_23 <=> k5_xboole_0(sK2,k2_tarski(sK1,sK1)) = k3_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 2.72/0.74  fof(f570,plain,(
% 2.72/0.74    k5_xboole_0(sK2,k2_tarski(sK1,sK1)) = k3_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2) | ~spl3_18),
% 2.72/0.74    inference(resolution,[],[f551,f62])).
% 2.72/0.74  fof(f62,plain,(
% 2.72/0.74    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 2.72/0.74    inference(cnf_transformation,[],[f35])).
% 2.72/0.74  fof(f35,plain,(
% 2.72/0.74    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.72/0.74    inference(ennf_transformation,[],[f11])).
% 2.72/0.74  fof(f11,axiom,(
% 2.72/0.74    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.72/0.74  fof(f579,plain,(
% 2.72/0.74    spl3_21 | ~spl3_22 | ~spl3_18),
% 2.72/0.74    inference(avatar_split_clause,[],[f569,f549,f576,f572])).
% 2.72/0.74  fof(f569,plain,(
% 2.72/0.74    ~r1_tarski(sK2,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | sK2 = k5_xboole_0(sK2,k2_tarski(sK1,sK1)) | ~spl3_18),
% 2.72/0.74    inference(resolution,[],[f551,f61])).
% 2.72/0.74  fof(f568,plain,(
% 2.72/0.74    spl3_17 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f567,f512,f544])).
% 2.72/0.74  fof(f512,plain,(
% 2.72/0.74    spl3_14 <=> k2_tarski(sK1,sK1) = k3_xboole_0(sK2,k2_tarski(sK1,sK1))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.72/0.74  fof(f567,plain,(
% 2.72/0.74    r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | ~spl3_14),
% 2.72/0.74    inference(forward_demodulation,[],[f531,f53])).
% 2.72/0.74  fof(f531,plain,(
% 2.72/0.74    r1_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),sK2),k2_tarski(sK1,sK1)) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f115,f514])).
% 2.72/0.74  fof(f514,plain,(
% 2.72/0.74    k2_tarski(sK1,sK1) = k3_xboole_0(sK2,k2_tarski(sK1,sK1)) | ~spl3_14),
% 2.72/0.74    inference(avatar_component_clause,[],[f512])).
% 2.72/0.74  fof(f566,plain,(
% 2.72/0.74    spl3_20 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f530,f512,f563])).
% 2.72/0.74  fof(f563,plain,(
% 2.72/0.74    spl3_20 <=> r1_xboole_0(sK2,k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 2.72/0.74  fof(f530,plain,(
% 2.72/0.74    r1_xboole_0(sK2,k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1))) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f108,f514])).
% 2.72/0.74  fof(f561,plain,(
% 2.72/0.74    spl3_19 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f529,f512,f558])).
% 2.72/0.74  fof(f558,plain,(
% 2.72/0.74    spl3_19 <=> r1_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)),sK2)),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 2.72/0.74  fof(f529,plain,(
% 2.72/0.74    r1_xboole_0(k5_xboole_0(k2_tarski(sK1,sK1),k2_tarski(sK1,sK1)),sK2) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f97,f514])).
% 2.72/0.74  fof(f556,plain,(
% 2.72/0.74    spl3_16 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f555,f512,f539])).
% 2.72/0.74  fof(f555,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | ~spl3_14),
% 2.72/0.74    inference(forward_demodulation,[],[f527,f53])).
% 2.72/0.74  fof(f527,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(k2_tarski(sK1,sK1),sK2)) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f92,f514])).
% 2.72/0.74  fof(f554,plain,(
% 2.72/0.74    spl3_17 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f526,f512,f544])).
% 2.72/0.74  fof(f526,plain,(
% 2.72/0.74    r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f90,f514])).
% 2.72/0.74  fof(f553,plain,(
% 2.72/0.74    spl3_16 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f525,f512,f539])).
% 2.72/0.74  fof(f525,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f85,f514])).
% 2.72/0.74  fof(f552,plain,(
% 2.72/0.74    spl3_18 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f524,f512,f549])).
% 2.72/0.74  fof(f524,plain,(
% 2.72/0.74    r1_tarski(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),sK2) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f67,f514])).
% 2.72/0.74  fof(f67,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r1_tarski(k5_xboole_0(X0,k3_xboole_0(X0,X1)),X0)) )),
% 2.72/0.74    inference(definition_unfolding,[],[f47,f45])).
% 2.72/0.74  fof(f47,plain,(
% 2.72/0.74    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f12])).
% 2.72/0.74  fof(f12,axiom,(
% 2.72/0.74    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.72/0.74  fof(f547,plain,(
% 2.72/0.74    spl3_17 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f523,f512,f544])).
% 2.72/0.74  fof(f523,plain,(
% 2.72/0.74    r1_xboole_0(k5_xboole_0(sK2,k2_tarski(sK1,sK1)),k2_tarski(sK1,sK1)) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f66,f514])).
% 2.72/0.74  fof(f542,plain,(
% 2.72/0.74    spl3_16 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f522,f512,f539])).
% 2.72/0.74  fof(f522,plain,(
% 2.72/0.74    r1_xboole_0(k2_tarski(sK1,sK1),k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f50,f514])).
% 2.72/0.74  fof(f537,plain,(
% 2.72/0.74    ~spl3_15 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f521,f512,f533])).
% 2.72/0.74  fof(f521,plain,(
% 2.72/0.74    ~r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f111,f514])).
% 2.72/0.74  fof(f536,plain,(
% 2.72/0.74    ~spl3_15 | ~spl3_14),
% 2.72/0.74    inference(avatar_split_clause,[],[f520,f512,f533])).
% 2.72/0.74  fof(f520,plain,(
% 2.72/0.74    ~r2_hidden(sK1,k5_xboole_0(sK2,k2_tarski(sK1,sK1))) | ~spl3_14),
% 2.72/0.74    inference(superposition,[],[f161,f514])).
% 2.72/0.74  fof(f515,plain,(
% 2.72/0.74    spl3_14 | ~spl3_2),
% 2.72/0.74    inference(avatar_split_clause,[],[f510,f75,f512])).
% 2.72/0.74  fof(f510,plain,(
% 2.72/0.74    k2_tarski(sK1,sK1) = k3_xboole_0(sK2,k2_tarski(sK1,sK1)) | ~spl3_2),
% 2.72/0.74    inference(resolution,[],[f483,f76])).
% 2.72/0.74  fof(f483,plain,(
% 2.72/0.74    ( ! [X0] : (~r2_hidden(X0,sK2) | k2_tarski(X0,sK1) = k3_xboole_0(sK2,k2_tarski(X0,sK1))) ) | ~spl3_2),
% 2.72/0.74    inference(forward_demodulation,[],[f482,f54])).
% 2.72/0.74  fof(f482,plain,(
% 2.72/0.74    ( ! [X0] : (~r2_hidden(X0,sK2) | k2_tarski(X0,sK1) = k3_xboole_0(k2_tarski(X0,sK1),sK2)) ) | ~spl3_2),
% 2.72/0.74    inference(resolution,[],[f76,f44])).
% 2.72/0.74  fof(f44,plain,(
% 2.72/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1) | k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f33])).
% 2.72/0.74  fof(f33,plain,(
% 2.72/0.74    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X0,X1))),
% 2.72/0.74    inference(flattening,[],[f32])).
% 2.72/0.74  fof(f32,plain,(
% 2.72/0.74    ! [X0,X1,X2] : (k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1) | (~r2_hidden(X2,X1) | ~r2_hidden(X0,X1)))),
% 2.72/0.74    inference(ennf_transformation,[],[f24])).
% 2.72/0.74  fof(f24,axiom,(
% 2.72/0.74    ! [X0,X1,X2] : ((r2_hidden(X2,X1) & r2_hidden(X0,X1)) => k2_tarski(X0,X2) = k3_xboole_0(k2_tarski(X0,X2),X1))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).
% 2.72/0.74  fof(f502,plain,(
% 2.72/0.74    ~spl3_13 | spl3_11),
% 2.72/0.74    inference(avatar_split_clause,[],[f497,f487,f499])).
% 2.72/0.74  fof(f487,plain,(
% 2.72/0.74    spl3_11 <=> r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(sK2,k2_tarski(sK0,sK0)))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.72/0.74  fof(f497,plain,(
% 2.72/0.74    ~r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0))) | spl3_11),
% 2.72/0.74    inference(duplicate_literal_removal,[],[f496])).
% 2.72/0.74  fof(f496,plain,(
% 2.72/0.74    ~r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0))) | ~r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK0))) | spl3_11),
% 2.72/0.74    inference(resolution,[],[f489,f58])).
% 2.72/0.74  fof(f58,plain,(
% 2.72/0.74    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.72/0.74    inference(cnf_transformation,[],[f23])).
% 2.72/0.74  fof(f489,plain,(
% 2.72/0.74    ~r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(sK2,k2_tarski(sK0,sK0))) | spl3_11),
% 2.72/0.74    inference(avatar_component_clause,[],[f487])).
% 2.72/0.74  fof(f495,plain,(
% 2.72/0.74    ~spl3_12 | ~spl3_11 | spl3_10),
% 2.72/0.74    inference(avatar_split_clause,[],[f485,f466,f487,f491])).
% 2.72/0.74  fof(f491,plain,(
% 2.72/0.74    spl3_12 <=> r1_tarski(k3_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.72/0.74  fof(f466,plain,(
% 2.72/0.74    spl3_10 <=> k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 2.72/0.74  fof(f485,plain,(
% 2.72/0.74    ~r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(sK2,k2_tarski(sK0,sK0))) | ~r1_tarski(k3_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | spl3_10),
% 2.72/0.74    inference(extensionality_resolution,[],[f61,f467])).
% 2.72/0.74  fof(f467,plain,(
% 2.72/0.74    k2_tarski(sK0,sK0) != k3_xboole_0(sK2,k2_tarski(sK0,sK0)) | spl3_10),
% 2.72/0.74    inference(avatar_component_clause,[],[f466])).
% 2.72/0.74  fof(f494,plain,(
% 2.72/0.74    ~spl3_11 | ~spl3_12 | spl3_10),
% 2.72/0.74    inference(avatar_split_clause,[],[f484,f466,f491,f487])).
% 2.72/0.74  fof(f484,plain,(
% 2.72/0.74    ~r1_tarski(k3_xboole_0(sK2,k2_tarski(sK0,sK0)),k2_tarski(sK0,sK0)) | ~r1_tarski(k2_tarski(sK0,sK0),k3_xboole_0(sK2,k2_tarski(sK0,sK0))) | spl3_10),
% 2.72/0.74    inference(extensionality_resolution,[],[f61,f467])).
% 2.72/0.74  fof(f481,plain,(
% 2.72/0.74    spl3_4 | ~spl3_1),
% 2.72/0.74    inference(avatar_split_clause,[],[f480,f71,f102])).
% 2.72/0.74  fof(f71,plain,(
% 2.72/0.74    spl3_1 <=> k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.72/0.74  fof(f480,plain,(
% 2.72/0.74    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_1),
% 2.72/0.74    inference(forward_demodulation,[],[f73,f54])).
% 2.72/0.74  fof(f73,plain,(
% 2.72/0.74    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~spl3_1),
% 2.72/0.74    inference(avatar_component_clause,[],[f71])).
% 2.72/0.74  fof(f479,plain,(
% 2.72/0.74    spl3_2 | ~spl3_9),
% 2.72/0.74    inference(avatar_split_clause,[],[f475,f443,f75])).
% 2.72/0.74  fof(f443,plain,(
% 2.72/0.74    spl3_9 <=> r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.72/0.74  fof(f475,plain,(
% 2.72/0.74    r2_hidden(sK1,sK2) | ~spl3_9),
% 2.72/0.74    inference(resolution,[],[f445,f246])).
% 2.72/0.74  fof(f246,plain,(
% 2.72/0.74    ( ! [X10,X11,X9] : (~r2_hidden(X9,k3_xboole_0(X10,k2_tarski(X11,X9))) | r2_hidden(X9,X10)) )),
% 2.72/0.74    inference(resolution,[],[f42,f161])).
% 2.72/0.74  fof(f445,plain,(
% 2.72/0.74    r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_9),
% 2.72/0.74    inference(avatar_component_clause,[],[f443])).
% 2.72/0.74  fof(f478,plain,(
% 2.72/0.74    spl3_2 | ~spl3_9),
% 2.72/0.74    inference(avatar_contradiction_clause,[],[f477])).
% 2.72/0.74  fof(f477,plain,(
% 2.72/0.74    $false | (spl3_2 | ~spl3_9)),
% 2.72/0.74    inference(subsumption_resolution,[],[f475,f77])).
% 2.72/0.74  fof(f77,plain,(
% 2.72/0.74    ~r2_hidden(sK1,sK2) | spl3_2),
% 2.72/0.74    inference(avatar_component_clause,[],[f75])).
% 2.72/0.74  fof(f471,plain,(
% 2.72/0.74    ~spl3_4 | spl3_1),
% 2.72/0.74    inference(avatar_split_clause,[],[f470,f71,f102])).
% 2.72/0.74  fof(f470,plain,(
% 2.72/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_1),
% 2.72/0.74    inference(forward_demodulation,[],[f72,f54])).
% 2.72/0.74  fof(f72,plain,(
% 2.72/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_1),
% 2.72/0.74    inference(avatar_component_clause,[],[f71])).
% 2.72/0.74  fof(f469,plain,(
% 2.72/0.74    spl3_10 | ~spl3_3),
% 2.72/0.74    inference(avatar_split_clause,[],[f464,f80,f466])).
% 2.72/0.74  fof(f464,plain,(
% 2.72/0.74    k2_tarski(sK0,sK0) = k3_xboole_0(sK2,k2_tarski(sK0,sK0)) | ~spl3_3),
% 2.72/0.74    inference(resolution,[],[f457,f81])).
% 2.72/0.74  fof(f81,plain,(
% 2.72/0.74    r2_hidden(sK0,sK2) | ~spl3_3),
% 2.72/0.74    inference(avatar_component_clause,[],[f80])).
% 2.72/0.74  fof(f457,plain,(
% 2.72/0.74    ( ! [X0] : (~r2_hidden(X0,sK2) | k2_tarski(X0,sK0) = k3_xboole_0(sK2,k2_tarski(X0,sK0))) ) | ~spl3_3),
% 2.72/0.74    inference(forward_demodulation,[],[f456,f54])).
% 2.72/0.74  fof(f456,plain,(
% 2.72/0.74    ( ! [X0] : (~r2_hidden(X0,sK2) | k2_tarski(X0,sK0) = k3_xboole_0(k2_tarski(X0,sK0),sK2)) ) | ~spl3_3),
% 2.72/0.74    inference(resolution,[],[f81,f44])).
% 2.72/0.74  fof(f455,plain,(
% 2.72/0.74    spl3_4 | ~spl3_1),
% 2.72/0.74    inference(avatar_split_clause,[],[f452,f71,f102])).
% 2.72/0.74  fof(f452,plain,(
% 2.72/0.74    k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_1),
% 2.72/0.74    inference(forward_demodulation,[],[f73,f54])).
% 2.72/0.74  fof(f454,plain,(
% 2.72/0.74    ~spl3_1 | spl3_4),
% 2.72/0.74    inference(avatar_contradiction_clause,[],[f453])).
% 2.72/0.74  fof(f453,plain,(
% 2.72/0.74    $false | (~spl3_1 | spl3_4)),
% 2.72/0.74    inference(subsumption_resolution,[],[f452,f104])).
% 2.72/0.74  fof(f104,plain,(
% 2.72/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_4),
% 2.72/0.74    inference(avatar_component_clause,[],[f102])).
% 2.72/0.74  fof(f451,plain,(
% 2.72/0.74    spl3_3 | ~spl3_8),
% 2.72/0.74    inference(avatar_split_clause,[],[f447,f431,f80])).
% 2.72/0.74  fof(f431,plain,(
% 2.72/0.74    spl3_8 <=> r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.72/0.74    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 2.72/0.74  fof(f447,plain,(
% 2.72/0.74    r2_hidden(sK0,sK2) | ~spl3_8),
% 2.72/0.74    inference(resolution,[],[f433,f245])).
% 2.72/0.74  fof(f245,plain,(
% 2.72/0.74    ( ! [X6,X8,X7] : (~r2_hidden(X6,k3_xboole_0(X7,k2_tarski(X6,X8))) | r2_hidden(X6,X7)) )),
% 2.72/0.74    inference(resolution,[],[f42,f111])).
% 2.72/0.74  fof(f433,plain,(
% 2.72/0.74    r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_8),
% 2.72/0.74    inference(avatar_component_clause,[],[f431])).
% 2.72/0.74  fof(f450,plain,(
% 2.72/0.74    spl3_3 | ~spl3_8),
% 2.72/0.74    inference(avatar_contradiction_clause,[],[f449])).
% 2.72/0.74  fof(f449,plain,(
% 2.72/0.74    $false | (spl3_3 | ~spl3_8)),
% 2.72/0.74    inference(subsumption_resolution,[],[f447,f82])).
% 2.72/0.74  fof(f82,plain,(
% 2.72/0.74    ~r2_hidden(sK0,sK2) | spl3_3),
% 2.72/0.74    inference(avatar_component_clause,[],[f80])).
% 2.72/0.74  fof(f446,plain,(
% 2.72/0.74    spl3_9 | spl3_7),
% 2.72/0.74    inference(avatar_split_clause,[],[f441,f423,f443])).
% 2.72/0.74  fof(f441,plain,(
% 2.72/0.74    r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_7),
% 2.72/0.74    inference(subsumption_resolution,[],[f439,f149])).
% 2.72/0.74  fof(f439,plain,(
% 2.72/0.74    ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_7),
% 2.72/0.74    inference(resolution,[],[f425,f43])).
% 2.72/0.74  fof(f434,plain,(
% 2.72/0.74    spl3_8 | spl3_6),
% 2.72/0.74    inference(avatar_split_clause,[],[f429,f419,f431])).
% 2.72/0.74  fof(f429,plain,(
% 2.72/0.74    r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_6),
% 2.72/0.74    inference(subsumption_resolution,[],[f427,f146])).
% 2.72/0.74  fof(f427,plain,(
% 2.72/0.74    ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_6),
% 2.72/0.74    inference(resolution,[],[f421,f43])).
% 2.72/0.74  fof(f426,plain,(
% 2.72/0.74    ~spl3_6 | ~spl3_7 | spl3_5),
% 2.72/0.74    inference(avatar_split_clause,[],[f412,f173,f423,f419])).
% 2.72/0.74  fof(f412,plain,(
% 2.72/0.74    ~r2_hidden(sK1,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | ~r2_hidden(sK0,k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl3_5),
% 2.72/0.74    inference(resolution,[],[f58,f175])).
% 2.72/0.74  fof(f178,plain,(
% 2.72/0.74    ~spl3_5 | spl3_4),
% 2.72/0.74    inference(avatar_split_clause,[],[f177,f102,f173])).
% 2.72/0.74  fof(f177,plain,(
% 2.72/0.74    ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl3_4),
% 2.72/0.74    inference(subsumption_resolution,[],[f166,f96])).
% 2.72/0.74  fof(f96,plain,(
% 2.72/0.74    ( ! [X4,X3] : (r1_tarski(k5_xboole_0(X3,k3_xboole_0(X4,X3)),X3)) )),
% 2.72/0.74    inference(superposition,[],[f67,f54])).
% 2.72/0.74  fof(f166,plain,(
% 2.72/0.74    ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | ~r1_tarski(k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) | spl3_4),
% 2.72/0.74    inference(extensionality_resolution,[],[f61,f104])).
% 2.72/0.74  fof(f176,plain,(
% 2.72/0.74    ~spl3_5 | spl3_4),
% 2.72/0.74    inference(avatar_split_clause,[],[f171,f102,f173])).
% 2.72/0.74  fof(f171,plain,(
% 2.72/0.74    ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl3_4),
% 2.72/0.74    inference(subsumption_resolution,[],[f165,f96])).
% 2.72/0.74  fof(f165,plain,(
% 2.72/0.74    ~r1_tarski(k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))),k2_tarski(sK0,sK1)) | ~r1_tarski(k2_tarski(sK0,sK1),k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))) | spl3_4),
% 2.72/0.74    inference(extensionality_resolution,[],[f61,f104])).
% 2.72/0.74  fof(f105,plain,(
% 2.72/0.74    ~spl3_4 | spl3_1),
% 2.72/0.74    inference(avatar_split_clause,[],[f94,f71,f102])).
% 2.72/0.74  fof(f94,plain,(
% 2.72/0.74    k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_1),
% 2.72/0.74    inference(backward_demodulation,[],[f72,f54])).
% 2.72/0.74  fof(f84,plain,(
% 2.72/0.74    ~spl3_1 | spl3_2 | spl3_3),
% 2.72/0.74    inference(avatar_split_clause,[],[f65,f80,f75,f71])).
% 2.72/0.74  fof(f65,plain,(
% 2.72/0.74    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) != k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.72/0.74    inference(definition_unfolding,[],[f36,f45])).
% 2.72/0.74  fof(f36,plain,(
% 2.72/0.74    r2_hidden(sK0,sK2) | r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.72/0.74    inference(cnf_transformation,[],[f29])).
% 2.72/0.74  fof(f29,plain,(
% 2.72/0.74    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.72/0.74    inference(ennf_transformation,[],[f27])).
% 2.72/0.74  fof(f27,negated_conjecture,(
% 2.72/0.74    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.72/0.74    inference(negated_conjecture,[],[f26])).
% 2.72/0.74  fof(f26,conjecture,(
% 2.72/0.74    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.72/0.74    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.72/0.74  fof(f83,plain,(
% 2.72/0.74    spl3_1 | ~spl3_3),
% 2.72/0.74    inference(avatar_split_clause,[],[f64,f80,f71])).
% 2.72/0.74  fof(f64,plain,(
% 2.72/0.74    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.72/0.74    inference(definition_unfolding,[],[f37,f45])).
% 2.72/0.74  fof(f37,plain,(
% 2.72/0.74    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.72/0.74    inference(cnf_transformation,[],[f29])).
% 2.72/0.74  fof(f78,plain,(
% 2.72/0.74    spl3_1 | ~spl3_2),
% 2.72/0.74    inference(avatar_split_clause,[],[f63,f75,f71])).
% 2.72/0.74  fof(f63,plain,(
% 2.72/0.74    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.72/0.74    inference(definition_unfolding,[],[f38,f45])).
% 2.72/0.74  fof(f38,plain,(
% 2.72/0.74    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.72/0.74    inference(cnf_transformation,[],[f29])).
% 2.72/0.74  % SZS output end Proof for theBenchmark
% 2.72/0.74  % (32764)------------------------------
% 2.72/0.74  % (32764)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.72/0.74  % (32764)Termination reason: Refutation
% 2.72/0.74  
% 2.72/0.74  % (32764)Memory used [KB]: 2046
% 2.72/0.74  % (32764)Time elapsed: 0.307 s
% 2.72/0.74  % (32764)------------------------------
% 2.72/0.74  % (32764)------------------------------
% 2.72/0.75  % (32763)Success in time 0.368 s
%------------------------------------------------------------------------------
