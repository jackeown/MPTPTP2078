%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:41:20 EST 2020

% Result     : Theorem 2.86s
% Output     : Refutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 333 expanded)
%              Number of leaves         :   29 ( 115 expanded)
%              Depth                    :   15
%              Number of atoms          :  346 ( 745 expanded)
%              Number of equality atoms :   80 ( 219 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3913,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f90,f91,f1134,f1139,f1165,f1167,f2429,f2711,f2900,f2995,f3073,f3087,f3131,f3205,f3216,f3912])).

fof(f3912,plain,
    ( spl3_1
    | ~ spl3_15
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f3911])).

fof(f3911,plain,
    ( $false
    | spl3_1
    | ~ spl3_15
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f3910,f80])).

fof(f80,plain,
    ( k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl3_1
  <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f3910,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_15
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f3909,f1212])).

fof(f1212,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f1210])).

fof(f1210,plain,
    ( spl3_15
  <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f3909,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f3908,f126])).

fof(f126,plain,(
    ! [X4,X3] : k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3)) ),
    inference(superposition,[],[f63,f65])).

fof(f65,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f63,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f3908,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_37 ),
    inference(forward_demodulation,[],[f3873,f64])).

fof(f64,plain,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

fof(f3873,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1))
    | ~ spl3_37 ),
    inference(superposition,[],[f2904,f3209])).

fof(f3209,plain,
    ( k3_xboole_0(sK2,k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f3207])).

fof(f3207,plain,
    ( spl3_37
  <=> k3_xboole_0(sK2,k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f2904,plain,(
    ! [X6,X5] : k4_xboole_0(X6,X5) = k5_xboole_0(k3_xboole_0(X6,X5),X6) ),
    inference(superposition,[],[f2820,f65])).

fof(f2820,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(backward_demodulation,[],[f211,f546])).

fof(f546,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k3_xboole_0(X2,k5_xboole_0(X3,X2)) ),
    inference(superposition,[],[f529,f64])).

fof(f529,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f210,f126])).

fof(f210,plain,(
    ! [X0,X1] : k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1)) ),
    inference(forward_demodulation,[],[f191,f65])).

fof(f191,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f56,f67])).

fof(f67,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f56,plain,(
    ! [X2,X0,X1] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

fof(f211,plain,(
    ! [X0,X1] : k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0)) ),
    inference(forward_demodulation,[],[f195,f65])).

fof(f195,plain,(
    ! [X0,X1] : k3_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f56,f67])).

fof(f3216,plain,
    ( spl3_37
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f3215,f1196,f3207])).

fof(f1196,plain,
    ( spl3_13
  <=> k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f3215,plain,
    ( k3_xboole_0(sK2,k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f3214,f1198])).

fof(f1198,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f1196])).

fof(f3214,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f3198,f124])).

fof(f124,plain,(
    ! [X0] : k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0) ),
    inference(superposition,[],[f63,f67])).

fof(f3198,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_13 ),
    inference(superposition,[],[f546,f1198])).

fof(f3205,plain,
    ( spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f3174,f1196,f1210])).

fof(f3174,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_13 ),
    inference(superposition,[],[f237,f1198])).

fof(f237,plain,(
    ! [X1] : k4_xboole_0(X1,k5_xboole_0(X1,X1)) = X1 ),
    inference(forward_demodulation,[],[f233,f67])).

fof(f233,plain,(
    ! [X1] : k3_xboole_0(X1,X1) = k4_xboole_0(X1,k5_xboole_0(X1,X1)) ),
    inference(superposition,[],[f62,f124])).

fof(f62,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f3131,plain,
    ( spl3_13
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f3130,f1131,f1196])).

fof(f1131,plain,
    ( spl3_6
  <=> k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f3130,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f3100,f75])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f3100,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1))
    | ~ spl3_6 ),
    inference(superposition,[],[f125,f1133])).

fof(f1133,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f1131])).

fof(f125,plain,(
    ! [X2,X1] :
      ( k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1)
      | ~ r1_tarski(X1,X2) ) ),
    inference(superposition,[],[f63,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f3087,plain,
    ( spl3_3
    | ~ spl3_16 ),
    inference(avatar_contradiction_clause,[],[f3086])).

fof(f3086,plain,
    ( $false
    | spl3_3
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f3085,f238])).

fof(f238,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X0))) ),
    inference(resolution,[],[f103,f92])).

fof(f92,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f70,f68])).

fof(f68,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X1,X0),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(superposition,[],[f47,f66])).

fof(f66,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_hidden(X0,X2)
      | ~ r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ~ ( r2_hidden(X0,X2)
        & r1_xboole_0(k2_tarski(X0,X1),X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

fof(f3085,plain,
    ( r2_hidden(sK1,k4_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_3
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f3080,f87])).

fof(f87,plain,
    ( ~ r2_hidden(sK1,sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_3
  <=> r2_hidden(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f3080,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK1,k4_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_16 ),
    inference(resolution,[],[f1322,f165])).

fof(f165,plain,(
    ! [X10,X8,X9] :
      ( ~ r2_hidden(X10,k3_xboole_0(X8,X9))
      | r2_hidden(X10,X8)
      | r2_hidden(X10,k4_xboole_0(X8,X9)) ) ),
    inference(superposition,[],[f54,f63])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k5_xboole_0(X1,X2))
        | ( ( r2_hidden(X0,X1)
            | ~ r2_hidden(X0,X2) )
          & ( r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) ) ) )
      & ( ( ( ~ r2_hidden(X0,X2)
            | ~ r2_hidden(X0,X1) )
          & ( r2_hidden(X0,X2)
            | r2_hidden(X0,X1) ) )
        | ~ r2_hidden(X0,k5_xboole_0(X1,X2)) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ( r2_hidden(X0,X1)
      <~> r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
    <=> ~ ( r2_hidden(X0,X1)
        <=> r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

fof(f1322,plain,
    ( r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f1321])).

fof(f1321,plain,
    ( spl3_16
  <=> r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f3073,plain,
    ( spl3_16
    | spl3_36 ),
    inference(avatar_split_clause,[],[f3070,f2708,f1321])).

fof(f2708,plain,
    ( spl3_36
  <=> r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f3070,plain,
    ( r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_36 ),
    inference(forward_demodulation,[],[f3069,f65])).

fof(f3069,plain,
    ( r2_hidden(sK1,k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_36 ),
    inference(subsumption_resolution,[],[f3068,f108])).

fof(f108,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f49,f75])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f3068,plain,
    ( r2_hidden(sK1,k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ r2_hidden(sK1,k2_tarski(sK0,sK1))
    | spl3_36 ),
    inference(resolution,[],[f2710,f155])).

fof(f155,plain,(
    ! [X10,X8,X9] :
      ( r2_hidden(X10,k4_xboole_0(X8,X9))
      | r2_hidden(X10,k3_xboole_0(X8,X9))
      | ~ r2_hidden(X10,X8) ) ),
    inference(superposition,[],[f53,f63])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k5_xboole_0(X1,X2))
      | r2_hidden(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2710,plain,
    ( ~ r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f2708])).

fof(f2995,plain,
    ( spl3_2
    | ~ spl3_14 ),
    inference(avatar_contradiction_clause,[],[f2994])).

fof(f2994,plain,
    ( $false
    | spl3_2
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f2993,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] : ~ r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X2))) ),
    inference(resolution,[],[f47,f92])).

fof(f2993,plain,
    ( r2_hidden(sK0,k4_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_2
    | ~ spl3_14 ),
    inference(subsumption_resolution,[],[f2988,f83])).

fof(f83,plain,
    ( ~ r2_hidden(sK0,sK2)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_2
  <=> r2_hidden(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f2988,plain,
    ( r2_hidden(sK0,sK2)
    | r2_hidden(sK0,k4_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_14 ),
    inference(resolution,[],[f1204,f165])).

fof(f1204,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f1203])).

fof(f1203,plain,
    ( spl3_14
  <=> r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f2900,plain,
    ( spl3_14
    | spl3_35 ),
    inference(avatar_split_clause,[],[f2897,f2704,f1203])).

fof(f2704,plain,
    ( spl3_35
  <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f2897,plain,
    ( r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))
    | spl3_35 ),
    inference(forward_demodulation,[],[f2896,f65])).

fof(f2896,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_35 ),
    inference(subsumption_resolution,[],[f2895,f105])).

fof(f105,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f48,f75])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k2_tarski(X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2895,plain,
    ( r2_hidden(sK0,k3_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ r2_hidden(sK0,k2_tarski(sK0,sK1))
    | spl3_35 ),
    inference(resolution,[],[f2706,f155])).

fof(f2706,plain,
    ( ~ r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f2704])).

fof(f2711,plain,
    ( ~ spl3_35
    | ~ spl3_36
    | spl3_25 ),
    inference(avatar_split_clause,[],[f2702,f2426,f2708,f2704])).

fof(f2426,plain,
    ( spl3_25
  <=> r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f2702,plain,
    ( ~ r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | ~ r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_25 ),
    inference(resolution,[],[f2428,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f2428,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f2426])).

fof(f2429,plain,
    ( ~ spl3_25
    | spl3_13 ),
    inference(avatar_split_clause,[],[f2424,f1196,f2426])).

fof(f2424,plain,
    ( ~ r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2))
    | spl3_13 ),
    inference(equality_resolution,[],[f1669])).

fof(f1669,plain,
    ( ! [X3] :
        ( k3_xboole_0(sK2,k2_tarski(sK0,sK1)) != k3_xboole_0(X3,k2_tarski(sK0,sK1))
        | ~ r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),X3)) )
    | spl3_13 ),
    inference(superposition,[],[f1606,f65])).

fof(f1606,plain,
    ( ! [X2] :
        ( k3_xboole_0(sK2,k2_tarski(sK0,sK1)) != k3_xboole_0(k2_tarski(sK0,sK1),X2)
        | ~ r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),X2)) )
    | spl3_13 ),
    inference(superposition,[],[f1602,f62])).

fof(f1602,plain,
    ( ! [X0] :
        ( k3_xboole_0(sK2,k2_tarski(sK0,sK1)) != k4_xboole_0(k2_tarski(sK0,sK1),X0)
        | ~ r1_tarski(k2_tarski(sK0,sK1),X0) )
    | spl3_13 ),
    inference(superposition,[],[f1197,f125])).

fof(f1197,plain,
    ( k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) != k3_xboole_0(sK2,k2_tarski(sK0,sK1))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f1196])).

fof(f1167,plain,
    ( ~ spl3_2
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f1160,f1136,f82])).

fof(f1136,plain,
    ( spl3_7
  <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f1160,plain,
    ( ~ r2_hidden(sK0,sK2)
    | ~ spl3_7 ),
    inference(resolution,[],[f1138,f47])).

fof(f1138,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f1136])).

fof(f1165,plain,
    ( ~ spl3_3
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f1159,f1136,f86])).

fof(f1159,plain,
    ( ~ r2_hidden(sK1,sK2)
    | ~ spl3_7 ),
    inference(resolution,[],[f1138,f103])).

fof(f1139,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f1121,f78,f1136])).

fof(f1121,plain,
    ( r1_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(superposition,[],[f68,f79])).

fof(f79,plain,
    ( k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f1134,plain,
    ( spl3_6
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f1129,f78,f1131])).

fof(f1129,plain,
    ( k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1))
    | ~ spl3_1 ),
    inference(forward_demodulation,[],[f1120,f65])).

fof(f1120,plain,
    ( k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1))
    | ~ spl3_1 ),
    inference(superposition,[],[f62,f79])).

fof(f91,plain,
    ( spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f44,f82,f78])).

fof(f44,plain,
    ( ~ r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( r2_hidden(sK1,sK2)
      | r2_hidden(sK0,sK2)
      | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
    & ( ( ~ r2_hidden(sK1,sK2)
        & ~ r2_hidden(sK0,sK2) )
      | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f37])).

fof(f37,plain,
    ( ? [X0,X1,X2] :
        ( ( r2_hidden(X1,X2)
          | r2_hidden(X0,X2)
          | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
        & ( ( ~ r2_hidden(X1,X2)
            & ~ r2_hidden(X0,X2) )
          | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) )
   => ( ( r2_hidden(sK1,sK2)
        | r2_hidden(sK0,sK2)
        | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) )
      & ( ( ~ r2_hidden(sK1,sK2)
          & ~ r2_hidden(sK0,sK2) )
        | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1,X2] :
      ( ( r2_hidden(X1,X2)
        | r2_hidden(X0,X2)
        | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2) )
      & ( ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) )
        | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <~> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
      <=> ( ~ r2_hidden(X1,X2)
          & ~ r2_hidden(X0,X2) ) ) ),
    inference(negated_conjecture,[],[f25])).

fof(f25,conjecture,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)
    <=> ( ~ r2_hidden(X1,X2)
        & ~ r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).

fof(f90,plain,
    ( spl3_1
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f45,f86,f78])).

fof(f45,plain,
    ( ~ r2_hidden(sK1,sK2)
    | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,
    ( ~ spl3_1
    | spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f46,f86,f82,f78])).

fof(f46,plain,
    ( r2_hidden(sK1,sK2)
    | r2_hidden(sK0,sK2)
    | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 14:32:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (4339)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.50  % (4339)Refutation not found, incomplete strategy% (4339)------------------------------
% 0.21/0.50  % (4339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4332)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.51  % (4339)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4339)Memory used [KB]: 10746
% 0.21/0.51  % (4339)Time elapsed: 0.102 s
% 0.21/0.51  % (4339)------------------------------
% 0.21/0.51  % (4339)------------------------------
% 0.21/0.51  % (4343)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (4343)Refutation not found, incomplete strategy% (4343)------------------------------
% 0.21/0.51  % (4343)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (4343)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (4343)Memory used [KB]: 1663
% 0.21/0.51  % (4343)Time elapsed: 0.007 s
% 0.21/0.51  % (4343)------------------------------
% 0.21/0.51  % (4343)------------------------------
% 0.21/0.51  % (4335)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (4350)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.52  % (4329)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (4355)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (4342)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.52  % (4355)Refutation not found, incomplete strategy% (4355)------------------------------
% 0.21/0.52  % (4355)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (4355)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (4355)Memory used [KB]: 6268
% 0.21/0.52  % (4355)Time elapsed: 0.122 s
% 0.21/0.52  % (4355)------------------------------
% 0.21/0.52  % (4355)------------------------------
% 0.21/0.52  % (4351)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (4338)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.53  % (4347)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (4344)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (4358)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (4333)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (4358)Refutation not found, incomplete strategy% (4358)------------------------------
% 0.21/0.54  % (4358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (4358)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (4358)Memory used [KB]: 1663
% 0.21/0.54  % (4358)Time elapsed: 0.002 s
% 0.21/0.54  % (4358)------------------------------
% 0.21/0.54  % (4358)------------------------------
% 0.21/0.54  % (4331)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.55  % (4348)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.46/0.55  % (4352)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.46/0.55  % (4340)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.46/0.56  % (4340)Refutation not found, incomplete strategy% (4340)------------------------------
% 1.46/0.56  % (4340)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (4340)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (4340)Memory used [KB]: 6140
% 1.46/0.56  % (4340)Time elapsed: 0.130 s
% 1.46/0.56  % (4340)------------------------------
% 1.46/0.56  % (4340)------------------------------
% 1.46/0.56  % (4354)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.46/0.56  % (4336)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.46/0.56  % (4337)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.46/0.56  % (4346)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.46/0.56  % (4346)Refutation not found, incomplete strategy% (4346)------------------------------
% 1.46/0.56  % (4346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % (4346)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.56  
% 1.46/0.56  % (4346)Memory used [KB]: 1663
% 1.46/0.56  % (4346)Time elapsed: 0.146 s
% 1.46/0.56  % (4346)------------------------------
% 1.46/0.56  % (4346)------------------------------
% 1.60/0.57  % (4353)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.60/0.57  % (4334)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.60/0.58  % (4330)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.60/0.58  % (4330)Refutation not found, incomplete strategy% (4330)------------------------------
% 1.60/0.58  % (4330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.58  % (4330)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.58  
% 1.60/0.58  % (4330)Memory used [KB]: 1663
% 1.60/0.58  % (4330)Time elapsed: 0.156 s
% 1.60/0.58  % (4330)------------------------------
% 1.60/0.58  % (4330)------------------------------
% 1.60/0.58  % (4345)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.60/0.59  % (4349)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.60/0.59  % (4345)Refutation not found, incomplete strategy% (4345)------------------------------
% 1.60/0.59  % (4345)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (4356)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.60/0.59  % (4345)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.59  
% 1.60/0.59  % (4345)Memory used [KB]: 10618
% 1.60/0.59  % (4345)Time elapsed: 0.169 s
% 1.60/0.59  % (4345)------------------------------
% 1.60/0.59  % (4345)------------------------------
% 1.60/0.59  % (4357)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.60/0.59  % (4357)Refutation not found, incomplete strategy% (4357)------------------------------
% 1.60/0.59  % (4357)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.59  % (4357)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.59  
% 1.60/0.59  % (4357)Memory used [KB]: 10746
% 1.60/0.59  % (4357)Time elapsed: 0.169 s
% 1.60/0.59  % (4357)------------------------------
% 1.60/0.59  % (4357)------------------------------
% 1.60/0.60  % (4341)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.60/0.62  % (4390)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 1.99/0.63  % (4391)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 1.99/0.65  % (4392)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.17/0.66  % (4332)Refutation not found, incomplete strategy% (4332)------------------------------
% 2.17/0.66  % (4332)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.66  % (4332)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.66  
% 2.17/0.66  % (4332)Memory used [KB]: 6140
% 2.17/0.66  % (4332)Time elapsed: 0.253 s
% 2.17/0.66  % (4332)------------------------------
% 2.17/0.66  % (4332)------------------------------
% 2.17/0.67  % (4392)Refutation not found, incomplete strategy% (4392)------------------------------
% 2.17/0.67  % (4392)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.67  % (4392)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.67  
% 2.17/0.67  % (4395)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_171 on theBenchmark
% 2.17/0.67  % (4392)Memory used [KB]: 6140
% 2.17/0.67  % (4392)Time elapsed: 0.111 s
% 2.17/0.67  % (4392)------------------------------
% 2.17/0.67  % (4392)------------------------------
% 2.17/0.67  % (4395)Refutation not found, incomplete strategy% (4395)------------------------------
% 2.17/0.67  % (4395)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.67  % (4395)Termination reason: Refutation not found, incomplete strategy
% 2.17/0.67  
% 2.17/0.67  % (4395)Memory used [KB]: 10618
% 2.17/0.67  % (4395)Time elapsed: 0.070 s
% 2.17/0.67  % (4395)------------------------------
% 2.17/0.67  % (4395)------------------------------
% 2.17/0.68  % (4394)lrs-1_14_add=off:afr=on:afp=40000:afq=1.4:amm=sco:anc=none:bd=off:br=off:cond=fast:fde=unused:gs=on:lcm=reverse:lma=on:nwc=1:stl=30:sos=on:urr=on:updr=off_25 on theBenchmark
% 2.17/0.69  % (4396)dis+1010_3:2_av=off:lma=on:nm=2:newcnf=on:nwc=1:sd=3:ss=axioms:st=5.0:sos=all:sp=reverse_arity:updr=off_99 on theBenchmark
% 2.17/0.71  % (4397)lrs+10_2_afp=40000:afq=1.0:amm=sco:anc=none:bsr=on:br=off:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=3.0:sos=all:sac=on:sp=occurrence:urr=on:updr=off_3 on theBenchmark
% 2.17/0.71  % (4398)dis+1002_1_av=off:bsr=on:cond=on:lma=on:nwc=2:sd=3:ss=axioms:st=3.0:updr=off_24 on theBenchmark
% 2.62/0.73  % (4399)lrs+1002_2:1_aac=none:afr=on:afp=1000:afq=1.2:anc=all:bd=preordered:bsr=on:cond=fast:gsp=input_only:gs=on:nm=0:nwc=2.5:nicw=on:sas=z3:stl=30:sd=4:ss=axioms:st=2.0:sos=on:sac=on:urr=on:updr=off:uhcvi=on_22 on theBenchmark
% 2.86/0.77  % (4350)Refutation found. Thanks to Tanya!
% 2.86/0.77  % SZS status Theorem for theBenchmark
% 2.86/0.77  % SZS output start Proof for theBenchmark
% 2.86/0.77  fof(f3913,plain,(
% 2.86/0.77    $false),
% 2.86/0.77    inference(avatar_sat_refutation,[],[f89,f90,f91,f1134,f1139,f1165,f1167,f2429,f2711,f2900,f2995,f3073,f3087,f3131,f3205,f3216,f3912])).
% 2.86/0.77  fof(f3912,plain,(
% 2.86/0.77    spl3_1 | ~spl3_15 | ~spl3_37),
% 2.86/0.77    inference(avatar_contradiction_clause,[],[f3911])).
% 2.86/0.77  fof(f3911,plain,(
% 2.86/0.77    $false | (spl3_1 | ~spl3_15 | ~spl3_37)),
% 2.86/0.77    inference(subsumption_resolution,[],[f3910,f80])).
% 2.86/0.77  fof(f80,plain,(
% 2.86/0.77    k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2) | spl3_1),
% 2.86/0.77    inference(avatar_component_clause,[],[f78])).
% 2.86/0.77  fof(f78,plain,(
% 2.86/0.77    spl3_1 <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.86/0.77  fof(f3910,plain,(
% 2.86/0.77    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | (~spl3_15 | ~spl3_37)),
% 2.86/0.77    inference(forward_demodulation,[],[f3909,f1212])).
% 2.86/0.77  fof(f1212,plain,(
% 2.86/0.77    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_15),
% 2.86/0.77    inference(avatar_component_clause,[],[f1210])).
% 2.86/0.77  fof(f1210,plain,(
% 2.86/0.77    spl3_15 <=> k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.86/0.77  fof(f3909,plain,(
% 2.86/0.77    k4_xboole_0(k2_tarski(sK0,sK1),sK2) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_37),
% 2.86/0.77    inference(forward_demodulation,[],[f3908,f126])).
% 2.86/0.77  fof(f126,plain,(
% 2.86/0.77    ( ! [X4,X3] : (k4_xboole_0(X3,X4) = k5_xboole_0(X3,k3_xboole_0(X4,X3))) )),
% 2.86/0.77    inference(superposition,[],[f63,f65])).
% 2.86/0.77  fof(f65,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f1])).
% 2.86/0.77  fof(f1,axiom,(
% 2.86/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.86/0.77  fof(f63,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.86/0.77    inference(cnf_transformation,[],[f7])).
% 2.86/0.77  fof(f7,axiom,(
% 2.86/0.77    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).
% 2.86/0.77  fof(f3908,plain,(
% 2.86/0.77    k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) = k5_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_37),
% 2.86/0.77    inference(forward_demodulation,[],[f3873,f64])).
% 2.86/0.77  fof(f64,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f2])).
% 2.86/0.77  fof(f2,axiom,(
% 2.86/0.77    ! [X0,X1] : k5_xboole_0(X0,X1) = k5_xboole_0(X1,X0)),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).
% 2.86/0.77  fof(f3873,plain,(
% 2.86/0.77    k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) = k5_xboole_0(k3_xboole_0(sK2,k2_tarski(sK0,sK1)),k2_tarski(sK0,sK1)) | ~spl3_37),
% 2.86/0.77    inference(superposition,[],[f2904,f3209])).
% 2.86/0.77  fof(f3209,plain,(
% 2.86/0.77    k3_xboole_0(sK2,k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_37),
% 2.86/0.77    inference(avatar_component_clause,[],[f3207])).
% 2.86/0.77  fof(f3207,plain,(
% 2.86/0.77    spl3_37 <=> k3_xboole_0(sK2,k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.86/0.77  fof(f2904,plain,(
% 2.86/0.77    ( ! [X6,X5] : (k4_xboole_0(X6,X5) = k5_xboole_0(k3_xboole_0(X6,X5),X6)) )),
% 2.86/0.77    inference(superposition,[],[f2820,f65])).
% 2.86/0.77  fof(f2820,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(k3_xboole_0(X1,X0),X0)) )),
% 2.86/0.77    inference(backward_demodulation,[],[f211,f546])).
% 2.86/0.77  fof(f546,plain,(
% 2.86/0.77    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k3_xboole_0(X2,k5_xboole_0(X3,X2))) )),
% 2.86/0.77    inference(superposition,[],[f529,f64])).
% 2.86/0.77  fof(f529,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.86/0.77    inference(forward_demodulation,[],[f210,f126])).
% 2.86/0.77  fof(f210,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k5_xboole_0(X0,k3_xboole_0(X1,X0)) = k3_xboole_0(X0,k5_xboole_0(X0,X1))) )),
% 2.86/0.77    inference(forward_demodulation,[],[f191,f65])).
% 2.86/0.77  fof(f191,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X0,X1),X0) = k5_xboole_0(X0,k3_xboole_0(X1,X0))) )),
% 2.86/0.77    inference(superposition,[],[f56,f67])).
% 2.86/0.77  fof(f67,plain,(
% 2.86/0.77    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 2.86/0.77    inference(cnf_transformation,[],[f27])).
% 2.86/0.77  fof(f27,plain,(
% 2.86/0.77    ! [X0] : k3_xboole_0(X0,X0) = X0),
% 2.86/0.77    inference(rectify,[],[f3])).
% 2.86/0.77  fof(f3,axiom,(
% 2.86/0.77    ! [X0,X1] : k3_xboole_0(X0,X0) = X0),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).
% 2.86/0.77  fof(f56,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f8])).
% 2.86/0.77  fof(f8,axiom,(
% 2.86/0.77    ! [X0,X1,X2] : k5_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X2,X1)) = k3_xboole_0(k5_xboole_0(X0,X2),X1)),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).
% 2.86/0.77  fof(f211,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k5_xboole_0(k3_xboole_0(X1,X0),X0) = k3_xboole_0(X0,k5_xboole_0(X1,X0))) )),
% 2.86/0.77    inference(forward_demodulation,[],[f195,f65])).
% 2.86/0.77  fof(f195,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k3_xboole_0(k5_xboole_0(X1,X0),X0) = k5_xboole_0(k3_xboole_0(X1,X0),X0)) )),
% 2.86/0.77    inference(superposition,[],[f56,f67])).
% 2.86/0.77  fof(f3216,plain,(
% 2.86/0.77    spl3_37 | ~spl3_13),
% 2.86/0.77    inference(avatar_split_clause,[],[f3215,f1196,f3207])).
% 2.86/0.77  fof(f1196,plain,(
% 2.86/0.77    spl3_13 <=> k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.86/0.77  fof(f3215,plain,(
% 2.86/0.77    k3_xboole_0(sK2,k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_13),
% 2.86/0.77    inference(forward_demodulation,[],[f3214,f1198])).
% 2.86/0.77  fof(f1198,plain,(
% 2.86/0.77    k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl3_13),
% 2.86/0.77    inference(avatar_component_clause,[],[f1196])).
% 2.86/0.77  fof(f3214,plain,(
% 2.86/0.77    k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_13),
% 2.86/0.77    inference(forward_demodulation,[],[f3198,f124])).
% 2.86/0.77  fof(f124,plain,(
% 2.86/0.77    ( ! [X0] : (k4_xboole_0(X0,X0) = k5_xboole_0(X0,X0)) )),
% 2.86/0.77    inference(superposition,[],[f63,f67])).
% 2.86/0.77  fof(f3198,plain,(
% 2.86/0.77    k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_13),
% 2.86/0.77    inference(superposition,[],[f546,f1198])).
% 2.86/0.77  fof(f3205,plain,(
% 2.86/0.77    spl3_15 | ~spl3_13),
% 2.86/0.77    inference(avatar_split_clause,[],[f3174,f1196,f1210])).
% 2.86/0.77  fof(f3174,plain,(
% 2.86/0.77    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_13),
% 2.86/0.77    inference(superposition,[],[f237,f1198])).
% 2.86/0.77  fof(f237,plain,(
% 2.86/0.77    ( ! [X1] : (k4_xboole_0(X1,k5_xboole_0(X1,X1)) = X1) )),
% 2.86/0.77    inference(forward_demodulation,[],[f233,f67])).
% 2.86/0.77  fof(f233,plain,(
% 2.86/0.77    ( ! [X1] : (k3_xboole_0(X1,X1) = k4_xboole_0(X1,k5_xboole_0(X1,X1))) )),
% 2.86/0.77    inference(superposition,[],[f62,f124])).
% 2.86/0.77  fof(f62,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.86/0.77    inference(cnf_transformation,[],[f11])).
% 2.86/0.77  fof(f11,axiom,(
% 2.86/0.77    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.86/0.77  fof(f3131,plain,(
% 2.86/0.77    spl3_13 | ~spl3_6),
% 2.86/0.77    inference(avatar_split_clause,[],[f3130,f1131,f1196])).
% 2.86/0.77  fof(f1131,plain,(
% 2.86/0.77    spl3_6 <=> k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1))),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.86/0.77  fof(f3130,plain,(
% 2.86/0.77    k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl3_6),
% 2.86/0.77    inference(subsumption_resolution,[],[f3100,f75])).
% 2.86/0.77  fof(f75,plain,(
% 2.86/0.77    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.86/0.77    inference(equality_resolution,[],[f59])).
% 2.86/0.77  fof(f59,plain,(
% 2.86/0.77    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.86/0.77    inference(cnf_transformation,[],[f43])).
% 2.86/0.77  fof(f43,plain,(
% 2.86/0.77    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.86/0.77    inference(flattening,[],[f42])).
% 2.86/0.77  fof(f42,plain,(
% 2.86/0.77    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.86/0.77    inference(nnf_transformation,[],[f6])).
% 2.86/0.77  fof(f6,axiom,(
% 2.86/0.77    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.86/0.77  fof(f3100,plain,(
% 2.86/0.77    k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~r1_tarski(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) | ~spl3_6),
% 2.86/0.77    inference(superposition,[],[f125,f1133])).
% 2.86/0.77  fof(f1133,plain,(
% 2.86/0.77    k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl3_6),
% 2.86/0.77    inference(avatar_component_clause,[],[f1131])).
% 2.86/0.77  fof(f125,plain,(
% 2.86/0.77    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = k5_xboole_0(X1,X1) | ~r1_tarski(X1,X2)) )),
% 2.86/0.77    inference(superposition,[],[f63,f61])).
% 2.86/0.77  fof(f61,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f33])).
% 2.86/0.77  fof(f33,plain,(
% 2.86/0.77    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 2.86/0.77    inference(ennf_transformation,[],[f9])).
% 2.86/0.77  fof(f9,axiom,(
% 2.86/0.77    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 2.86/0.77  fof(f3087,plain,(
% 2.86/0.77    spl3_3 | ~spl3_16),
% 2.86/0.77    inference(avatar_contradiction_clause,[],[f3086])).
% 2.86/0.77  fof(f3086,plain,(
% 2.86/0.77    $false | (spl3_3 | ~spl3_16)),
% 2.86/0.77    inference(subsumption_resolution,[],[f3085,f238])).
% 2.86/0.77  fof(f238,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X2,X0)))) )),
% 2.86/0.77    inference(resolution,[],[f103,f92])).
% 2.86/0.77  fof(f92,plain,(
% 2.86/0.77    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.86/0.77    inference(resolution,[],[f70,f68])).
% 2.86/0.77  fof(f68,plain,(
% 2.86/0.77    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f13])).
% 2.86/0.77  fof(f13,axiom,(
% 2.86/0.77    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.86/0.77  fof(f70,plain,(
% 2.86/0.77    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f34])).
% 2.86/0.77  fof(f34,plain,(
% 2.86/0.77    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.86/0.77    inference(ennf_transformation,[],[f4])).
% 2.86/0.77  fof(f4,axiom,(
% 2.86/0.77    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.86/0.77  fof(f103,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X1,X0),X2) | ~r2_hidden(X0,X2)) )),
% 2.86/0.77    inference(superposition,[],[f47,f66])).
% 2.86/0.77  fof(f66,plain,(
% 2.86/0.77    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f15])).
% 2.86/0.77  fof(f15,axiom,(
% 2.86/0.77    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 2.86/0.77  fof(f47,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (~r1_xboole_0(k2_tarski(X0,X1),X2) | ~r2_hidden(X0,X2)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f29])).
% 2.86/0.77  fof(f29,plain,(
% 2.86/0.77    ! [X0,X1,X2] : (~r2_hidden(X0,X2) | ~r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.86/0.77    inference(ennf_transformation,[],[f24])).
% 2.86/0.77  fof(f24,axiom,(
% 2.86/0.77    ! [X0,X1,X2] : ~(r2_hidden(X0,X2) & r1_xboole_0(k2_tarski(X0,X1),X2))),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).
% 2.86/0.77  fof(f3085,plain,(
% 2.86/0.77    r2_hidden(sK1,k4_xboole_0(sK2,k2_tarski(sK0,sK1))) | (spl3_3 | ~spl3_16)),
% 2.86/0.77    inference(subsumption_resolution,[],[f3080,f87])).
% 2.86/0.77  fof(f87,plain,(
% 2.86/0.77    ~r2_hidden(sK1,sK2) | spl3_3),
% 2.86/0.77    inference(avatar_component_clause,[],[f86])).
% 2.86/0.77  fof(f86,plain,(
% 2.86/0.77    spl3_3 <=> r2_hidden(sK1,sK2)),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.86/0.77  fof(f3080,plain,(
% 2.86/0.77    r2_hidden(sK1,sK2) | r2_hidden(sK1,k4_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_16),
% 2.86/0.77    inference(resolution,[],[f1322,f165])).
% 2.86/0.77  fof(f165,plain,(
% 2.86/0.77    ( ! [X10,X8,X9] : (~r2_hidden(X10,k3_xboole_0(X8,X9)) | r2_hidden(X10,X8) | r2_hidden(X10,k4_xboole_0(X8,X9))) )),
% 2.86/0.77    inference(superposition,[],[f54,f63])).
% 2.86/0.77  fof(f54,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f41])).
% 2.86/0.77  fof(f41,plain,(
% 2.86/0.77    ! [X0,X1,X2] : ((r2_hidden(X0,k5_xboole_0(X1,X2)) | ((r2_hidden(X0,X1) | ~r2_hidden(X0,X2)) & (r2_hidden(X0,X2) | ~r2_hidden(X0,X1)))) & (((~r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X2) | r2_hidden(X0,X1))) | ~r2_hidden(X0,k5_xboole_0(X1,X2))))),
% 2.86/0.77    inference(nnf_transformation,[],[f30])).
% 2.86/0.77  fof(f30,plain,(
% 2.86/0.77    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> (r2_hidden(X0,X1) <~> r2_hidden(X0,X2)))),
% 2.86/0.77    inference(ennf_transformation,[],[f5])).
% 2.86/0.77  fof(f5,axiom,(
% 2.86/0.77    ! [X0,X1,X2] : (r2_hidden(X0,k5_xboole_0(X1,X2)) <=> ~(r2_hidden(X0,X1) <=> r2_hidden(X0,X2)))),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).
% 2.86/0.77  fof(f1322,plain,(
% 2.86/0.77    r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_16),
% 2.86/0.77    inference(avatar_component_clause,[],[f1321])).
% 2.86/0.77  fof(f1321,plain,(
% 2.86/0.77    spl3_16 <=> r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.86/0.77  fof(f3073,plain,(
% 2.86/0.77    spl3_16 | spl3_36),
% 2.86/0.77    inference(avatar_split_clause,[],[f3070,f2708,f1321])).
% 2.86/0.77  fof(f2708,plain,(
% 2.86/0.77    spl3_36 <=> r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.86/0.77  fof(f3070,plain,(
% 2.86/0.77    r2_hidden(sK1,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_36),
% 2.86/0.77    inference(forward_demodulation,[],[f3069,f65])).
% 2.86/0.77  fof(f3069,plain,(
% 2.86/0.77    r2_hidden(sK1,k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_36),
% 2.86/0.77    inference(subsumption_resolution,[],[f3068,f108])).
% 2.86/0.77  fof(f108,plain,(
% 2.86/0.77    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 2.86/0.77    inference(resolution,[],[f49,f75])).
% 2.86/0.77  fof(f49,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X1,X2)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f40])).
% 2.86/0.77  fof(f40,plain,(
% 2.86/0.77    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.86/0.77    inference(flattening,[],[f39])).
% 2.86/0.77  fof(f39,plain,(
% 2.86/0.77    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 2.86/0.77    inference(nnf_transformation,[],[f22])).
% 2.86/0.77  fof(f22,axiom,(
% 2.86/0.77    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 2.86/0.77  fof(f3068,plain,(
% 2.86/0.77    r2_hidden(sK1,k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~r2_hidden(sK1,k2_tarski(sK0,sK1)) | spl3_36),
% 2.86/0.77    inference(resolution,[],[f2710,f155])).
% 2.86/0.77  fof(f155,plain,(
% 2.86/0.77    ( ! [X10,X8,X9] : (r2_hidden(X10,k4_xboole_0(X8,X9)) | r2_hidden(X10,k3_xboole_0(X8,X9)) | ~r2_hidden(X10,X8)) )),
% 2.86/0.77    inference(superposition,[],[f53,f63])).
% 2.86/0.77  fof(f53,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (r2_hidden(X0,k5_xboole_0(X1,X2)) | r2_hidden(X0,X2) | ~r2_hidden(X0,X1)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f41])).
% 2.86/0.77  fof(f2710,plain,(
% 2.86/0.77    ~r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_36),
% 2.86/0.77    inference(avatar_component_clause,[],[f2708])).
% 2.86/0.77  fof(f2995,plain,(
% 2.86/0.77    spl3_2 | ~spl3_14),
% 2.86/0.77    inference(avatar_contradiction_clause,[],[f2994])).
% 2.86/0.77  fof(f2994,plain,(
% 2.86/0.77    $false | (spl3_2 | ~spl3_14)),
% 2.86/0.77    inference(subsumption_resolution,[],[f2993,f102])).
% 2.86/0.77  fof(f102,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (~r2_hidden(X0,k4_xboole_0(X1,k2_tarski(X0,X2)))) )),
% 2.86/0.77    inference(resolution,[],[f47,f92])).
% 2.86/0.77  fof(f2993,plain,(
% 2.86/0.77    r2_hidden(sK0,k4_xboole_0(sK2,k2_tarski(sK0,sK1))) | (spl3_2 | ~spl3_14)),
% 2.86/0.77    inference(subsumption_resolution,[],[f2988,f83])).
% 2.86/0.77  fof(f83,plain,(
% 2.86/0.77    ~r2_hidden(sK0,sK2) | spl3_2),
% 2.86/0.77    inference(avatar_component_clause,[],[f82])).
% 2.86/0.77  fof(f82,plain,(
% 2.86/0.77    spl3_2 <=> r2_hidden(sK0,sK2)),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.86/0.77  fof(f2988,plain,(
% 2.86/0.77    r2_hidden(sK0,sK2) | r2_hidden(sK0,k4_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_14),
% 2.86/0.77    inference(resolution,[],[f1204,f165])).
% 2.86/0.77  fof(f1204,plain,(
% 2.86/0.77    r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | ~spl3_14),
% 2.86/0.77    inference(avatar_component_clause,[],[f1203])).
% 2.86/0.77  fof(f1203,plain,(
% 2.86/0.77    spl3_14 <=> r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1)))),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.86/0.77  fof(f2900,plain,(
% 2.86/0.77    spl3_14 | spl3_35),
% 2.86/0.77    inference(avatar_split_clause,[],[f2897,f2704,f1203])).
% 2.86/0.77  fof(f2704,plain,(
% 2.86/0.77    spl3_35 <=> r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 2.86/0.77  fof(f2897,plain,(
% 2.86/0.77    r2_hidden(sK0,k3_xboole_0(sK2,k2_tarski(sK0,sK1))) | spl3_35),
% 2.86/0.77    inference(forward_demodulation,[],[f2896,f65])).
% 2.86/0.77  fof(f2896,plain,(
% 2.86/0.77    r2_hidden(sK0,k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_35),
% 2.86/0.77    inference(subsumption_resolution,[],[f2895,f105])).
% 2.86/0.77  fof(f105,plain,(
% 2.86/0.77    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 2.86/0.77    inference(resolution,[],[f48,f75])).
% 2.86/0.77  fof(f48,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (~r1_tarski(k2_tarski(X0,X1),X2) | r2_hidden(X0,X2)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f40])).
% 2.86/0.77  fof(f2895,plain,(
% 2.86/0.77    r2_hidden(sK0,k3_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~r2_hidden(sK0,k2_tarski(sK0,sK1)) | spl3_35),
% 2.86/0.77    inference(resolution,[],[f2706,f155])).
% 2.86/0.77  fof(f2706,plain,(
% 2.86/0.77    ~r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_35),
% 2.86/0.77    inference(avatar_component_clause,[],[f2704])).
% 2.86/0.77  fof(f2711,plain,(
% 2.86/0.77    ~spl3_35 | ~spl3_36 | spl3_25),
% 2.86/0.77    inference(avatar_split_clause,[],[f2702,f2426,f2708,f2704])).
% 2.86/0.77  fof(f2426,plain,(
% 2.86/0.77    spl3_25 <=> r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 2.86/0.77  fof(f2702,plain,(
% 2.86/0.77    ~r2_hidden(sK1,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | ~r2_hidden(sK0,k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_25),
% 2.86/0.77    inference(resolution,[],[f2428,f50])).
% 2.86/0.77  fof(f50,plain,(
% 2.86/0.77    ( ! [X2,X0,X1] : (r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 2.86/0.77    inference(cnf_transformation,[],[f40])).
% 2.86/0.77  fof(f2428,plain,(
% 2.86/0.77    ~r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_25),
% 2.86/0.77    inference(avatar_component_clause,[],[f2426])).
% 2.86/0.77  fof(f2429,plain,(
% 2.86/0.77    ~spl3_25 | spl3_13),
% 2.86/0.77    inference(avatar_split_clause,[],[f2424,f1196,f2426])).
% 2.86/0.77  fof(f2424,plain,(
% 2.86/0.77    ~r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),sK2)) | spl3_13),
% 2.86/0.77    inference(equality_resolution,[],[f1669])).
% 2.86/0.77  fof(f1669,plain,(
% 2.86/0.77    ( ! [X3] : (k3_xboole_0(sK2,k2_tarski(sK0,sK1)) != k3_xboole_0(X3,k2_tarski(sK0,sK1)) | ~r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),X3))) ) | spl3_13),
% 2.86/0.77    inference(superposition,[],[f1606,f65])).
% 2.86/0.77  fof(f1606,plain,(
% 2.86/0.77    ( ! [X2] : (k3_xboole_0(sK2,k2_tarski(sK0,sK1)) != k3_xboole_0(k2_tarski(sK0,sK1),X2) | ~r1_tarski(k2_tarski(sK0,sK1),k4_xboole_0(k2_tarski(sK0,sK1),X2))) ) | spl3_13),
% 2.86/0.77    inference(superposition,[],[f1602,f62])).
% 2.86/0.77  fof(f1602,plain,(
% 2.86/0.77    ( ! [X0] : (k3_xboole_0(sK2,k2_tarski(sK0,sK1)) != k4_xboole_0(k2_tarski(sK0,sK1),X0) | ~r1_tarski(k2_tarski(sK0,sK1),X0)) ) | spl3_13),
% 2.86/0.77    inference(superposition,[],[f1197,f125])).
% 2.86/0.77  fof(f1197,plain,(
% 2.86/0.77    k5_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) != k3_xboole_0(sK2,k2_tarski(sK0,sK1)) | spl3_13),
% 2.86/0.77    inference(avatar_component_clause,[],[f1196])).
% 2.86/0.77  fof(f1167,plain,(
% 2.86/0.77    ~spl3_2 | ~spl3_7),
% 2.86/0.77    inference(avatar_split_clause,[],[f1160,f1136,f82])).
% 2.86/0.77  fof(f1136,plain,(
% 2.86/0.77    spl3_7 <=> r1_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.86/0.77    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 2.86/0.77  fof(f1160,plain,(
% 2.86/0.77    ~r2_hidden(sK0,sK2) | ~spl3_7),
% 2.86/0.77    inference(resolution,[],[f1138,f47])).
% 2.86/0.77  fof(f1138,plain,(
% 2.86/0.77    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_7),
% 2.86/0.77    inference(avatar_component_clause,[],[f1136])).
% 2.86/0.77  fof(f1165,plain,(
% 2.86/0.77    ~spl3_3 | ~spl3_7),
% 2.86/0.77    inference(avatar_split_clause,[],[f1159,f1136,f86])).
% 2.86/0.77  fof(f1159,plain,(
% 2.86/0.77    ~r2_hidden(sK1,sK2) | ~spl3_7),
% 2.86/0.77    inference(resolution,[],[f1138,f103])).
% 2.86/0.77  fof(f1139,plain,(
% 2.86/0.77    spl3_7 | ~spl3_1),
% 2.86/0.77    inference(avatar_split_clause,[],[f1121,f78,f1136])).
% 2.86/0.77  fof(f1121,plain,(
% 2.86/0.77    r1_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_1),
% 2.86/0.77    inference(superposition,[],[f68,f79])).
% 2.86/0.77  fof(f79,plain,(
% 2.86/0.77    k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2) | ~spl3_1),
% 2.86/0.77    inference(avatar_component_clause,[],[f78])).
% 2.86/0.77  fof(f1134,plain,(
% 2.86/0.77    spl3_6 | ~spl3_1),
% 2.86/0.77    inference(avatar_split_clause,[],[f1129,f78,f1131])).
% 2.86/0.77  fof(f1129,plain,(
% 2.86/0.77    k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) = k3_xboole_0(sK2,k2_tarski(sK0,sK1)) | ~spl3_1),
% 2.86/0.77    inference(forward_demodulation,[],[f1120,f65])).
% 2.86/0.77  fof(f1120,plain,(
% 2.86/0.77    k3_xboole_0(k2_tarski(sK0,sK1),sK2) = k4_xboole_0(k2_tarski(sK0,sK1),k2_tarski(sK0,sK1)) | ~spl3_1),
% 2.86/0.77    inference(superposition,[],[f62,f79])).
% 2.86/0.77  fof(f91,plain,(
% 2.86/0.77    spl3_1 | ~spl3_2),
% 2.86/0.77    inference(avatar_split_clause,[],[f44,f82,f78])).
% 2.86/0.77  fof(f44,plain,(
% 2.86/0.77    ~r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.86/0.77    inference(cnf_transformation,[],[f38])).
% 2.86/0.77  fof(f38,plain,(
% 2.86/0.77    (r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2))),
% 2.86/0.77    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f37])).
% 2.86/0.77  fof(f37,plain,(
% 2.86/0.77    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2))) => ((r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)) & ((~r2_hidden(sK1,sK2) & ~r2_hidden(sK0,sK2)) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)))),
% 2.86/0.77    introduced(choice_axiom,[])).
% 2.86/0.77  fof(f36,plain,(
% 2.86/0.77    ? [X0,X1,X2] : ((r2_hidden(X1,X2) | r2_hidden(X0,X2) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.86/0.77    inference(flattening,[],[f35])).
% 2.86/0.77  fof(f35,plain,(
% 2.86/0.77    ? [X0,X1,X2] : (((r2_hidden(X1,X2) | r2_hidden(X0,X2)) | k2_tarski(X0,X1) != k4_xboole_0(k2_tarski(X0,X1),X2)) & ((~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)) | k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2)))),
% 2.86/0.77    inference(nnf_transformation,[],[f28])).
% 2.86/0.77  fof(f28,plain,(
% 2.86/0.77    ? [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <~> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.86/0.77    inference(ennf_transformation,[],[f26])).
% 2.86/0.77  fof(f26,negated_conjecture,(
% 2.86/0.77    ~! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.86/0.77    inference(negated_conjecture,[],[f25])).
% 2.86/0.77  fof(f25,conjecture,(
% 2.86/0.77    ! [X0,X1,X2] : (k2_tarski(X0,X1) = k4_xboole_0(k2_tarski(X0,X1),X2) <=> (~r2_hidden(X1,X2) & ~r2_hidden(X0,X2)))),
% 2.86/0.77    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_zfmisc_1)).
% 2.86/0.77  fof(f90,plain,(
% 2.86/0.77    spl3_1 | ~spl3_3),
% 2.86/0.77    inference(avatar_split_clause,[],[f45,f86,f78])).
% 2.86/0.77  fof(f45,plain,(
% 2.86/0.77    ~r2_hidden(sK1,sK2) | k2_tarski(sK0,sK1) = k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.86/0.77    inference(cnf_transformation,[],[f38])).
% 2.86/0.77  fof(f89,plain,(
% 2.86/0.77    ~spl3_1 | spl3_2 | spl3_3),
% 2.86/0.77    inference(avatar_split_clause,[],[f46,f86,f82,f78])).
% 2.86/0.77  fof(f46,plain,(
% 2.86/0.77    r2_hidden(sK1,sK2) | r2_hidden(sK0,sK2) | k2_tarski(sK0,sK1) != k4_xboole_0(k2_tarski(sK0,sK1),sK2)),
% 2.86/0.77    inference(cnf_transformation,[],[f38])).
% 2.86/0.77  % SZS output end Proof for theBenchmark
% 2.86/0.77  % (4350)------------------------------
% 2.86/0.77  % (4350)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.86/0.77  % (4350)Termination reason: Refutation
% 2.86/0.77  
% 2.86/0.77  % (4350)Memory used [KB]: 8699
% 2.86/0.77  % (4350)Time elapsed: 0.361 s
% 2.86/0.77  % (4350)------------------------------
% 2.86/0.77  % (4350)------------------------------
% 2.86/0.78  % (4328)Success in time 0.403 s
%------------------------------------------------------------------------------
