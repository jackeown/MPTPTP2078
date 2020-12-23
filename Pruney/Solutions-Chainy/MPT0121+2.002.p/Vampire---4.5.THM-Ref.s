%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:32:56 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 183 expanded)
%              Number of leaves         :   24 (  74 expanded)
%              Depth                    :   10
%              Number of atoms          :  207 ( 419 expanded)
%              Number of equality atoms :   45 (  90 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1839,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f66,f78,f90,f97,f104,f111,f166,f181,f1727,f1737,f1771,f1838])).

fof(f1838,plain,
    ( spl4_1
    | ~ spl4_139 ),
    inference(avatar_split_clause,[],[f1832,f1768,f36])).

fof(f36,plain,
    ( spl4_1
  <=> r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1768,plain,
    ( spl4_139
  <=> r1_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).

fof(f1832,plain,
    ( r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3)
    | ~ spl4_139 ),
    inference(resolution,[],[f1770,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f1770,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl4_139 ),
    inference(avatar_component_clause,[],[f1768])).

fof(f1771,plain,
    ( spl4_139
    | ~ spl4_20
    | ~ spl4_135 ),
    inference(avatar_split_clause,[],[f1760,f1734,f163,f1768])).

fof(f163,plain,
    ( spl4_20
  <=> sK3 = k4_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f1734,plain,
    ( spl4_135
  <=> k1_xboole_0 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).

fof(f1760,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl4_20
    | ~ spl4_135 ),
    inference(trivial_inequality_removal,[],[f1755])).

fof(f1755,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)))
    | ~ spl4_20
    | ~ spl4_135 ),
    inference(superposition,[],[f788,f1736])).

fof(f1736,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_135 ),
    inference(avatar_component_clause,[],[f1734])).

fof(f788,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(sK3,X0)
        | r1_xboole_0(sK3,k2_xboole_0(sK2,X0)) )
    | ~ spl4_20 ),
    inference(superposition,[],[f32,f478])).

fof(f478,plain,
    ( ! [X3] : k3_xboole_0(sK3,k2_xboole_0(sK2,X3)) = k3_xboole_0(sK3,X3)
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f475,f26])).

fof(f26,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f475,plain,
    ( ! [X3] : k3_xboole_0(sK3,k2_xboole_0(sK2,X3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,X3))
    | ~ spl4_20 ),
    inference(superposition,[],[f26,f247])).

fof(f247,plain,
    ( ! [X0] : k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,X0)
    | ~ spl4_20 ),
    inference(superposition,[],[f33,f165])).

fof(f165,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f163])).

fof(f33,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f1737,plain,
    ( spl4_135
    | ~ spl4_134 ),
    inference(avatar_split_clause,[],[f1731,f1724,f1734])).

fof(f1724,plain,
    ( spl4_134
  <=> r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).

fof(f1731,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_134 ),
    inference(resolution,[],[f1726,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1726,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_134 ),
    inference(avatar_component_clause,[],[f1724])).

fof(f1727,plain,
    ( spl4_134
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(avatar_split_clause,[],[f1722,f178,f108,f1724])).

fof(f108,plain,
    ( spl4_13
  <=> k1_xboole_0 = k3_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f178,plain,
    ( spl4_22
  <=> sK3 = k4_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f1722,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f1697,f25])).

fof(f25,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1697,plain,
    ( r1_xboole_0(sK3,k2_xboole_0(sK1,sK0))
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(trivial_inequality_removal,[],[f1689])).

fof(f1689,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(sK3,k2_xboole_0(sK1,sK0))
    | ~ spl4_13
    | ~ spl4_22 ),
    inference(superposition,[],[f817,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK0)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f108])).

fof(f817,plain,
    ( ! [X0] :
        ( k1_xboole_0 != k3_xboole_0(sK3,X0)
        | r1_xboole_0(sK3,k2_xboole_0(sK1,X0)) )
    | ~ spl4_22 ),
    inference(superposition,[],[f32,f486])).

fof(f486,plain,
    ( ! [X3] : k3_xboole_0(sK3,X3) = k3_xboole_0(sK3,k2_xboole_0(sK1,X3))
    | ~ spl4_22 ),
    inference(forward_demodulation,[],[f483,f26])).

fof(f483,plain,
    ( ! [X3] : k4_xboole_0(sK3,k4_xboole_0(sK3,X3)) = k3_xboole_0(sK3,k2_xboole_0(sK1,X3))
    | ~ spl4_22 ),
    inference(superposition,[],[f26,f261])).

fof(f261,plain,
    ( ! [X0] : k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(sK1,X0))
    | ~ spl4_22 ),
    inference(superposition,[],[f33,f180])).

fof(f180,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f178])).

fof(f181,plain,
    ( spl4_22
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f176,f101,f178])).

fof(f101,plain,
    ( spl4_12
  <=> k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f176,plain,
    ( sK3 = k4_xboole_0(sK3,sK1)
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f173,f24])).

fof(f24,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f173,plain,
    ( k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1)
    | ~ spl4_12 ),
    inference(superposition,[],[f29,f103])).

fof(f103,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f101])).

fof(f29,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f166,plain,
    ( spl4_20
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f161,f94,f163])).

fof(f94,plain,
    ( spl4_11
  <=> k1_xboole_0 = k3_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f161,plain,
    ( sK3 = k4_xboole_0(sK3,sK2)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f158,f24])).

fof(f158,plain,
    ( k4_xboole_0(sK3,sK2) = k4_xboole_0(sK3,k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f29,f96])).

fof(f96,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK2)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f94])).

fof(f111,plain,
    ( spl4_13
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f105,f87,f108])).

fof(f87,plain,
    ( spl4_10
  <=> r1_xboole_0(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f105,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK0)
    | ~ spl4_10 ),
    inference(resolution,[],[f89,f31])).

fof(f89,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f87])).

fof(f104,plain,
    ( spl4_12
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f98,f75,f101])).

fof(f75,plain,
    ( spl4_8
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f98,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK1)
    | ~ spl4_8 ),
    inference(resolution,[],[f77,f31])).

fof(f77,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f75])).

fof(f97,plain,
    ( spl4_11
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f91,f63,f94])).

fof(f63,plain,
    ( spl4_6
  <=> r1_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f91,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK2)
    | ~ spl4_6 ),
    inference(resolution,[],[f65,f31])).

fof(f65,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f63])).

fof(f90,plain,
    ( spl4_10
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f80,f51,f87])).

fof(f51,plain,
    ( spl4_4
  <=> r1_xboole_0(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f80,plain,
    ( r1_xboole_0(sK3,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f53,f30])).

fof(f53,plain,
    ( r1_xboole_0(sK0,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f78,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f68,f46,f75])).

fof(f46,plain,
    ( spl4_3
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f68,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f48,f30])).

fof(f48,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f46])).

fof(f66,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f56,f41,f63])).

fof(f41,plain,
    ( spl4_2
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f56,plain,
    ( r1_xboole_0(sK3,sK2)
    | ~ spl4_2 ),
    inference(resolution,[],[f43,f30])).

fof(f43,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f41])).

fof(f54,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f19,f51])).

fof(f19,plain,(
    r1_xboole_0(sK0,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,
    ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
    & r1_xboole_0(sK2,sK3)
    & r1_xboole_0(sK1,sK3)
    & r1_xboole_0(sK0,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f16])).

fof(f16,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
        & r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
   => ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)
      & r1_xboole_0(sK2,sK3)
      & r1_xboole_0(sK1,sK3)
      & r1_xboole_0(sK0,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3)
      & r1_xboole_0(X2,X3)
      & r1_xboole_0(X1,X3)
      & r1_xboole_0(X0,X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X3)
          & r1_xboole_0(X1,X3)
          & r1_xboole_0(X0,X3) )
       => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X3)
        & r1_xboole_0(X1,X3)
        & r1_xboole_0(X0,X3) )
     => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).

fof(f49,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f20,f46])).

fof(f20,plain,(
    r1_xboole_0(sK1,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f44,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f21,f41])).

fof(f21,plain,(
    r1_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f17])).

fof(f39,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f34,f36])).

fof(f34,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3) ),
    inference(forward_demodulation,[],[f22,f25])).

fof(f22,plain,(
    ~ r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:36:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (26450)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.47  % (26451)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (26457)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.48  % (26448)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (26452)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.49  % (26458)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.49  % (26456)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.50  % (26459)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.50  % (26455)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.50  % (26454)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.50  % (26460)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.51  % (26447)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.51  % (26463)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.51  % (26453)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (26449)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.52  % (26462)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.21/0.52  % (26461)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 1.26/0.52  % (26458)Refutation found. Thanks to Tanya!
% 1.26/0.52  % SZS status Theorem for theBenchmark
% 1.26/0.52  % SZS output start Proof for theBenchmark
% 1.26/0.52  fof(f1839,plain,(
% 1.26/0.52    $false),
% 1.26/0.52    inference(avatar_sat_refutation,[],[f39,f44,f49,f54,f66,f78,f90,f97,f104,f111,f166,f181,f1727,f1737,f1771,f1838])).
% 1.26/0.52  fof(f1838,plain,(
% 1.26/0.52    spl4_1 | ~spl4_139),
% 1.26/0.52    inference(avatar_split_clause,[],[f1832,f1768,f36])).
% 1.26/0.52  fof(f36,plain,(
% 1.26/0.52    spl4_1 <=> r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.26/0.52  fof(f1768,plain,(
% 1.26/0.52    spl4_139 <=> r1_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_139])])).
% 1.26/0.52  fof(f1832,plain,(
% 1.26/0.52    r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3) | ~spl4_139),
% 1.26/0.52    inference(resolution,[],[f1770,f30])).
% 1.26/0.52  fof(f30,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f15])).
% 1.26/0.52  fof(f15,plain,(
% 1.26/0.52    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.26/0.52    inference(ennf_transformation,[],[f3])).
% 1.26/0.52  fof(f3,axiom,(
% 1.26/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.26/0.52  fof(f1770,plain,(
% 1.26/0.52    r1_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))) | ~spl4_139),
% 1.26/0.52    inference(avatar_component_clause,[],[f1768])).
% 1.26/0.52  fof(f1771,plain,(
% 1.26/0.52    spl4_139 | ~spl4_20 | ~spl4_135),
% 1.26/0.52    inference(avatar_split_clause,[],[f1760,f1734,f163,f1768])).
% 1.26/0.52  fof(f163,plain,(
% 1.26/0.52    spl4_20 <=> sK3 = k4_xboole_0(sK3,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 1.26/0.52  fof(f1734,plain,(
% 1.26/0.52    spl4_135 <=> k1_xboole_0 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_135])])).
% 1.26/0.52  fof(f1760,plain,(
% 1.26/0.52    r1_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))) | (~spl4_20 | ~spl4_135)),
% 1.26/0.52    inference(trivial_inequality_removal,[],[f1755])).
% 1.26/0.52  fof(f1755,plain,(
% 1.26/0.52    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,k2_xboole_0(sK2,k2_xboole_0(sK0,sK1))) | (~spl4_20 | ~spl4_135)),
% 1.26/0.52    inference(superposition,[],[f788,f1736])).
% 1.26/0.52  fof(f1736,plain,(
% 1.26/0.52    k1_xboole_0 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl4_135),
% 1.26/0.52    inference(avatar_component_clause,[],[f1734])).
% 1.26/0.52  fof(f788,plain,(
% 1.26/0.52    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(sK3,X0) | r1_xboole_0(sK3,k2_xboole_0(sK2,X0))) ) | ~spl4_20),
% 1.26/0.52    inference(superposition,[],[f32,f478])).
% 1.26/0.52  fof(f478,plain,(
% 1.26/0.52    ( ! [X3] : (k3_xboole_0(sK3,k2_xboole_0(sK2,X3)) = k3_xboole_0(sK3,X3)) ) | ~spl4_20),
% 1.26/0.52    inference(forward_demodulation,[],[f475,f26])).
% 1.26/0.52  fof(f26,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f9])).
% 1.26/0.52  fof(f9,axiom,(
% 1.26/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.26/0.52  fof(f475,plain,(
% 1.26/0.52    ( ! [X3] : (k3_xboole_0(sK3,k2_xboole_0(sK2,X3)) = k4_xboole_0(sK3,k4_xboole_0(sK3,X3))) ) | ~spl4_20),
% 1.26/0.52    inference(superposition,[],[f26,f247])).
% 1.26/0.52  fof(f247,plain,(
% 1.26/0.52    ( ! [X0] : (k4_xboole_0(sK3,k2_xboole_0(sK2,X0)) = k4_xboole_0(sK3,X0)) ) | ~spl4_20),
% 1.26/0.52    inference(superposition,[],[f33,f165])).
% 1.26/0.52  fof(f165,plain,(
% 1.26/0.52    sK3 = k4_xboole_0(sK3,sK2) | ~spl4_20),
% 1.26/0.52    inference(avatar_component_clause,[],[f163])).
% 1.26/0.52  fof(f33,plain,(
% 1.26/0.52    ( ! [X2,X0,X1] : (k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f7])).
% 1.26/0.52  fof(f7,axiom,(
% 1.26/0.52    ! [X0,X1,X2] : k4_xboole_0(k4_xboole_0(X0,X1),X2) = k4_xboole_0(X0,k2_xboole_0(X1,X2))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).
% 1.26/0.52  fof(f32,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k3_xboole_0(X0,X1) != k1_xboole_0 | r1_xboole_0(X0,X1)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f18])).
% 1.26/0.52  fof(f18,plain,(
% 1.26/0.52    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.26/0.52    inference(nnf_transformation,[],[f2])).
% 1.26/0.52  fof(f2,axiom,(
% 1.26/0.52    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.26/0.52  fof(f1737,plain,(
% 1.26/0.52    spl4_135 | ~spl4_134),
% 1.26/0.52    inference(avatar_split_clause,[],[f1731,f1724,f1734])).
% 1.26/0.52  fof(f1724,plain,(
% 1.26/0.52    spl4_134 <=> r1_xboole_0(sK3,k2_xboole_0(sK0,sK1))),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_134])])).
% 1.26/0.52  fof(f1731,plain,(
% 1.26/0.52    k1_xboole_0 = k3_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl4_134),
% 1.26/0.52    inference(resolution,[],[f1726,f31])).
% 1.26/0.52  fof(f31,plain,(
% 1.26/0.52    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) = k1_xboole_0) )),
% 1.26/0.52    inference(cnf_transformation,[],[f18])).
% 1.26/0.52  fof(f1726,plain,(
% 1.26/0.52    r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | ~spl4_134),
% 1.26/0.52    inference(avatar_component_clause,[],[f1724])).
% 1.26/0.52  fof(f1727,plain,(
% 1.26/0.52    spl4_134 | ~spl4_13 | ~spl4_22),
% 1.26/0.52    inference(avatar_split_clause,[],[f1722,f178,f108,f1724])).
% 1.26/0.52  fof(f108,plain,(
% 1.26/0.52    spl4_13 <=> k1_xboole_0 = k3_xboole_0(sK3,sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 1.26/0.52  fof(f178,plain,(
% 1.26/0.52    spl4_22 <=> sK3 = k4_xboole_0(sK3,sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.26/0.52  fof(f1722,plain,(
% 1.26/0.52    r1_xboole_0(sK3,k2_xboole_0(sK0,sK1)) | (~spl4_13 | ~spl4_22)),
% 1.26/0.52    inference(forward_demodulation,[],[f1697,f25])).
% 1.26/0.52  fof(f25,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.26/0.52    inference(cnf_transformation,[],[f1])).
% 1.26/0.52  fof(f1,axiom,(
% 1.26/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.26/0.52  fof(f1697,plain,(
% 1.26/0.52    r1_xboole_0(sK3,k2_xboole_0(sK1,sK0)) | (~spl4_13 | ~spl4_22)),
% 1.26/0.52    inference(trivial_inequality_removal,[],[f1689])).
% 1.26/0.52  fof(f1689,plain,(
% 1.26/0.52    k1_xboole_0 != k1_xboole_0 | r1_xboole_0(sK3,k2_xboole_0(sK1,sK0)) | (~spl4_13 | ~spl4_22)),
% 1.26/0.52    inference(superposition,[],[f817,f110])).
% 1.26/0.52  fof(f110,plain,(
% 1.26/0.52    k1_xboole_0 = k3_xboole_0(sK3,sK0) | ~spl4_13),
% 1.26/0.52    inference(avatar_component_clause,[],[f108])).
% 1.26/0.52  fof(f817,plain,(
% 1.26/0.52    ( ! [X0] : (k1_xboole_0 != k3_xboole_0(sK3,X0) | r1_xboole_0(sK3,k2_xboole_0(sK1,X0))) ) | ~spl4_22),
% 1.26/0.52    inference(superposition,[],[f32,f486])).
% 1.26/0.52  fof(f486,plain,(
% 1.26/0.52    ( ! [X3] : (k3_xboole_0(sK3,X3) = k3_xboole_0(sK3,k2_xboole_0(sK1,X3))) ) | ~spl4_22),
% 1.26/0.52    inference(forward_demodulation,[],[f483,f26])).
% 1.26/0.52  fof(f483,plain,(
% 1.26/0.52    ( ! [X3] : (k4_xboole_0(sK3,k4_xboole_0(sK3,X3)) = k3_xboole_0(sK3,k2_xboole_0(sK1,X3))) ) | ~spl4_22),
% 1.26/0.52    inference(superposition,[],[f26,f261])).
% 1.26/0.52  fof(f261,plain,(
% 1.26/0.52    ( ! [X0] : (k4_xboole_0(sK3,X0) = k4_xboole_0(sK3,k2_xboole_0(sK1,X0))) ) | ~spl4_22),
% 1.26/0.52    inference(superposition,[],[f33,f180])).
% 1.26/0.52  fof(f180,plain,(
% 1.26/0.52    sK3 = k4_xboole_0(sK3,sK1) | ~spl4_22),
% 1.26/0.52    inference(avatar_component_clause,[],[f178])).
% 1.26/0.52  fof(f181,plain,(
% 1.26/0.52    spl4_22 | ~spl4_12),
% 1.26/0.52    inference(avatar_split_clause,[],[f176,f101,f178])).
% 1.26/0.52  fof(f101,plain,(
% 1.26/0.52    spl4_12 <=> k1_xboole_0 = k3_xboole_0(sK3,sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.26/0.52  fof(f176,plain,(
% 1.26/0.52    sK3 = k4_xboole_0(sK3,sK1) | ~spl4_12),
% 1.26/0.52    inference(forward_demodulation,[],[f173,f24])).
% 1.26/0.52  fof(f24,plain,(
% 1.26/0.52    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.26/0.52    inference(cnf_transformation,[],[f6])).
% 1.26/0.52  fof(f6,axiom,(
% 1.26/0.52    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.26/0.52  fof(f173,plain,(
% 1.26/0.52    k4_xboole_0(sK3,k1_xboole_0) = k4_xboole_0(sK3,sK1) | ~spl4_12),
% 1.26/0.52    inference(superposition,[],[f29,f103])).
% 1.26/0.52  fof(f103,plain,(
% 1.26/0.52    k1_xboole_0 = k3_xboole_0(sK3,sK1) | ~spl4_12),
% 1.26/0.52    inference(avatar_component_clause,[],[f101])).
% 1.26/0.52  fof(f29,plain,(
% 1.26/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 1.26/0.52    inference(cnf_transformation,[],[f8])).
% 1.26/0.52  fof(f8,axiom,(
% 1.26/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 1.26/0.52  fof(f166,plain,(
% 1.26/0.52    spl4_20 | ~spl4_11),
% 1.26/0.52    inference(avatar_split_clause,[],[f161,f94,f163])).
% 1.26/0.52  fof(f94,plain,(
% 1.26/0.52    spl4_11 <=> k1_xboole_0 = k3_xboole_0(sK3,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.26/0.52  fof(f161,plain,(
% 1.26/0.52    sK3 = k4_xboole_0(sK3,sK2) | ~spl4_11),
% 1.26/0.52    inference(forward_demodulation,[],[f158,f24])).
% 1.26/0.52  fof(f158,plain,(
% 1.26/0.52    k4_xboole_0(sK3,sK2) = k4_xboole_0(sK3,k1_xboole_0) | ~spl4_11),
% 1.26/0.52    inference(superposition,[],[f29,f96])).
% 1.26/0.52  fof(f96,plain,(
% 1.26/0.52    k1_xboole_0 = k3_xboole_0(sK3,sK2) | ~spl4_11),
% 1.26/0.52    inference(avatar_component_clause,[],[f94])).
% 1.26/0.52  fof(f111,plain,(
% 1.26/0.52    spl4_13 | ~spl4_10),
% 1.26/0.52    inference(avatar_split_clause,[],[f105,f87,f108])).
% 1.26/0.52  fof(f87,plain,(
% 1.26/0.52    spl4_10 <=> r1_xboole_0(sK3,sK0)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.26/0.52  fof(f105,plain,(
% 1.26/0.52    k1_xboole_0 = k3_xboole_0(sK3,sK0) | ~spl4_10),
% 1.26/0.52    inference(resolution,[],[f89,f31])).
% 1.26/0.52  fof(f89,plain,(
% 1.26/0.52    r1_xboole_0(sK3,sK0) | ~spl4_10),
% 1.26/0.52    inference(avatar_component_clause,[],[f87])).
% 1.26/0.52  fof(f104,plain,(
% 1.26/0.52    spl4_12 | ~spl4_8),
% 1.26/0.52    inference(avatar_split_clause,[],[f98,f75,f101])).
% 1.26/0.52  fof(f75,plain,(
% 1.26/0.52    spl4_8 <=> r1_xboole_0(sK3,sK1)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.26/0.52  fof(f98,plain,(
% 1.26/0.52    k1_xboole_0 = k3_xboole_0(sK3,sK1) | ~spl4_8),
% 1.26/0.52    inference(resolution,[],[f77,f31])).
% 1.26/0.52  fof(f77,plain,(
% 1.26/0.52    r1_xboole_0(sK3,sK1) | ~spl4_8),
% 1.26/0.52    inference(avatar_component_clause,[],[f75])).
% 1.26/0.52  fof(f97,plain,(
% 1.26/0.52    spl4_11 | ~spl4_6),
% 1.26/0.52    inference(avatar_split_clause,[],[f91,f63,f94])).
% 1.26/0.52  fof(f63,plain,(
% 1.26/0.52    spl4_6 <=> r1_xboole_0(sK3,sK2)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.26/0.52  fof(f91,plain,(
% 1.26/0.52    k1_xboole_0 = k3_xboole_0(sK3,sK2) | ~spl4_6),
% 1.26/0.52    inference(resolution,[],[f65,f31])).
% 1.26/0.52  fof(f65,plain,(
% 1.26/0.52    r1_xboole_0(sK3,sK2) | ~spl4_6),
% 1.26/0.52    inference(avatar_component_clause,[],[f63])).
% 1.26/0.52  fof(f90,plain,(
% 1.26/0.52    spl4_10 | ~spl4_4),
% 1.26/0.52    inference(avatar_split_clause,[],[f80,f51,f87])).
% 1.26/0.52  fof(f51,plain,(
% 1.26/0.52    spl4_4 <=> r1_xboole_0(sK0,sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.26/0.52  fof(f80,plain,(
% 1.26/0.52    r1_xboole_0(sK3,sK0) | ~spl4_4),
% 1.26/0.52    inference(resolution,[],[f53,f30])).
% 1.26/0.52  fof(f53,plain,(
% 1.26/0.52    r1_xboole_0(sK0,sK3) | ~spl4_4),
% 1.26/0.52    inference(avatar_component_clause,[],[f51])).
% 1.26/0.52  fof(f78,plain,(
% 1.26/0.52    spl4_8 | ~spl4_3),
% 1.26/0.52    inference(avatar_split_clause,[],[f68,f46,f75])).
% 1.26/0.52  fof(f46,plain,(
% 1.26/0.52    spl4_3 <=> r1_xboole_0(sK1,sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.26/0.52  fof(f68,plain,(
% 1.26/0.52    r1_xboole_0(sK3,sK1) | ~spl4_3),
% 1.26/0.52    inference(resolution,[],[f48,f30])).
% 1.26/0.52  fof(f48,plain,(
% 1.26/0.52    r1_xboole_0(sK1,sK3) | ~spl4_3),
% 1.26/0.52    inference(avatar_component_clause,[],[f46])).
% 1.26/0.52  fof(f66,plain,(
% 1.26/0.52    spl4_6 | ~spl4_2),
% 1.26/0.52    inference(avatar_split_clause,[],[f56,f41,f63])).
% 1.26/0.52  fof(f41,plain,(
% 1.26/0.52    spl4_2 <=> r1_xboole_0(sK2,sK3)),
% 1.26/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.26/0.52  fof(f56,plain,(
% 1.26/0.52    r1_xboole_0(sK3,sK2) | ~spl4_2),
% 1.26/0.52    inference(resolution,[],[f43,f30])).
% 1.26/0.52  fof(f43,plain,(
% 1.26/0.52    r1_xboole_0(sK2,sK3) | ~spl4_2),
% 1.26/0.52    inference(avatar_component_clause,[],[f41])).
% 1.26/0.52  fof(f54,plain,(
% 1.26/0.52    spl4_4),
% 1.26/0.52    inference(avatar_split_clause,[],[f19,f51])).
% 1.26/0.52  fof(f19,plain,(
% 1.26/0.52    r1_xboole_0(sK0,sK3)),
% 1.26/0.52    inference(cnf_transformation,[],[f17])).
% 1.26/0.52  fof(f17,plain,(
% 1.26/0.52    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3)),
% 1.26/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f14,f16])).
% 1.26/0.52  fof(f16,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => (~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3) & r1_xboole_0(sK2,sK3) & r1_xboole_0(sK1,sK3) & r1_xboole_0(sK0,sK3))),
% 1.26/0.52    introduced(choice_axiom,[])).
% 1.26/0.52  fof(f14,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3))),
% 1.26/0.52    inference(flattening,[],[f13])).
% 1.26/0.52  fof(f13,plain,(
% 1.26/0.52    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3) & (r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)))),
% 1.26/0.52    inference(ennf_transformation,[],[f12])).
% 1.26/0.52  fof(f12,negated_conjecture,(
% 1.26/0.52    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 1.26/0.52    inference(negated_conjecture,[],[f11])).
% 1.26/0.52  fof(f11,conjecture,(
% 1.26/0.52    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X3) & r1_xboole_0(X1,X3) & r1_xboole_0(X0,X3)) => r1_xboole_0(k2_xboole_0(k2_xboole_0(X0,X1),X2),X3))),
% 1.26/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_xboole_1)).
% 1.26/0.52  fof(f49,plain,(
% 1.26/0.52    spl4_3),
% 1.26/0.52    inference(avatar_split_clause,[],[f20,f46])).
% 1.26/0.52  fof(f20,plain,(
% 1.26/0.52    r1_xboole_0(sK1,sK3)),
% 1.26/0.52    inference(cnf_transformation,[],[f17])).
% 1.26/0.52  fof(f44,plain,(
% 1.26/0.52    spl4_2),
% 1.26/0.52    inference(avatar_split_clause,[],[f21,f41])).
% 1.26/0.52  fof(f21,plain,(
% 1.26/0.52    r1_xboole_0(sK2,sK3)),
% 1.26/0.52    inference(cnf_transformation,[],[f17])).
% 1.26/0.52  fof(f39,plain,(
% 1.26/0.52    ~spl4_1),
% 1.26/0.52    inference(avatar_split_clause,[],[f34,f36])).
% 1.26/0.52  fof(f34,plain,(
% 1.26/0.52    ~r1_xboole_0(k2_xboole_0(sK2,k2_xboole_0(sK0,sK1)),sK3)),
% 1.26/0.52    inference(forward_demodulation,[],[f22,f25])).
% 1.26/0.52  fof(f22,plain,(
% 1.26/0.52    ~r1_xboole_0(k2_xboole_0(k2_xboole_0(sK0,sK1),sK2),sK3)),
% 1.26/0.52    inference(cnf_transformation,[],[f17])).
% 1.26/0.52  % SZS output end Proof for theBenchmark
% 1.26/0.52  % (26458)------------------------------
% 1.26/0.52  % (26458)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.52  % (26458)Termination reason: Refutation
% 1.26/0.52  
% 1.26/0.52  % (26458)Memory used [KB]: 11641
% 1.26/0.52  % (26458)Time elapsed: 0.102 s
% 1.26/0.52  % (26458)------------------------------
% 1.26/0.52  % (26458)------------------------------
% 1.26/0.53  % (26446)Success in time 0.16 s
%------------------------------------------------------------------------------
