%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0079+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:47:19 EST 2020

% Result     : Theorem 0.13s
% Output     : Refutation 0.13s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 134 expanded)
%              Number of leaves         :   22 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :  156 ( 306 expanded)
%              Number of equality atoms :   63 ( 135 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f958,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f31,f35,f39,f43,f49,f68,f107,f111,f172,f347,f368,f950,f957])).

fof(f957,plain,
    ( sK1 != k3_xboole_0(sK1,sK2)
    | sK2 != k3_xboole_0(sK1,sK2)
    | sK1 = sK2 ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f950,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f946,f165,f41,f948])).

fof(f948,plain,
    ( spl4_20
  <=> sK1 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f41,plain,
    ( spl4_4
  <=> k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f165,plain,
    ( spl4_11
  <=> k1_xboole_0 = k3_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f946,plain,
    ( sK1 = k3_xboole_0(sK1,sK2)
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f932,f69])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f53,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f53,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f22,f24])).

fof(f24,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f22,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f932,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k2_xboole_0(sK0,sK1))
    | ~ spl4_4
    | ~ spl4_11 ),
    inference(superposition,[],[f190,f42])).

fof(f42,plain,
    ( k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f41])).

fof(f190,plain,
    ( ! [X0] : k3_xboole_0(sK1,k2_xboole_0(X0,sK3)) = k3_xboole_0(sK1,X0)
    | ~ spl4_11 ),
    inference(forward_demodulation,[],[f188,f21])).

fof(f21,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

fof(f188,plain,
    ( ! [X0] : k3_xboole_0(sK1,k2_xboole_0(X0,sK3)) = k2_xboole_0(k3_xboole_0(sK1,X0),k1_xboole_0)
    | ~ spl4_11 ),
    inference(superposition,[],[f27,f166])).

fof(f166,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f165])).

fof(f27,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k2_xboole_0(X1,X2)) = k2_xboole_0(k3_xboole_0(X0,X1),k3_xboole_0(X0,X2)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

fof(f368,plain,
    ( spl4_16
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f358,f344,f360])).

fof(f360,plain,
    ( spl4_16
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f344,plain,
    ( spl4_15
  <=> sK2 = k3_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f358,plain,
    ( sK2 = k3_xboole_0(sK1,sK2)
    | ~ spl4_15 ),
    inference(superposition,[],[f23,f345])).

fof(f345,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f344])).

fof(f23,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f347,plain,
    ( spl4_15
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f335,f109,f66,f344])).

fof(f66,plain,
    ( spl4_6
  <=> sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f109,plain,
    ( spl4_10
  <=> k1_xboole_0 = k3_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f335,plain,
    ( sK2 = k3_xboole_0(sK2,sK1)
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(superposition,[],[f67,f185])).

fof(f185,plain,
    ( ! [X1] : k3_xboole_0(sK2,k2_xboole_0(sK0,X1)) = k3_xboole_0(sK2,X1)
    | ~ spl4_10 ),
    inference(forward_demodulation,[],[f176,f50])).

fof(f50,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f24,f21])).

fof(f176,plain,
    ( ! [X1] : k3_xboole_0(sK2,k2_xboole_0(sK0,X1)) = k2_xboole_0(k1_xboole_0,k3_xboole_0(sK2,X1))
    | ~ spl4_10 ),
    inference(superposition,[],[f27,f110])).

fof(f110,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f67,plain,
    ( sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f172,plain,
    ( spl4_11
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f163,f105,f165])).

fof(f105,plain,
    ( spl4_9
  <=> k1_xboole_0 = k3_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f163,plain,
    ( k1_xboole_0 = k3_xboole_0(sK1,sK3)
    | ~ spl4_9 ),
    inference(superposition,[],[f23,f106])).

fof(f106,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK1)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f105])).

fof(f111,plain,
    ( spl4_10
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f103,f37,f109])).

fof(f37,plain,
    ( spl4_3
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f103,plain,
    ( k1_xboole_0 = k3_xboole_0(sK2,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f26,f38])).

fof(f38,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f37])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f107,plain,
    ( spl4_9
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f102,f33,f105])).

fof(f33,plain,
    ( spl4_2
  <=> r1_xboole_0(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f102,plain,
    ( k1_xboole_0 = k3_xboole_0(sK3,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f26,f34])).

fof(f34,plain,
    ( r1_xboole_0(sK3,sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f68,plain,
    ( spl4_6
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f62,f47,f66])).

fof(f47,plain,
    ( spl4_5
  <=> r1_tarski(sK2,k2_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f62,plain,
    ( sK2 = k3_xboole_0(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_5 ),
    inference(resolution,[],[f25,f48])).

fof(f48,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f47])).

fof(f49,plain,
    ( spl4_5
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f44,f41,f47])).

fof(f44,plain,
    ( r1_tarski(sK2,k2_xboole_0(sK0,sK1))
    | ~ spl4_4 ),
    inference(superposition,[],[f22,f42])).

fof(f43,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f17,f41])).

fof(f17,plain,(
    k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,
    ( sK1 != sK2
    & r1_xboole_0(sK3,sK1)
    & r1_xboole_0(sK2,sK0)
    & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f12,f15])).

fof(f15,plain,
    ( ? [X0,X1,X2,X3] :
        ( X1 != X2
        & r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
   => ( sK1 != sK2
      & r1_xboole_0(sK3,sK1)
      & r1_xboole_0(sK2,sK0)
      & k2_xboole_0(sK0,sK1) = k2_xboole_0(sK2,sK3) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0,X1,X2,X3] :
      ( X1 != X2
      & r1_xboole_0(X3,X1)
      & r1_xboole_0(X2,X0)
      & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X3,X1)
          & r1_xboole_0(X2,X0)
          & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
       => X1 = X2 ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X3,X1)
        & r1_xboole_0(X2,X0)
        & k2_xboole_0(X0,X1) = k2_xboole_0(X2,X3) )
     => X1 = X2 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_xboole_1)).

fof(f39,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f18,f37])).

fof(f18,plain,(
    r1_xboole_0(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f19,f33])).

fof(f19,plain,(
    r1_xboole_0(sK3,sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f31,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f20,f29])).

fof(f29,plain,
    ( spl4_1
  <=> sK1 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f20,plain,(
    sK1 != sK2 ),
    inference(cnf_transformation,[],[f16])).

%------------------------------------------------------------------------------
