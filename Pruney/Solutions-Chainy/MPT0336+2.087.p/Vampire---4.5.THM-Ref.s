%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:35 EST 2020

% Result     : Theorem 3.32s
% Output     : Refutation 3.32s
% Verified   : 
% Statistics : Number of formulae       :  182 ( 420 expanded)
%              Number of leaves         :   45 ( 169 expanded)
%              Depth                    :   14
%              Number of atoms          :  412 ( 983 expanded)
%              Number of equality atoms :   62 ( 172 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5176,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f88,f96,f101,f109,f123,f293,f312,f643,f649,f655,f1589,f1648,f1654,f1659,f1743,f1751,f1806,f1813,f1820,f2730,f2798,f4802,f4944,f4949,f4958,f4964,f4969,f5175])).

fof(f5175,plain,
    ( spl5_3
    | ~ spl5_5
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f5174])).

fof(f5174,plain,
    ( $false
    | spl5_3
    | ~ spl5_5
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f5173,f4943])).

fof(f4943,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f4941])).

fof(f4941,plain,
    ( spl5_28
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f5173,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f5166,f76])).

fof(f76,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_5
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f5166,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0)
    | spl5_3 ),
    inference(resolution,[],[f1293,f64])).

fof(f64,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1293,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(k2_xboole_0(X10,X11),X9)
      | ~ r1_xboole_0(X9,X11)
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f46,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f4969,plain,
    ( spl5_32
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f4952,f4946,f4966])).

fof(f4966,plain,
    ( spl5_32
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f4946,plain,
    ( spl5_29
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f4952,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_29 ),
    inference(resolution,[],[f4948,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k4_xboole_0(X0,X1) != X0 )
      & ( k4_xboole_0(X0,X1) = X0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f4948,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f4946])).

fof(f4964,plain,
    ( spl5_31
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f4950,f4941,f4961])).

fof(f4961,plain,
    ( spl5_31
  <=> sK1 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f4950,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl5_28 ),
    inference(resolution,[],[f4943,f42])).

fof(f4958,plain,
    ( spl5_30
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f4924,f4799,f4955])).

fof(f4955,plain,
    ( spl5_30
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f4799,plain,
    ( spl5_27
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f4924,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_27 ),
    inference(superposition,[],[f271,f4801])).

fof(f4801,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f4799])).

fof(f271,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f214,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f214,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f33,f36])).

fof(f36,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f4949,plain,
    ( spl5_29
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f4916,f4799,f4946])).

fof(f4916,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_27 ),
    inference(superposition,[],[f273,f4801])).

fof(f273,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
    inference(resolution,[],[f271,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
      | ~ r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
     => ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f4944,plain,
    ( spl5_28
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f4914,f4799,f4941])).

fof(f4914,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_27 ),
    inference(superposition,[],[f1238,f4801])).

fof(f1238,plain,(
    ! [X4,X5,X3] : r1_xboole_0(X3,k3_xboole_0(X4,k4_xboole_0(X5,X3))) ),
    inference(resolution,[],[f273,f41])).

fof(f4802,plain,
    ( spl5_27
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f4617,f1817,f4799])).

fof(f1817,plain,
    ( spl5_24
  <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f4617,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_24 ),
    inference(superposition,[],[f4352,f211])).

fof(f211,plain,(
    ! [X4,X3] : k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4)) ),
    inference(superposition,[],[f36,f36])).

fof(f4352,plain,
    ( ! [X0] : k4_xboole_0(X0,k3_xboole_0(sK0,sK1)) = X0
    | ~ spl5_24 ),
    inference(resolution,[],[f4348,f42])).

fof(f4348,plain,
    ( ! [X1] : r1_xboole_0(X1,k3_xboole_0(sK0,sK1))
    | ~ spl5_24 ),
    inference(resolution,[],[f4338,f41])).

fof(f4338,plain,
    ( ! [X10] : r1_xboole_0(k3_xboole_0(sK0,sK1),X10)
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f4315,f271])).

fof(f4315,plain,
    ( ! [X10] :
        ( r1_xboole_0(k3_xboole_0(sK0,sK1),X10)
        | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1) )
    | ~ spl5_24 ),
    inference(resolution,[],[f4309,f1860])).

fof(f1860,plain,
    ( ! [X13] :
        ( r1_xboole_0(X13,k3_xboole_0(sK0,sK1))
        | ~ r1_tarski(X13,sK1) )
    | ~ spl5_24 ),
    inference(superposition,[],[f50,f1819])).

fof(f1819,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f1817])).

fof(f4309,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f4305])).

fof(f4305,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f636,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f636,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(sK4(X1,X2),X3)
      | ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f40,f38])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2798,plain,
    ( spl5_26
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f2782,f2727,f2795])).

fof(f2795,plain,
    ( spl5_26
  <=> r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f2727,plain,
    ( spl5_25
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f2782,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK3))
    | ~ spl5_25 ),
    inference(superposition,[],[f271,f2729])).

fof(f2729,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f2727])).

fof(f2730,plain,
    ( spl5_25
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1637,f1586,f309,f2727])).

fof(f309,plain,
    ( spl5_12
  <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1586,plain,
    ( spl5_16
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1637,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_12
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f1610,f311])).

fof(f311,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f309])).

fof(f1610,plain,
    ( k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_16 ),
    inference(superposition,[],[f36,f1588])).

fof(f1588,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f1586])).

fof(f1820,plain,
    ( spl5_24
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1814,f1810,f1817])).

fof(f1810,plain,
    ( spl5_23
  <=> r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1814,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_23 ),
    inference(resolution,[],[f1812,f42])).

fof(f1812,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f1810])).

fof(f1813,plain,
    ( spl5_23
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f1808,f1803,f1810])).

fof(f1803,plain,
    ( spl5_22
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1808,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_22 ),
    inference(resolution,[],[f1805,f41])).

fof(f1805,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f1803])).

fof(f1806,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f1789,f1748,f67,f1803])).

fof(f67,plain,
    ( spl5_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1748,plain,
    ( spl5_21
  <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1789,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_4
    | ~ spl5_21 ),
    inference(resolution,[],[f1758,f69])).

fof(f69,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f1758,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_tarski(sK3))
        | r1_xboole_0(X1,sK1) )
    | ~ spl5_21 ),
    inference(superposition,[],[f50,f1750])).

fof(f1750,plain,
    ( k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f1748])).

fof(f1751,plain,
    ( spl5_21
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1614,f1586,f1748])).

fof(f1614,plain,
    ( k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_16 ),
    inference(superposition,[],[f80,f1588])).

fof(f80,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f42,f72])).

fof(f72,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1743,plain,
    ( ~ spl5_20
    | spl5_3 ),
    inference(avatar_split_clause,[],[f1664,f62,f1740])).

fof(f1740,plain,
    ( spl5_20
  <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1664,plain,
    ( sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl5_3 ),
    inference(resolution,[],[f112,f64])).

fof(f112,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | k4_xboole_0(X2,X3) != X2 ) ),
    inference(resolution,[],[f43,f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1659,plain,
    ( spl5_19
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1613,f1586,f1656])).

fof(f1656,plain,
    ( spl5_19
  <=> r1_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1613,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_16 ),
    inference(superposition,[],[f72,f1588])).

fof(f1654,plain,
    ( spl5_18
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1609,f1586,f1651])).

fof(f1651,plain,
    ( spl5_18
  <=> r1_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1609,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_16 ),
    inference(superposition,[],[f34,f1588])).

fof(f1648,plain,
    ( ~ spl5_17
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f1636,f1586,f1645])).

fof(f1645,plain,
    ( spl5_17
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1636,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl5_16 ),
    inference(trivial_inequality_removal,[],[f1607])).

fof(f1607,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK3,sK1)
    | ~ spl5_16 ),
    inference(superposition,[],[f44,f1588])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,k1_tarski(X1)) = X0
        | r2_hidden(X1,X0) )
      & ( ~ r2_hidden(X1,X0)
        | k4_xboole_0(X0,k1_tarski(X1)) != X0 ) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) = X0
    <=> ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f1589,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1559,f57,f52,f1586])).

fof(f52,plain,
    ( spl5_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f57,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1559,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f1003,f59])).

fof(f59,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f1003,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(sK2,X3)
        | k4_xboole_0(X3,k1_tarski(sK3)) = X3 )
    | ~ spl5_1 ),
    inference(resolution,[],[f45,f635])).

fof(f635,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f40,f54])).

fof(f54,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f655,plain,
    ( ~ spl5_15
    | ~ spl5_11
    | spl5_14 ),
    inference(avatar_split_clause,[],[f650,f646,f290,f652])).

fof(f652,plain,
    ( spl5_15
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f290,plain,
    ( spl5_11
  <=> k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f646,plain,
    ( spl5_14
  <=> sK2 = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f650,plain,
    ( sK2 != k3_xboole_0(sK1,sK2)
    | ~ spl5_11
    | spl5_14 ),
    inference(superposition,[],[f648,f292])).

fof(f292,plain,
    ( k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f290])).

fof(f648,plain,
    ( sK2 != k4_xboole_0(sK2,sK2)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f646])).

fof(f649,plain,
    ( ~ spl5_14
    | spl5_13 ),
    inference(avatar_split_clause,[],[f644,f640,f646])).

fof(f640,plain,
    ( spl5_13
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f644,plain,
    ( sK2 != k4_xboole_0(sK2,sK2)
    | spl5_13 ),
    inference(resolution,[],[f642,f43])).

fof(f642,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f640])).

fof(f643,plain,
    ( ~ spl5_13
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f638,f52,f640])).

fof(f638,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f635,f54])).

fof(f312,plain,
    ( spl5_12
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f208,f98,f309])).

fof(f98,plain,
    ( spl5_8
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f208,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl5_8 ),
    inference(superposition,[],[f36,f100])).

fof(f100,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f293,plain,
    ( spl5_11
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f233,f85,f290])).

fof(f85,plain,
    ( spl5_6
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f233,plain,
    ( k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f207,f35])).

fof(f207,plain,
    ( k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f36,f87])).

fof(f87,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f123,plain,
    ( ~ spl5_10
    | spl5_3 ),
    inference(avatar_split_clause,[],[f110,f62,f120])).

fof(f120,plain,
    ( spl5_10
  <=> k2_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f110,plain,
    ( k2_xboole_0(sK0,sK2) != k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(resolution,[],[f43,f64])).

fof(f109,plain,
    ( spl5_9
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f104,f98,f106])).

fof(f106,plain,
    ( spl5_9
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f104,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl5_8 ),
    inference(superposition,[],[f33,f100])).

fof(f101,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f82,f74,f98])).

fof(f82,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f42,f76])).

fof(f96,plain,
    ( spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f91,f85,f93])).

fof(f93,plain,
    ( spl5_7
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f91,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f33,f87])).

fof(f88,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f83,f57,f85])).

fof(f83,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f59])).

fof(f77,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f71,f57,f74])).

fof(f71,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f41,f59])).

fof(f70,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f28,f67])).

fof(f28,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2,X3] :
        ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
        & r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
   => ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
      & r1_xboole_0(sK2,sK1)
      & r2_hidden(sK3,sK2)
      & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f65,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f31,f62])).

fof(f31,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f55,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.42  % (16622)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.19/0.46  % (16607)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.19/0.46  % (16617)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.19/0.46  % (16620)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.19/0.47  % (16609)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.19/0.47  % (16608)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.19/0.47  % (16612)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.19/0.47  % (16614)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.19/0.48  % (16619)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.19/0.48  % (16611)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.19/0.48  % (16623)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.19/0.49  % (16615)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.19/0.49  % (16616)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.19/0.49  % (16606)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.19/0.49  % (16618)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.19/0.50  % (16610)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.19/0.50  % (16621)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.19/0.51  % (16613)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 3.32/0.79  % (16606)Refutation found. Thanks to Tanya!
% 3.32/0.79  % SZS status Theorem for theBenchmark
% 3.32/0.79  % SZS output start Proof for theBenchmark
% 3.32/0.79  fof(f5176,plain,(
% 3.32/0.79    $false),
% 3.32/0.79    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f88,f96,f101,f109,f123,f293,f312,f643,f649,f655,f1589,f1648,f1654,f1659,f1743,f1751,f1806,f1813,f1820,f2730,f2798,f4802,f4944,f4949,f4958,f4964,f4969,f5175])).
% 3.32/0.79  fof(f5175,plain,(
% 3.32/0.79    spl5_3 | ~spl5_5 | ~spl5_28),
% 3.32/0.79    inference(avatar_contradiction_clause,[],[f5174])).
% 3.32/0.79  fof(f5174,plain,(
% 3.32/0.79    $false | (spl5_3 | ~spl5_5 | ~spl5_28)),
% 3.32/0.79    inference(subsumption_resolution,[],[f5173,f4943])).
% 3.32/0.79  fof(f4943,plain,(
% 3.32/0.79    r1_xboole_0(sK1,sK0) | ~spl5_28),
% 3.32/0.79    inference(avatar_component_clause,[],[f4941])).
% 3.32/0.79  fof(f4941,plain,(
% 3.32/0.79    spl5_28 <=> r1_xboole_0(sK1,sK0)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 3.32/0.79  fof(f5173,plain,(
% 3.32/0.79    ~r1_xboole_0(sK1,sK0) | (spl5_3 | ~spl5_5)),
% 3.32/0.79    inference(subsumption_resolution,[],[f5166,f76])).
% 3.32/0.79  fof(f76,plain,(
% 3.32/0.79    r1_xboole_0(sK1,sK2) | ~spl5_5),
% 3.32/0.79    inference(avatar_component_clause,[],[f74])).
% 3.32/0.79  fof(f74,plain,(
% 3.32/0.79    spl5_5 <=> r1_xboole_0(sK1,sK2)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 3.32/0.79  fof(f5166,plain,(
% 3.32/0.79    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0) | spl5_3),
% 3.32/0.79    inference(resolution,[],[f1293,f64])).
% 3.32/0.79  fof(f64,plain,(
% 3.32/0.79    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 3.32/0.79    inference(avatar_component_clause,[],[f62])).
% 3.32/0.79  fof(f62,plain,(
% 3.32/0.79    spl5_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 3.32/0.79  fof(f1293,plain,(
% 3.32/0.79    ( ! [X10,X11,X9] : (r1_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10)) )),
% 3.32/0.79    inference(resolution,[],[f46,f41])).
% 3.32/0.79  fof(f41,plain,(
% 3.32/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 3.32/0.79    inference(cnf_transformation,[],[f19])).
% 3.32/0.79  fof(f19,plain,(
% 3.32/0.79    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 3.32/0.79    inference(ennf_transformation,[],[f2])).
% 3.32/0.79  fof(f2,axiom,(
% 3.32/0.79    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 3.32/0.79  fof(f46,plain,(
% 3.32/0.79    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 3.32/0.79    inference(cnf_transformation,[],[f20])).
% 3.32/0.79  fof(f20,plain,(
% 3.32/0.79    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.32/0.79    inference(ennf_transformation,[],[f7])).
% 3.32/0.79  fof(f7,axiom,(
% 3.32/0.79    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).
% 3.32/0.79  fof(f4969,plain,(
% 3.32/0.79    spl5_32 | ~spl5_29),
% 3.32/0.79    inference(avatar_split_clause,[],[f4952,f4946,f4966])).
% 3.32/0.79  fof(f4966,plain,(
% 3.32/0.79    spl5_32 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 3.32/0.79  fof(f4946,plain,(
% 3.32/0.79    spl5_29 <=> r1_xboole_0(sK0,sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 3.32/0.79  fof(f4952,plain,(
% 3.32/0.79    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_29),
% 3.32/0.79    inference(resolution,[],[f4948,f42])).
% 3.32/0.79  fof(f42,plain,(
% 3.32/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 3.32/0.79    inference(cnf_transformation,[],[f26])).
% 3.32/0.79  fof(f26,plain,(
% 3.32/0.79    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 3.32/0.79    inference(nnf_transformation,[],[f9])).
% 3.32/0.79  fof(f9,axiom,(
% 3.32/0.79    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).
% 3.32/0.79  fof(f4948,plain,(
% 3.32/0.79    r1_xboole_0(sK0,sK1) | ~spl5_29),
% 3.32/0.79    inference(avatar_component_clause,[],[f4946])).
% 3.32/0.79  fof(f4964,plain,(
% 3.32/0.79    spl5_31 | ~spl5_28),
% 3.32/0.79    inference(avatar_split_clause,[],[f4950,f4941,f4961])).
% 3.32/0.79  fof(f4961,plain,(
% 3.32/0.79    spl5_31 <=> sK1 = k4_xboole_0(sK1,sK0)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 3.32/0.79  fof(f4950,plain,(
% 3.32/0.79    sK1 = k4_xboole_0(sK1,sK0) | ~spl5_28),
% 3.32/0.79    inference(resolution,[],[f4943,f42])).
% 3.32/0.79  fof(f4958,plain,(
% 3.32/0.79    spl5_30 | ~spl5_27),
% 3.32/0.79    inference(avatar_split_clause,[],[f4924,f4799,f4955])).
% 3.32/0.79  fof(f4955,plain,(
% 3.32/0.79    spl5_30 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 3.32/0.79  fof(f4799,plain,(
% 3.32/0.79    spl5_27 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 3.32/0.79  fof(f4924,plain,(
% 3.32/0.79    r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_27),
% 3.32/0.79    inference(superposition,[],[f271,f4801])).
% 3.32/0.79  fof(f4801,plain,(
% 3.32/0.79    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_27),
% 3.32/0.79    inference(avatar_component_clause,[],[f4799])).
% 3.32/0.79  fof(f271,plain,(
% 3.32/0.79    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 3.32/0.79    inference(superposition,[],[f214,f35])).
% 3.32/0.79  fof(f35,plain,(
% 3.32/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 3.32/0.79    inference(cnf_transformation,[],[f1])).
% 3.32/0.79  fof(f1,axiom,(
% 3.32/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 3.32/0.79  fof(f214,plain,(
% 3.32/0.79    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X1,X2),X1)) )),
% 3.32/0.79    inference(superposition,[],[f33,f36])).
% 3.32/0.79  fof(f36,plain,(
% 3.32/0.79    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.32/0.79    inference(cnf_transformation,[],[f6])).
% 3.32/0.79  fof(f6,axiom,(
% 3.32/0.79    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.32/0.79  fof(f33,plain,(
% 3.32/0.79    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.32/0.79    inference(cnf_transformation,[],[f5])).
% 3.32/0.79  fof(f5,axiom,(
% 3.32/0.79    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.32/0.79  fof(f4949,plain,(
% 3.32/0.79    spl5_29 | ~spl5_27),
% 3.32/0.79    inference(avatar_split_clause,[],[f4916,f4799,f4946])).
% 3.32/0.79  fof(f4916,plain,(
% 3.32/0.79    r1_xboole_0(sK0,sK1) | ~spl5_27),
% 3.32/0.79    inference(superposition,[],[f273,f4801])).
% 3.32/0.79  fof(f273,plain,(
% 3.32/0.79    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),X2)) )),
% 3.32/0.79    inference(resolution,[],[f271,f50])).
% 3.32/0.79  fof(f50,plain,(
% 3.32/0.79    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 3.32/0.79    inference(cnf_transformation,[],[f21])).
% 3.32/0.79  fof(f21,plain,(
% 3.32/0.79    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.32/0.79    inference(ennf_transformation,[],[f4])).
% 3.32/0.79  fof(f4,axiom,(
% 3.32/0.79    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).
% 3.32/0.79  fof(f4944,plain,(
% 3.32/0.79    spl5_28 | ~spl5_27),
% 3.32/0.79    inference(avatar_split_clause,[],[f4914,f4799,f4941])).
% 3.32/0.79  fof(f4914,plain,(
% 3.32/0.79    r1_xboole_0(sK1,sK0) | ~spl5_27),
% 3.32/0.79    inference(superposition,[],[f1238,f4801])).
% 3.32/0.79  fof(f1238,plain,(
% 3.32/0.79    ( ! [X4,X5,X3] : (r1_xboole_0(X3,k3_xboole_0(X4,k4_xboole_0(X5,X3)))) )),
% 3.32/0.79    inference(resolution,[],[f273,f41])).
% 3.32/0.79  fof(f4802,plain,(
% 3.32/0.79    spl5_27 | ~spl5_24),
% 3.32/0.79    inference(avatar_split_clause,[],[f4617,f1817,f4799])).
% 3.32/0.79  fof(f1817,plain,(
% 3.32/0.79    spl5_24 <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 3.32/0.79  fof(f4617,plain,(
% 3.32/0.79    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_24),
% 3.32/0.79    inference(superposition,[],[f4352,f211])).
% 3.32/0.79  fof(f211,plain,(
% 3.32/0.79    ( ! [X4,X3] : (k3_xboole_0(X3,k4_xboole_0(X3,X4)) = k4_xboole_0(X3,k3_xboole_0(X3,X4))) )),
% 3.32/0.79    inference(superposition,[],[f36,f36])).
% 3.32/0.79  fof(f4352,plain,(
% 3.32/0.79    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(sK0,sK1)) = X0) ) | ~spl5_24),
% 3.32/0.79    inference(resolution,[],[f4348,f42])).
% 3.32/0.79  fof(f4348,plain,(
% 3.32/0.79    ( ! [X1] : (r1_xboole_0(X1,k3_xboole_0(sK0,sK1))) ) | ~spl5_24),
% 3.32/0.79    inference(resolution,[],[f4338,f41])).
% 3.32/0.79  fof(f4338,plain,(
% 3.32/0.79    ( ! [X10] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X10)) ) | ~spl5_24),
% 3.32/0.79    inference(subsumption_resolution,[],[f4315,f271])).
% 3.32/0.79  fof(f4315,plain,(
% 3.32/0.79    ( ! [X10] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X10) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1)) ) | ~spl5_24),
% 3.32/0.79    inference(resolution,[],[f4309,f1860])).
% 3.32/0.79  fof(f1860,plain,(
% 3.32/0.79    ( ! [X13] : (r1_xboole_0(X13,k3_xboole_0(sK0,sK1)) | ~r1_tarski(X13,sK1)) ) | ~spl5_24),
% 3.32/0.79    inference(superposition,[],[f50,f1819])).
% 3.32/0.79  fof(f1819,plain,(
% 3.32/0.79    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_24),
% 3.32/0.79    inference(avatar_component_clause,[],[f1817])).
% 3.32/0.79  fof(f4309,plain,(
% 3.32/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 3.32/0.79    inference(duplicate_literal_removal,[],[f4305])).
% 3.32/0.79  fof(f4305,plain,(
% 3.32/0.79    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 3.32/0.79    inference(resolution,[],[f636,f38])).
% 3.32/0.79  fof(f38,plain,(
% 3.32/0.79    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 3.32/0.79    inference(cnf_transformation,[],[f25])).
% 3.32/0.79  fof(f25,plain,(
% 3.32/0.79    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 3.32/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).
% 3.32/0.79  fof(f24,plain,(
% 3.32/0.79    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 3.32/0.79    introduced(choice_axiom,[])).
% 3.32/0.79  fof(f18,plain,(
% 3.32/0.79    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 3.32/0.79    inference(ennf_transformation,[],[f15])).
% 3.32/0.79  fof(f15,plain,(
% 3.32/0.79    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.32/0.79    inference(rectify,[],[f3])).
% 3.32/0.79  fof(f3,axiom,(
% 3.32/0.79    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 3.32/0.79  fof(f636,plain,(
% 3.32/0.79    ( ! [X2,X3,X1] : (~r2_hidden(sK4(X1,X2),X3) | ~r1_xboole_0(X1,X3) | r1_xboole_0(X1,X2)) )),
% 3.32/0.79    inference(resolution,[],[f40,f38])).
% 3.32/0.79  fof(f40,plain,(
% 3.32/0.79    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 3.32/0.79    inference(cnf_transformation,[],[f25])).
% 3.32/0.79  fof(f2798,plain,(
% 3.32/0.79    spl5_26 | ~spl5_25),
% 3.32/0.79    inference(avatar_split_clause,[],[f2782,f2727,f2795])).
% 3.32/0.79  fof(f2795,plain,(
% 3.32/0.79    spl5_26 <=> r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK3))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 3.32/0.79  fof(f2727,plain,(
% 3.32/0.79    spl5_25 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 3.32/0.79  fof(f2782,plain,(
% 3.32/0.79    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK3)) | ~spl5_25),
% 3.32/0.79    inference(superposition,[],[f271,f2729])).
% 3.32/0.79  fof(f2729,plain,(
% 3.32/0.79    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_25),
% 3.32/0.79    inference(avatar_component_clause,[],[f2727])).
% 3.32/0.79  fof(f2730,plain,(
% 3.32/0.79    spl5_25 | ~spl5_12 | ~spl5_16),
% 3.32/0.79    inference(avatar_split_clause,[],[f1637,f1586,f309,f2727])).
% 3.32/0.79  fof(f309,plain,(
% 3.32/0.79    spl5_12 <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 3.32/0.79  fof(f1586,plain,(
% 3.32/0.79    spl5_16 <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK3))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 3.32/0.79  fof(f1637,plain,(
% 3.32/0.79    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3)) | (~spl5_12 | ~spl5_16)),
% 3.32/0.79    inference(forward_demodulation,[],[f1610,f311])).
% 3.32/0.79  fof(f311,plain,(
% 3.32/0.79    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | ~spl5_12),
% 3.32/0.79    inference(avatar_component_clause,[],[f309])).
% 3.32/0.79  fof(f1610,plain,(
% 3.32/0.79    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_16),
% 3.32/0.79    inference(superposition,[],[f36,f1588])).
% 3.32/0.79  fof(f1588,plain,(
% 3.32/0.79    sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_16),
% 3.32/0.79    inference(avatar_component_clause,[],[f1586])).
% 3.32/0.79  fof(f1820,plain,(
% 3.32/0.79    spl5_24 | ~spl5_23),
% 3.32/0.79    inference(avatar_split_clause,[],[f1814,f1810,f1817])).
% 3.32/0.79  fof(f1810,plain,(
% 3.32/0.79    spl5_23 <=> r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 3.32/0.79  fof(f1814,plain,(
% 3.32/0.79    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_23),
% 3.32/0.79    inference(resolution,[],[f1812,f42])).
% 3.32/0.79  fof(f1812,plain,(
% 3.32/0.79    r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_23),
% 3.32/0.79    inference(avatar_component_clause,[],[f1810])).
% 3.32/0.79  fof(f1813,plain,(
% 3.32/0.79    spl5_23 | ~spl5_22),
% 3.32/0.79    inference(avatar_split_clause,[],[f1808,f1803,f1810])).
% 3.32/0.79  fof(f1803,plain,(
% 3.32/0.79    spl5_22 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 3.32/0.79  fof(f1808,plain,(
% 3.32/0.79    r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_22),
% 3.32/0.79    inference(resolution,[],[f1805,f41])).
% 3.32/0.79  fof(f1805,plain,(
% 3.32/0.79    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | ~spl5_22),
% 3.32/0.79    inference(avatar_component_clause,[],[f1803])).
% 3.32/0.79  fof(f1806,plain,(
% 3.32/0.79    spl5_22 | ~spl5_4 | ~spl5_21),
% 3.32/0.79    inference(avatar_split_clause,[],[f1789,f1748,f67,f1803])).
% 3.32/0.79  fof(f67,plain,(
% 3.32/0.79    spl5_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 3.32/0.79  fof(f1748,plain,(
% 3.32/0.79    spl5_21 <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 3.32/0.79  fof(f1789,plain,(
% 3.32/0.79    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | (~spl5_4 | ~spl5_21)),
% 3.32/0.79    inference(resolution,[],[f1758,f69])).
% 3.32/0.79  fof(f69,plain,(
% 3.32/0.79    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl5_4),
% 3.32/0.79    inference(avatar_component_clause,[],[f67])).
% 3.32/0.79  fof(f1758,plain,(
% 3.32/0.79    ( ! [X1] : (~r1_tarski(X1,k1_tarski(sK3)) | r1_xboole_0(X1,sK1)) ) | ~spl5_21),
% 3.32/0.79    inference(superposition,[],[f50,f1750])).
% 3.32/0.79  fof(f1750,plain,(
% 3.32/0.79    k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) | ~spl5_21),
% 3.32/0.79    inference(avatar_component_clause,[],[f1748])).
% 3.32/0.79  fof(f1751,plain,(
% 3.32/0.79    spl5_21 | ~spl5_16),
% 3.32/0.79    inference(avatar_split_clause,[],[f1614,f1586,f1748])).
% 3.32/0.79  fof(f1614,plain,(
% 3.32/0.79    k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) | ~spl5_16),
% 3.32/0.79    inference(superposition,[],[f80,f1588])).
% 3.32/0.79  fof(f80,plain,(
% 3.32/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 3.32/0.79    inference(resolution,[],[f42,f72])).
% 3.32/0.79  fof(f72,plain,(
% 3.32/0.79    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 3.32/0.79    inference(resolution,[],[f41,f34])).
% 3.32/0.79  fof(f34,plain,(
% 3.32/0.79    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.32/0.79    inference(cnf_transformation,[],[f8])).
% 3.32/0.79  fof(f8,axiom,(
% 3.32/0.79    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.32/0.79  fof(f1743,plain,(
% 3.32/0.79    ~spl5_20 | spl5_3),
% 3.32/0.79    inference(avatar_split_clause,[],[f1664,f62,f1740])).
% 3.32/0.79  fof(f1740,plain,(
% 3.32/0.79    spl5_20 <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 3.32/0.79  fof(f1664,plain,(
% 3.32/0.79    sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl5_3),
% 3.32/0.79    inference(resolution,[],[f112,f64])).
% 3.32/0.79  fof(f112,plain,(
% 3.32/0.79    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | k4_xboole_0(X2,X3) != X2) )),
% 3.32/0.79    inference(resolution,[],[f43,f41])).
% 3.32/0.79  fof(f43,plain,(
% 3.32/0.79    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 3.32/0.79    inference(cnf_transformation,[],[f26])).
% 3.32/0.79  fof(f1659,plain,(
% 3.32/0.79    spl5_19 | ~spl5_16),
% 3.32/0.79    inference(avatar_split_clause,[],[f1613,f1586,f1656])).
% 3.32/0.79  fof(f1656,plain,(
% 3.32/0.79    spl5_19 <=> r1_xboole_0(k1_tarski(sK3),sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 3.32/0.79  fof(f1613,plain,(
% 3.32/0.79    r1_xboole_0(k1_tarski(sK3),sK1) | ~spl5_16),
% 3.32/0.79    inference(superposition,[],[f72,f1588])).
% 3.32/0.79  fof(f1654,plain,(
% 3.32/0.79    spl5_18 | ~spl5_16),
% 3.32/0.79    inference(avatar_split_clause,[],[f1609,f1586,f1651])).
% 3.32/0.79  fof(f1651,plain,(
% 3.32/0.79    spl5_18 <=> r1_xboole_0(sK1,k1_tarski(sK3))),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 3.32/0.79  fof(f1609,plain,(
% 3.32/0.79    r1_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_16),
% 3.32/0.79    inference(superposition,[],[f34,f1588])).
% 3.32/0.79  fof(f1648,plain,(
% 3.32/0.79    ~spl5_17 | ~spl5_16),
% 3.32/0.79    inference(avatar_split_clause,[],[f1636,f1586,f1645])).
% 3.32/0.79  fof(f1645,plain,(
% 3.32/0.79    spl5_17 <=> r2_hidden(sK3,sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 3.32/0.79  fof(f1636,plain,(
% 3.32/0.79    ~r2_hidden(sK3,sK1) | ~spl5_16),
% 3.32/0.79    inference(trivial_inequality_removal,[],[f1607])).
% 3.32/0.79  fof(f1607,plain,(
% 3.32/0.79    sK1 != sK1 | ~r2_hidden(sK3,sK1) | ~spl5_16),
% 3.32/0.79    inference(superposition,[],[f44,f1588])).
% 3.32/0.79  fof(f44,plain,(
% 3.32/0.79    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 3.32/0.79    inference(cnf_transformation,[],[f27])).
% 3.32/0.79  fof(f27,plain,(
% 3.32/0.79    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 3.32/0.79    inference(nnf_transformation,[],[f12])).
% 3.32/0.79  fof(f12,axiom,(
% 3.32/0.79    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 3.32/0.79  fof(f1589,plain,(
% 3.32/0.79    spl5_16 | ~spl5_1 | ~spl5_2),
% 3.32/0.79    inference(avatar_split_clause,[],[f1559,f57,f52,f1586])).
% 3.32/0.79  fof(f52,plain,(
% 3.32/0.79    spl5_1 <=> r2_hidden(sK3,sK2)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 3.32/0.79  fof(f57,plain,(
% 3.32/0.79    spl5_2 <=> r1_xboole_0(sK2,sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 3.32/0.79  fof(f1559,plain,(
% 3.32/0.79    sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) | (~spl5_1 | ~spl5_2)),
% 3.32/0.79    inference(resolution,[],[f1003,f59])).
% 3.32/0.79  fof(f59,plain,(
% 3.32/0.79    r1_xboole_0(sK2,sK1) | ~spl5_2),
% 3.32/0.79    inference(avatar_component_clause,[],[f57])).
% 3.32/0.79  fof(f1003,plain,(
% 3.32/0.79    ( ! [X3] : (~r1_xboole_0(sK2,X3) | k4_xboole_0(X3,k1_tarski(sK3)) = X3) ) | ~spl5_1),
% 3.32/0.79    inference(resolution,[],[f45,f635])).
% 3.32/0.79  fof(f635,plain,(
% 3.32/0.79    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl5_1),
% 3.32/0.79    inference(resolution,[],[f40,f54])).
% 3.32/0.79  fof(f54,plain,(
% 3.32/0.79    r2_hidden(sK3,sK2) | ~spl5_1),
% 3.32/0.79    inference(avatar_component_clause,[],[f52])).
% 3.32/0.79  fof(f45,plain,(
% 3.32/0.79    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 3.32/0.79    inference(cnf_transformation,[],[f27])).
% 3.32/0.79  fof(f655,plain,(
% 3.32/0.79    ~spl5_15 | ~spl5_11 | spl5_14),
% 3.32/0.79    inference(avatar_split_clause,[],[f650,f646,f290,f652])).
% 3.32/0.79  fof(f652,plain,(
% 3.32/0.79    spl5_15 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 3.32/0.79  fof(f290,plain,(
% 3.32/0.79    spl5_11 <=> k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 3.32/0.79  fof(f646,plain,(
% 3.32/0.79    spl5_14 <=> sK2 = k4_xboole_0(sK2,sK2)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 3.32/0.79  fof(f650,plain,(
% 3.32/0.79    sK2 != k3_xboole_0(sK1,sK2) | (~spl5_11 | spl5_14)),
% 3.32/0.79    inference(superposition,[],[f648,f292])).
% 3.32/0.79  fof(f292,plain,(
% 3.32/0.79    k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) | ~spl5_11),
% 3.32/0.79    inference(avatar_component_clause,[],[f290])).
% 3.32/0.79  fof(f648,plain,(
% 3.32/0.79    sK2 != k4_xboole_0(sK2,sK2) | spl5_14),
% 3.32/0.79    inference(avatar_component_clause,[],[f646])).
% 3.32/0.79  fof(f649,plain,(
% 3.32/0.79    ~spl5_14 | spl5_13),
% 3.32/0.79    inference(avatar_split_clause,[],[f644,f640,f646])).
% 3.32/0.79  fof(f640,plain,(
% 3.32/0.79    spl5_13 <=> r1_xboole_0(sK2,sK2)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 3.32/0.79  fof(f644,plain,(
% 3.32/0.79    sK2 != k4_xboole_0(sK2,sK2) | spl5_13),
% 3.32/0.79    inference(resolution,[],[f642,f43])).
% 3.32/0.79  fof(f642,plain,(
% 3.32/0.79    ~r1_xboole_0(sK2,sK2) | spl5_13),
% 3.32/0.79    inference(avatar_component_clause,[],[f640])).
% 3.32/0.79  fof(f643,plain,(
% 3.32/0.79    ~spl5_13 | ~spl5_1),
% 3.32/0.79    inference(avatar_split_clause,[],[f638,f52,f640])).
% 3.32/0.79  fof(f638,plain,(
% 3.32/0.79    ~r1_xboole_0(sK2,sK2) | ~spl5_1),
% 3.32/0.79    inference(resolution,[],[f635,f54])).
% 3.32/0.79  fof(f312,plain,(
% 3.32/0.79    spl5_12 | ~spl5_8),
% 3.32/0.79    inference(avatar_split_clause,[],[f208,f98,f309])).
% 3.32/0.79  fof(f98,plain,(
% 3.32/0.79    spl5_8 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 3.32/0.79  fof(f208,plain,(
% 3.32/0.79    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | ~spl5_8),
% 3.32/0.79    inference(superposition,[],[f36,f100])).
% 3.32/0.79  fof(f100,plain,(
% 3.32/0.79    sK1 = k4_xboole_0(sK1,sK2) | ~spl5_8),
% 3.32/0.79    inference(avatar_component_clause,[],[f98])).
% 3.32/0.79  fof(f293,plain,(
% 3.32/0.79    spl5_11 | ~spl5_6),
% 3.32/0.79    inference(avatar_split_clause,[],[f233,f85,f290])).
% 3.32/0.79  fof(f85,plain,(
% 3.32/0.79    spl5_6 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 3.32/0.79  fof(f233,plain,(
% 3.32/0.79    k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) | ~spl5_6),
% 3.32/0.79    inference(forward_demodulation,[],[f207,f35])).
% 3.32/0.79  fof(f207,plain,(
% 3.32/0.79    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) | ~spl5_6),
% 3.32/0.79    inference(superposition,[],[f36,f87])).
% 3.32/0.79  fof(f87,plain,(
% 3.32/0.79    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_6),
% 3.32/0.79    inference(avatar_component_clause,[],[f85])).
% 3.32/0.79  fof(f123,plain,(
% 3.32/0.79    ~spl5_10 | spl5_3),
% 3.32/0.79    inference(avatar_split_clause,[],[f110,f62,f120])).
% 3.32/0.79  fof(f120,plain,(
% 3.32/0.79    spl5_10 <=> k2_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 3.32/0.79  fof(f110,plain,(
% 3.32/0.79    k2_xboole_0(sK0,sK2) != k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 3.32/0.79    inference(resolution,[],[f43,f64])).
% 3.32/0.79  fof(f109,plain,(
% 3.32/0.79    spl5_9 | ~spl5_8),
% 3.32/0.79    inference(avatar_split_clause,[],[f104,f98,f106])).
% 3.32/0.79  fof(f106,plain,(
% 3.32/0.79    spl5_9 <=> r1_tarski(sK1,sK1)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 3.32/0.79  fof(f104,plain,(
% 3.32/0.79    r1_tarski(sK1,sK1) | ~spl5_8),
% 3.32/0.79    inference(superposition,[],[f33,f100])).
% 3.32/0.79  fof(f101,plain,(
% 3.32/0.79    spl5_8 | ~spl5_5),
% 3.32/0.79    inference(avatar_split_clause,[],[f82,f74,f98])).
% 3.32/0.79  fof(f82,plain,(
% 3.32/0.79    sK1 = k4_xboole_0(sK1,sK2) | ~spl5_5),
% 3.32/0.79    inference(resolution,[],[f42,f76])).
% 3.32/0.79  fof(f96,plain,(
% 3.32/0.79    spl5_7 | ~spl5_6),
% 3.32/0.79    inference(avatar_split_clause,[],[f91,f85,f93])).
% 3.32/0.79  fof(f93,plain,(
% 3.32/0.79    spl5_7 <=> r1_tarski(sK2,sK2)),
% 3.32/0.79    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 3.32/0.79  fof(f91,plain,(
% 3.32/0.79    r1_tarski(sK2,sK2) | ~spl5_6),
% 3.32/0.79    inference(superposition,[],[f33,f87])).
% 3.32/0.79  fof(f88,plain,(
% 3.32/0.79    spl5_6 | ~spl5_2),
% 3.32/0.79    inference(avatar_split_clause,[],[f83,f57,f85])).
% 3.32/0.79  fof(f83,plain,(
% 3.32/0.79    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_2),
% 3.32/0.79    inference(resolution,[],[f42,f59])).
% 3.32/0.79  fof(f77,plain,(
% 3.32/0.79    spl5_5 | ~spl5_2),
% 3.32/0.79    inference(avatar_split_clause,[],[f71,f57,f74])).
% 3.32/0.79  fof(f71,plain,(
% 3.32/0.79    r1_xboole_0(sK1,sK2) | ~spl5_2),
% 3.32/0.79    inference(resolution,[],[f41,f59])).
% 3.32/0.79  fof(f70,plain,(
% 3.32/0.79    spl5_4),
% 3.32/0.79    inference(avatar_split_clause,[],[f28,f67])).
% 3.32/0.79  fof(f28,plain,(
% 3.32/0.79    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 3.32/0.79    inference(cnf_transformation,[],[f23])).
% 3.32/0.79  fof(f23,plain,(
% 3.32/0.79    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 3.32/0.79    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f22])).
% 3.32/0.79  fof(f22,plain,(
% 3.32/0.79    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 3.32/0.79    introduced(choice_axiom,[])).
% 3.32/0.79  fof(f17,plain,(
% 3.32/0.79    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 3.32/0.79    inference(flattening,[],[f16])).
% 3.32/0.79  fof(f16,plain,(
% 3.32/0.79    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 3.32/0.79    inference(ennf_transformation,[],[f14])).
% 3.32/0.79  fof(f14,negated_conjecture,(
% 3.32/0.79    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.32/0.79    inference(negated_conjecture,[],[f13])).
% 3.32/0.79  fof(f13,conjecture,(
% 3.32/0.79    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 3.32/0.79    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 3.32/0.79  fof(f65,plain,(
% 3.32/0.79    ~spl5_3),
% 3.32/0.79    inference(avatar_split_clause,[],[f31,f62])).
% 3.32/0.79  fof(f31,plain,(
% 3.32/0.79    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 3.32/0.79    inference(cnf_transformation,[],[f23])).
% 3.32/0.79  fof(f60,plain,(
% 3.32/0.79    spl5_2),
% 3.32/0.79    inference(avatar_split_clause,[],[f30,f57])).
% 3.32/0.79  fof(f30,plain,(
% 3.32/0.79    r1_xboole_0(sK2,sK1)),
% 3.32/0.79    inference(cnf_transformation,[],[f23])).
% 3.32/0.79  fof(f55,plain,(
% 3.32/0.79    spl5_1),
% 3.32/0.79    inference(avatar_split_clause,[],[f29,f52])).
% 3.32/0.79  fof(f29,plain,(
% 3.32/0.79    r2_hidden(sK3,sK2)),
% 3.32/0.79    inference(cnf_transformation,[],[f23])).
% 3.32/0.79  % SZS output end Proof for theBenchmark
% 3.32/0.79  % (16606)------------------------------
% 3.32/0.79  % (16606)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.32/0.79  % (16606)Termination reason: Refutation
% 3.32/0.79  
% 3.32/0.79  % (16606)Memory used [KB]: 8571
% 3.32/0.79  % (16606)Time elapsed: 0.372 s
% 3.32/0.79  % (16606)------------------------------
% 3.32/0.79  % (16606)------------------------------
% 3.32/0.80  % (16605)Success in time 0.441 s
%------------------------------------------------------------------------------
