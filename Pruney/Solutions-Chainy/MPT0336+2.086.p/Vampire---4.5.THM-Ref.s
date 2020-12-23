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
% DateTime   : Thu Dec  3 12:43:35 EST 2020

% Result     : Theorem 2.14s
% Output     : Refutation 2.14s
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
fof(f4488,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f88,f96,f101,f112,f123,f278,f296,f391,f397,f403,f1297,f1601,f1660,f1666,f1687,f1767,f1822,f1829,f1898,f2748,f2816,f4120,f4261,f4266,f4275,f4281,f4286,f4487])).

fof(f4487,plain,
    ( spl5_3
    | ~ spl5_5
    | ~ spl5_28 ),
    inference(avatar_contradiction_clause,[],[f4486])).

fof(f4486,plain,
    ( $false
    | spl5_3
    | ~ spl5_5
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f4485,f4260])).

fof(f4260,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f4258])).

fof(f4258,plain,
    ( spl5_28
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f4485,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f4478,f76])).

fof(f76,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f74])).

fof(f74,plain,
    ( spl5_5
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f4478,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0)
    | spl5_3 ),
    inference(resolution,[],[f1002,f64])).

fof(f64,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f1002,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f4286,plain,
    ( spl5_32
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f4269,f4263,f4283])).

fof(f4283,plain,
    ( spl5_32
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f4263,plain,
    ( spl5_29
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f4269,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_29 ),
    inference(resolution,[],[f4265,f42])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f4265,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f4263])).

fof(f4281,plain,
    ( spl5_31
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f4267,f4258,f4278])).

fof(f4278,plain,
    ( spl5_31
  <=> sK1 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f4267,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl5_28 ),
    inference(resolution,[],[f4260,f42])).

fof(f4275,plain,
    ( spl5_30
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f4241,f4117,f4272])).

fof(f4272,plain,
    ( spl5_30
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f4117,plain,
    ( spl5_27
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f4241,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_27 ),
    inference(superposition,[],[f256,f4119])).

fof(f4119,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f4117])).

fof(f256,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f201,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f201,plain,(
    ! [X2,X1] : r1_tarski(k3_xboole_0(X1,X2),X1) ),
    inference(superposition,[],[f33,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f4266,plain,
    ( spl5_29
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f4233,f4117,f4263])).

fof(f4233,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_27 ),
    inference(superposition,[],[f258,f4119])).

fof(f258,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
    inference(resolution,[],[f256,f50])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).

fof(f4261,plain,
    ( spl5_28
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f4231,f4117,f4258])).

fof(f4231,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_27 ),
    inference(superposition,[],[f1242,f4119])).

fof(f1242,plain,(
    ! [X4,X5,X3] : r1_xboole_0(X3,k3_xboole_0(X4,k4_xboole_0(X5,X3))) ),
    inference(resolution,[],[f258,f41])).

fof(f4120,plain,
    ( spl5_27
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f3957,f1895,f4117])).

fof(f1895,plain,
    ( spl5_24
  <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f3957,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_24 ),
    inference(superposition,[],[f3714,f198])).

fof(f198,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f37,f37])).

fof(f3714,plain,
    ( ! [X0] : k4_xboole_0(X0,k3_xboole_0(sK0,sK1)) = X0
    | ~ spl5_24 ),
    inference(resolution,[],[f3710,f42])).

fof(f3710,plain,
    ( ! [X1] : r1_xboole_0(X1,k3_xboole_0(sK0,sK1))
    | ~ spl5_24 ),
    inference(resolution,[],[f3700,f41])).

fof(f3700,plain,
    ( ! [X10] : r1_xboole_0(k3_xboole_0(sK0,sK1),X10)
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f3678,f256])).

fof(f3678,plain,
    ( ! [X10] :
        ( r1_xboole_0(k3_xboole_0(sK0,sK1),X10)
        | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1) )
    | ~ spl5_24 ),
    inference(resolution,[],[f3672,f1922])).

fof(f1922,plain,
    ( ! [X13] :
        ( r1_xboole_0(X13,k3_xboole_0(sK0,sK1))
        | ~ r1_tarski(X13,sK1) )
    | ~ spl5_24 ),
    inference(superposition,[],[f50,f1897])).

fof(f1897,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f1895])).

fof(f3672,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f3668])).

fof(f3668,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f384,f38])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f384,plain,(
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

fof(f2816,plain,
    ( spl5_26
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f2799,f2745,f2813])).

fof(f2813,plain,
    ( spl5_26
  <=> r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f2745,plain,
    ( spl5_25
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f2799,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK3))
    | ~ spl5_25 ),
    inference(superposition,[],[f256,f2747])).

fof(f2747,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f2745])).

fof(f2748,plain,
    ( spl5_25
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f1649,f1598,f293,f2745])).

fof(f293,plain,
    ( spl5_12
  <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f1598,plain,
    ( spl5_17
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f1649,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_12
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f1622,f295])).

fof(f295,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f293])).

fof(f1622,plain,
    ( k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_17 ),
    inference(superposition,[],[f37,f1600])).

fof(f1600,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f1598])).

fof(f1898,plain,
    ( spl5_24
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f1830,f1826,f1895])).

fof(f1826,plain,
    ( spl5_23
  <=> r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f1830,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_23 ),
    inference(resolution,[],[f1828,f42])).

fof(f1828,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f1826])).

fof(f1829,plain,
    ( spl5_23
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f1824,f1819,f1826])).

fof(f1819,plain,
    ( spl5_22
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f1824,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_22 ),
    inference(resolution,[],[f1821,f41])).

fof(f1821,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f1819])).

fof(f1822,plain,
    ( spl5_22
    | ~ spl5_4
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f1805,f1764,f67,f1819])).

fof(f67,plain,
    ( spl5_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1764,plain,
    ( spl5_21
  <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f1805,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_4
    | ~ spl5_21 ),
    inference(resolution,[],[f1774,f69])).

fof(f69,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f1774,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,k1_tarski(sK3))
        | r1_xboole_0(X1,sK1) )
    | ~ spl5_21 ),
    inference(superposition,[],[f50,f1766])).

fof(f1766,plain,
    ( k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f1764])).

fof(f1767,plain,
    ( spl5_21
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f1626,f1598,f1764])).

fof(f1626,plain,
    ( k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_17 ),
    inference(superposition,[],[f80,f1600])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f1687,plain,
    ( spl5_20
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f1625,f1598,f1684])).

fof(f1684,plain,
    ( spl5_20
  <=> r1_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f1625,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_17 ),
    inference(superposition,[],[f72,f1600])).

fof(f1666,plain,
    ( spl5_19
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f1621,f1598,f1663])).

fof(f1663,plain,
    ( spl5_19
  <=> r1_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f1621,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_17 ),
    inference(superposition,[],[f34,f1600])).

fof(f1660,plain,
    ( ~ spl5_18
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f1648,f1598,f1657])).

fof(f1657,plain,
    ( spl5_18
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f1648,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl5_17 ),
    inference(trivial_inequality_removal,[],[f1619])).

fof(f1619,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK3,sK1)
    | ~ spl5_17 ),
    inference(superposition,[],[f44,f1600])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

fof(f1601,plain,
    ( spl5_17
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f1570,f57,f52,f1598])).

fof(f52,plain,
    ( spl5_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f57,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1570,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f780,f59])).

fof(f59,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f780,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(sK2,X3)
        | k4_xboole_0(X3,k1_tarski(sK3)) = X3 )
    | ~ spl5_1 ),
    inference(resolution,[],[f45,f383])).

fof(f383,plain,
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

fof(f1297,plain,
    ( ~ spl5_16
    | spl5_3 ),
    inference(avatar_split_clause,[],[f1287,f62,f1294])).

fof(f1294,plain,
    ( spl5_16
  <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f1287,plain,
    ( sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl5_3 ),
    inference(resolution,[],[f107,f64])).

fof(f107,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | k4_xboole_0(X2,X3) != X2 ) ),
    inference(resolution,[],[f43,f41])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f403,plain,
    ( ~ spl5_15
    | ~ spl5_11
    | spl5_14 ),
    inference(avatar_split_clause,[],[f398,f394,f275,f400])).

fof(f400,plain,
    ( spl5_15
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f275,plain,
    ( spl5_11
  <=> k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f394,plain,
    ( spl5_14
  <=> sK2 = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f398,plain,
    ( sK2 != k3_xboole_0(sK1,sK2)
    | ~ spl5_11
    | spl5_14 ),
    inference(superposition,[],[f396,f277])).

fof(f277,plain,
    ( k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f275])).

fof(f396,plain,
    ( sK2 != k4_xboole_0(sK2,sK2)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f394])).

fof(f397,plain,
    ( ~ spl5_14
    | spl5_13 ),
    inference(avatar_split_clause,[],[f392,f388,f394])).

fof(f388,plain,
    ( spl5_13
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f392,plain,
    ( sK2 != k4_xboole_0(sK2,sK2)
    | spl5_13 ),
    inference(resolution,[],[f390,f43])).

fof(f390,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f388])).

fof(f391,plain,
    ( ~ spl5_13
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f386,f52,f388])).

fof(f386,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f383,f54])).

fof(f296,plain,
    ( spl5_12
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f196,f98,f293])).

fof(f98,plain,
    ( spl5_8
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f196,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl5_8 ),
    inference(superposition,[],[f37,f100])).

fof(f100,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f278,plain,
    ( spl5_11
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f219,f85,f275])).

fof(f85,plain,
    ( spl5_6
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f219,plain,
    ( k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f195,f35])).

fof(f195,plain,
    ( k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f37,f87])).

fof(f87,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f123,plain,
    ( ~ spl5_10
    | spl5_3 ),
    inference(avatar_split_clause,[],[f105,f62,f120])).

fof(f120,plain,
    ( spl5_10
  <=> k2_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f105,plain,
    ( k2_xboole_0(sK0,sK2) != k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(resolution,[],[f43,f64])).

fof(f112,plain,
    ( spl5_9
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f104,f98,f109])).

fof(f109,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

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
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (21333)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.42  % (21325)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (21324)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (21329)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.46  % (21330)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.47  % (21328)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (21332)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.48  % (21337)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.48  % (21338)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (21336)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.49  % (21334)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (21335)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.49  % (21327)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.50  % (21326)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.50  % (21339)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.50  % (21341)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.51  % (21340)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.51  % (21331)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 2.14/0.63  % (21324)Refutation found. Thanks to Tanya!
% 2.14/0.63  % SZS status Theorem for theBenchmark
% 2.14/0.63  % SZS output start Proof for theBenchmark
% 2.14/0.63  fof(f4488,plain,(
% 2.14/0.63    $false),
% 2.14/0.63    inference(avatar_sat_refutation,[],[f55,f60,f65,f70,f77,f88,f96,f101,f112,f123,f278,f296,f391,f397,f403,f1297,f1601,f1660,f1666,f1687,f1767,f1822,f1829,f1898,f2748,f2816,f4120,f4261,f4266,f4275,f4281,f4286,f4487])).
% 2.14/0.63  fof(f4487,plain,(
% 2.14/0.63    spl5_3 | ~spl5_5 | ~spl5_28),
% 2.14/0.63    inference(avatar_contradiction_clause,[],[f4486])).
% 2.14/0.63  fof(f4486,plain,(
% 2.14/0.63    $false | (spl5_3 | ~spl5_5 | ~spl5_28)),
% 2.14/0.63    inference(subsumption_resolution,[],[f4485,f4260])).
% 2.14/0.63  fof(f4260,plain,(
% 2.14/0.63    r1_xboole_0(sK1,sK0) | ~spl5_28),
% 2.14/0.63    inference(avatar_component_clause,[],[f4258])).
% 2.14/0.63  fof(f4258,plain,(
% 2.14/0.63    spl5_28 <=> r1_xboole_0(sK1,sK0)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.14/0.63  fof(f4485,plain,(
% 2.14/0.63    ~r1_xboole_0(sK1,sK0) | (spl5_3 | ~spl5_5)),
% 2.14/0.63    inference(subsumption_resolution,[],[f4478,f76])).
% 2.14/0.63  fof(f76,plain,(
% 2.14/0.63    r1_xboole_0(sK1,sK2) | ~spl5_5),
% 2.14/0.63    inference(avatar_component_clause,[],[f74])).
% 2.14/0.63  fof(f74,plain,(
% 2.14/0.63    spl5_5 <=> r1_xboole_0(sK1,sK2)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.14/0.63  fof(f4478,plain,(
% 2.14/0.63    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0) | spl5_3),
% 2.14/0.63    inference(resolution,[],[f1002,f64])).
% 2.14/0.63  fof(f64,plain,(
% 2.14/0.63    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 2.14/0.63    inference(avatar_component_clause,[],[f62])).
% 2.14/0.63  fof(f62,plain,(
% 2.14/0.63    spl5_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.14/0.63  fof(f1002,plain,(
% 2.14/0.63    ( ! [X10,X11,X9] : (r1_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10)) )),
% 2.14/0.63    inference(resolution,[],[f46,f41])).
% 2.14/0.63  fof(f41,plain,(
% 2.14/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f19])).
% 2.14/0.63  fof(f19,plain,(
% 2.14/0.63    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.14/0.63    inference(ennf_transformation,[],[f2])).
% 2.14/0.63  fof(f2,axiom,(
% 2.14/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.14/0.63  fof(f46,plain,(
% 2.14/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f20])).
% 2.14/0.63  fof(f20,plain,(
% 2.14/0.63    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.14/0.63    inference(ennf_transformation,[],[f7])).
% 2.14/0.63  fof(f7,axiom,(
% 2.14/0.63    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.14/0.63  fof(f4286,plain,(
% 2.14/0.63    spl5_32 | ~spl5_29),
% 2.14/0.63    inference(avatar_split_clause,[],[f4269,f4263,f4283])).
% 2.14/0.63  fof(f4283,plain,(
% 2.14/0.63    spl5_32 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.14/0.63  fof(f4263,plain,(
% 2.14/0.63    spl5_29 <=> r1_xboole_0(sK0,sK1)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.14/0.63  fof(f4269,plain,(
% 2.14/0.63    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_29),
% 2.14/0.63    inference(resolution,[],[f4265,f42])).
% 2.14/0.63  fof(f42,plain,(
% 2.14/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.14/0.63    inference(cnf_transformation,[],[f26])).
% 2.14/0.63  fof(f26,plain,(
% 2.14/0.63    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.14/0.63    inference(nnf_transformation,[],[f9])).
% 2.14/0.63  fof(f9,axiom,(
% 2.14/0.63    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.14/0.63  fof(f4265,plain,(
% 2.14/0.63    r1_xboole_0(sK0,sK1) | ~spl5_29),
% 2.14/0.63    inference(avatar_component_clause,[],[f4263])).
% 2.14/0.63  fof(f4281,plain,(
% 2.14/0.63    spl5_31 | ~spl5_28),
% 2.14/0.63    inference(avatar_split_clause,[],[f4267,f4258,f4278])).
% 2.14/0.63  fof(f4278,plain,(
% 2.14/0.63    spl5_31 <=> sK1 = k4_xboole_0(sK1,sK0)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.14/0.63  fof(f4267,plain,(
% 2.14/0.63    sK1 = k4_xboole_0(sK1,sK0) | ~spl5_28),
% 2.14/0.63    inference(resolution,[],[f4260,f42])).
% 2.14/0.63  fof(f4275,plain,(
% 2.14/0.63    spl5_30 | ~spl5_27),
% 2.14/0.63    inference(avatar_split_clause,[],[f4241,f4117,f4272])).
% 2.14/0.63  fof(f4272,plain,(
% 2.14/0.63    spl5_30 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.14/0.63  fof(f4117,plain,(
% 2.14/0.63    spl5_27 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 2.14/0.63  fof(f4241,plain,(
% 2.14/0.63    r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_27),
% 2.14/0.63    inference(superposition,[],[f256,f4119])).
% 2.14/0.63  fof(f4119,plain,(
% 2.14/0.63    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_27),
% 2.14/0.63    inference(avatar_component_clause,[],[f4117])).
% 2.14/0.63  fof(f256,plain,(
% 2.14/0.63    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 2.14/0.63    inference(superposition,[],[f201,f35])).
% 2.14/0.63  fof(f35,plain,(
% 2.14/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f1])).
% 2.14/0.63  fof(f1,axiom,(
% 2.14/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.14/0.63  fof(f201,plain,(
% 2.14/0.63    ( ! [X2,X1] : (r1_tarski(k3_xboole_0(X1,X2),X1)) )),
% 2.14/0.63    inference(superposition,[],[f33,f37])).
% 2.14/0.63  fof(f37,plain,(
% 2.14/0.63    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.14/0.63    inference(cnf_transformation,[],[f6])).
% 2.14/0.63  fof(f6,axiom,(
% 2.14/0.63    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.14/0.63  fof(f33,plain,(
% 2.14/0.63    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f5])).
% 2.14/0.63  fof(f5,axiom,(
% 2.14/0.63    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.14/0.63  fof(f4266,plain,(
% 2.14/0.63    spl5_29 | ~spl5_27),
% 2.14/0.63    inference(avatar_split_clause,[],[f4233,f4117,f4263])).
% 2.14/0.63  fof(f4233,plain,(
% 2.14/0.63    r1_xboole_0(sK0,sK1) | ~spl5_27),
% 2.14/0.63    inference(superposition,[],[f258,f4119])).
% 2.14/0.63  fof(f258,plain,(
% 2.14/0.63    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),X2)) )),
% 2.14/0.63    inference(resolution,[],[f256,f50])).
% 2.14/0.63  fof(f50,plain,(
% 2.14/0.63    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f21])).
% 2.14/0.63  fof(f21,plain,(
% 2.14/0.63    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.14/0.63    inference(ennf_transformation,[],[f4])).
% 2.14/0.63  fof(f4,axiom,(
% 2.14/0.63    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.14/0.63  fof(f4261,plain,(
% 2.14/0.63    spl5_28 | ~spl5_27),
% 2.14/0.63    inference(avatar_split_clause,[],[f4231,f4117,f4258])).
% 2.14/0.63  fof(f4231,plain,(
% 2.14/0.63    r1_xboole_0(sK1,sK0) | ~spl5_27),
% 2.14/0.63    inference(superposition,[],[f1242,f4119])).
% 2.14/0.63  fof(f1242,plain,(
% 2.14/0.63    ( ! [X4,X5,X3] : (r1_xboole_0(X3,k3_xboole_0(X4,k4_xboole_0(X5,X3)))) )),
% 2.14/0.63    inference(resolution,[],[f258,f41])).
% 2.14/0.63  fof(f4120,plain,(
% 2.14/0.63    spl5_27 | ~spl5_24),
% 2.14/0.63    inference(avatar_split_clause,[],[f3957,f1895,f4117])).
% 2.14/0.63  fof(f1895,plain,(
% 2.14/0.63    spl5_24 <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 2.14/0.63  fof(f3957,plain,(
% 2.14/0.63    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_24),
% 2.14/0.63    inference(superposition,[],[f3714,f198])).
% 2.14/0.63  fof(f198,plain,(
% 2.14/0.63    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 2.14/0.63    inference(superposition,[],[f37,f37])).
% 2.14/0.63  fof(f3714,plain,(
% 2.14/0.63    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(sK0,sK1)) = X0) ) | ~spl5_24),
% 2.14/0.63    inference(resolution,[],[f3710,f42])).
% 2.14/0.63  fof(f3710,plain,(
% 2.14/0.63    ( ! [X1] : (r1_xboole_0(X1,k3_xboole_0(sK0,sK1))) ) | ~spl5_24),
% 2.14/0.63    inference(resolution,[],[f3700,f41])).
% 2.14/0.63  fof(f3700,plain,(
% 2.14/0.63    ( ! [X10] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X10)) ) | ~spl5_24),
% 2.14/0.63    inference(subsumption_resolution,[],[f3678,f256])).
% 2.14/0.63  fof(f3678,plain,(
% 2.14/0.63    ( ! [X10] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X10) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1)) ) | ~spl5_24),
% 2.14/0.63    inference(resolution,[],[f3672,f1922])).
% 2.14/0.63  fof(f1922,plain,(
% 2.14/0.63    ( ! [X13] : (r1_xboole_0(X13,k3_xboole_0(sK0,sK1)) | ~r1_tarski(X13,sK1)) ) | ~spl5_24),
% 2.14/0.63    inference(superposition,[],[f50,f1897])).
% 2.14/0.63  fof(f1897,plain,(
% 2.14/0.63    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_24),
% 2.14/0.63    inference(avatar_component_clause,[],[f1895])).
% 2.14/0.63  fof(f3672,plain,(
% 2.14/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 2.14/0.63    inference(duplicate_literal_removal,[],[f3668])).
% 2.14/0.63  fof(f3668,plain,(
% 2.14/0.63    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 2.14/0.63    inference(resolution,[],[f384,f38])).
% 2.14/0.63  fof(f38,plain,(
% 2.14/0.63    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f25])).
% 2.14/0.63  fof(f25,plain,(
% 2.14/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.14/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f24])).
% 2.14/0.63  fof(f24,plain,(
% 2.14/0.63    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.14/0.63    introduced(choice_axiom,[])).
% 2.14/0.63  fof(f18,plain,(
% 2.14/0.63    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.14/0.63    inference(ennf_transformation,[],[f15])).
% 2.14/0.63  fof(f15,plain,(
% 2.14/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.14/0.63    inference(rectify,[],[f3])).
% 2.14/0.63  fof(f3,axiom,(
% 2.14/0.63    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.14/0.63  fof(f384,plain,(
% 2.14/0.63    ( ! [X2,X3,X1] : (~r2_hidden(sK4(X1,X2),X3) | ~r1_xboole_0(X1,X3) | r1_xboole_0(X1,X2)) )),
% 2.14/0.63    inference(resolution,[],[f40,f38])).
% 2.14/0.63  fof(f40,plain,(
% 2.14/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f25])).
% 2.14/0.63  fof(f2816,plain,(
% 2.14/0.63    spl5_26 | ~spl5_25),
% 2.14/0.63    inference(avatar_split_clause,[],[f2799,f2745,f2813])).
% 2.14/0.63  fof(f2813,plain,(
% 2.14/0.63    spl5_26 <=> r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK3))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.14/0.63  fof(f2745,plain,(
% 2.14/0.63    spl5_25 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.14/0.63  fof(f2799,plain,(
% 2.14/0.63    r1_tarski(k3_xboole_0(sK1,sK2),k1_tarski(sK3)) | ~spl5_25),
% 2.14/0.63    inference(superposition,[],[f256,f2747])).
% 2.14/0.63  fof(f2747,plain,(
% 2.14/0.63    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_25),
% 2.14/0.63    inference(avatar_component_clause,[],[f2745])).
% 2.14/0.63  fof(f2748,plain,(
% 2.14/0.63    spl5_25 | ~spl5_12 | ~spl5_17),
% 2.14/0.63    inference(avatar_split_clause,[],[f1649,f1598,f293,f2745])).
% 2.14/0.63  fof(f293,plain,(
% 2.14/0.63    spl5_12 <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.14/0.63  fof(f1598,plain,(
% 2.14/0.63    spl5_17 <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK3))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.14/0.63  fof(f1649,plain,(
% 2.14/0.63    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3)) | (~spl5_12 | ~spl5_17)),
% 2.14/0.63    inference(forward_demodulation,[],[f1622,f295])).
% 2.14/0.63  fof(f295,plain,(
% 2.14/0.63    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | ~spl5_12),
% 2.14/0.63    inference(avatar_component_clause,[],[f293])).
% 2.14/0.63  fof(f1622,plain,(
% 2.14/0.63    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_17),
% 2.14/0.63    inference(superposition,[],[f37,f1600])).
% 2.14/0.63  fof(f1600,plain,(
% 2.14/0.63    sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_17),
% 2.14/0.63    inference(avatar_component_clause,[],[f1598])).
% 2.14/0.63  fof(f1898,plain,(
% 2.14/0.63    spl5_24 | ~spl5_23),
% 2.14/0.63    inference(avatar_split_clause,[],[f1830,f1826,f1895])).
% 2.14/0.63  fof(f1826,plain,(
% 2.14/0.63    spl5_23 <=> r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.14/0.63  fof(f1830,plain,(
% 2.14/0.63    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_23),
% 2.14/0.63    inference(resolution,[],[f1828,f42])).
% 2.14/0.63  fof(f1828,plain,(
% 2.14/0.63    r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_23),
% 2.14/0.63    inference(avatar_component_clause,[],[f1826])).
% 2.14/0.63  fof(f1829,plain,(
% 2.14/0.63    spl5_23 | ~spl5_22),
% 2.14/0.63    inference(avatar_split_clause,[],[f1824,f1819,f1826])).
% 2.14/0.63  fof(f1819,plain,(
% 2.14/0.63    spl5_22 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.14/0.63  fof(f1824,plain,(
% 2.14/0.63    r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_22),
% 2.14/0.63    inference(resolution,[],[f1821,f41])).
% 2.14/0.63  fof(f1821,plain,(
% 2.14/0.63    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | ~spl5_22),
% 2.14/0.63    inference(avatar_component_clause,[],[f1819])).
% 2.14/0.63  fof(f1822,plain,(
% 2.14/0.63    spl5_22 | ~spl5_4 | ~spl5_21),
% 2.14/0.63    inference(avatar_split_clause,[],[f1805,f1764,f67,f1819])).
% 2.14/0.63  fof(f67,plain,(
% 2.14/0.63    spl5_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.14/0.63  fof(f1764,plain,(
% 2.14/0.63    spl5_21 <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.14/0.63  fof(f1805,plain,(
% 2.14/0.63    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | (~spl5_4 | ~spl5_21)),
% 2.14/0.63    inference(resolution,[],[f1774,f69])).
% 2.14/0.63  fof(f69,plain,(
% 2.14/0.63    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl5_4),
% 2.14/0.63    inference(avatar_component_clause,[],[f67])).
% 2.14/0.63  fof(f1774,plain,(
% 2.14/0.63    ( ! [X1] : (~r1_tarski(X1,k1_tarski(sK3)) | r1_xboole_0(X1,sK1)) ) | ~spl5_21),
% 2.14/0.63    inference(superposition,[],[f50,f1766])).
% 2.14/0.63  fof(f1766,plain,(
% 2.14/0.63    k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) | ~spl5_21),
% 2.14/0.63    inference(avatar_component_clause,[],[f1764])).
% 2.14/0.63  fof(f1767,plain,(
% 2.14/0.63    spl5_21 | ~spl5_17),
% 2.14/0.63    inference(avatar_split_clause,[],[f1626,f1598,f1764])).
% 2.14/0.63  fof(f1626,plain,(
% 2.14/0.63    k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) | ~spl5_17),
% 2.14/0.63    inference(superposition,[],[f80,f1600])).
% 2.14/0.63  fof(f80,plain,(
% 2.14/0.63    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 2.14/0.63    inference(resolution,[],[f42,f72])).
% 2.14/0.63  fof(f72,plain,(
% 2.14/0.63    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.14/0.63    inference(resolution,[],[f41,f34])).
% 2.14/0.63  fof(f34,plain,(
% 2.14/0.63    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 2.14/0.63    inference(cnf_transformation,[],[f8])).
% 2.14/0.63  fof(f8,axiom,(
% 2.14/0.63    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 2.14/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 2.14/0.63  fof(f1687,plain,(
% 2.14/0.63    spl5_20 | ~spl5_17),
% 2.14/0.63    inference(avatar_split_clause,[],[f1625,f1598,f1684])).
% 2.14/0.63  fof(f1684,plain,(
% 2.14/0.63    spl5_20 <=> r1_xboole_0(k1_tarski(sK3),sK1)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.14/0.63  fof(f1625,plain,(
% 2.14/0.63    r1_xboole_0(k1_tarski(sK3),sK1) | ~spl5_17),
% 2.14/0.63    inference(superposition,[],[f72,f1600])).
% 2.14/0.63  fof(f1666,plain,(
% 2.14/0.63    spl5_19 | ~spl5_17),
% 2.14/0.63    inference(avatar_split_clause,[],[f1621,f1598,f1663])).
% 2.14/0.63  fof(f1663,plain,(
% 2.14/0.63    spl5_19 <=> r1_xboole_0(sK1,k1_tarski(sK3))),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.14/0.63  fof(f1621,plain,(
% 2.14/0.63    r1_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_17),
% 2.14/0.63    inference(superposition,[],[f34,f1600])).
% 2.14/0.63  fof(f1660,plain,(
% 2.14/0.63    ~spl5_18 | ~spl5_17),
% 2.14/0.63    inference(avatar_split_clause,[],[f1648,f1598,f1657])).
% 2.14/0.63  fof(f1657,plain,(
% 2.14/0.63    spl5_18 <=> r2_hidden(sK3,sK1)),
% 2.14/0.63    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.14/0.64  fof(f1648,plain,(
% 2.14/0.64    ~r2_hidden(sK3,sK1) | ~spl5_17),
% 2.14/0.64    inference(trivial_inequality_removal,[],[f1619])).
% 2.14/0.64  fof(f1619,plain,(
% 2.14/0.64    sK1 != sK1 | ~r2_hidden(sK3,sK1) | ~spl5_17),
% 2.14/0.64    inference(superposition,[],[f44,f1600])).
% 2.14/0.64  fof(f44,plain,(
% 2.14/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 2.14/0.64    inference(cnf_transformation,[],[f27])).
% 2.14/0.64  fof(f27,plain,(
% 2.14/0.64    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 2.14/0.64    inference(nnf_transformation,[],[f12])).
% 2.14/0.64  fof(f12,axiom,(
% 2.14/0.64    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 2.14/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 2.14/0.64  fof(f1601,plain,(
% 2.14/0.64    spl5_17 | ~spl5_1 | ~spl5_2),
% 2.14/0.64    inference(avatar_split_clause,[],[f1570,f57,f52,f1598])).
% 2.14/0.64  fof(f52,plain,(
% 2.14/0.64    spl5_1 <=> r2_hidden(sK3,sK2)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.14/0.64  fof(f57,plain,(
% 2.14/0.64    spl5_2 <=> r1_xboole_0(sK2,sK1)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.14/0.64  fof(f1570,plain,(
% 2.14/0.64    sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) | (~spl5_1 | ~spl5_2)),
% 2.14/0.64    inference(resolution,[],[f780,f59])).
% 2.14/0.64  fof(f59,plain,(
% 2.14/0.64    r1_xboole_0(sK2,sK1) | ~spl5_2),
% 2.14/0.64    inference(avatar_component_clause,[],[f57])).
% 2.14/0.64  fof(f780,plain,(
% 2.14/0.64    ( ! [X3] : (~r1_xboole_0(sK2,X3) | k4_xboole_0(X3,k1_tarski(sK3)) = X3) ) | ~spl5_1),
% 2.14/0.64    inference(resolution,[],[f45,f383])).
% 2.14/0.64  fof(f383,plain,(
% 2.14/0.64    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl5_1),
% 2.14/0.64    inference(resolution,[],[f40,f54])).
% 2.14/0.64  fof(f54,plain,(
% 2.14/0.64    r2_hidden(sK3,sK2) | ~spl5_1),
% 2.14/0.64    inference(avatar_component_clause,[],[f52])).
% 2.14/0.64  fof(f45,plain,(
% 2.14/0.64    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 2.14/0.64    inference(cnf_transformation,[],[f27])).
% 2.14/0.64  fof(f1297,plain,(
% 2.14/0.64    ~spl5_16 | spl5_3),
% 2.14/0.64    inference(avatar_split_clause,[],[f1287,f62,f1294])).
% 2.14/0.64  fof(f1294,plain,(
% 2.14/0.64    spl5_16 <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.14/0.64  fof(f1287,plain,(
% 2.14/0.64    sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl5_3),
% 2.14/0.64    inference(resolution,[],[f107,f64])).
% 2.14/0.64  fof(f107,plain,(
% 2.14/0.64    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | k4_xboole_0(X2,X3) != X2) )),
% 2.14/0.64    inference(resolution,[],[f43,f41])).
% 2.14/0.64  fof(f43,plain,(
% 2.14/0.64    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.14/0.64    inference(cnf_transformation,[],[f26])).
% 2.14/0.64  fof(f403,plain,(
% 2.14/0.64    ~spl5_15 | ~spl5_11 | spl5_14),
% 2.14/0.64    inference(avatar_split_clause,[],[f398,f394,f275,f400])).
% 2.14/0.64  fof(f400,plain,(
% 2.14/0.64    spl5_15 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.14/0.64  fof(f275,plain,(
% 2.14/0.64    spl5_11 <=> k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.14/0.64  fof(f394,plain,(
% 2.14/0.64    spl5_14 <=> sK2 = k4_xboole_0(sK2,sK2)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.14/0.64  fof(f398,plain,(
% 2.14/0.64    sK2 != k3_xboole_0(sK1,sK2) | (~spl5_11 | spl5_14)),
% 2.14/0.64    inference(superposition,[],[f396,f277])).
% 2.14/0.64  fof(f277,plain,(
% 2.14/0.64    k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) | ~spl5_11),
% 2.14/0.64    inference(avatar_component_clause,[],[f275])).
% 2.14/0.64  fof(f396,plain,(
% 2.14/0.64    sK2 != k4_xboole_0(sK2,sK2) | spl5_14),
% 2.14/0.64    inference(avatar_component_clause,[],[f394])).
% 2.14/0.64  fof(f397,plain,(
% 2.14/0.64    ~spl5_14 | spl5_13),
% 2.14/0.64    inference(avatar_split_clause,[],[f392,f388,f394])).
% 2.14/0.64  fof(f388,plain,(
% 2.14/0.64    spl5_13 <=> r1_xboole_0(sK2,sK2)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.14/0.64  fof(f392,plain,(
% 2.14/0.64    sK2 != k4_xboole_0(sK2,sK2) | spl5_13),
% 2.14/0.64    inference(resolution,[],[f390,f43])).
% 2.14/0.64  fof(f390,plain,(
% 2.14/0.64    ~r1_xboole_0(sK2,sK2) | spl5_13),
% 2.14/0.64    inference(avatar_component_clause,[],[f388])).
% 2.14/0.64  fof(f391,plain,(
% 2.14/0.64    ~spl5_13 | ~spl5_1),
% 2.14/0.64    inference(avatar_split_clause,[],[f386,f52,f388])).
% 2.14/0.64  fof(f386,plain,(
% 2.14/0.64    ~r1_xboole_0(sK2,sK2) | ~spl5_1),
% 2.14/0.64    inference(resolution,[],[f383,f54])).
% 2.14/0.64  fof(f296,plain,(
% 2.14/0.64    spl5_12 | ~spl5_8),
% 2.14/0.64    inference(avatar_split_clause,[],[f196,f98,f293])).
% 2.14/0.64  fof(f98,plain,(
% 2.14/0.64    spl5_8 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.14/0.64  fof(f196,plain,(
% 2.14/0.64    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | ~spl5_8),
% 2.14/0.64    inference(superposition,[],[f37,f100])).
% 2.14/0.64  fof(f100,plain,(
% 2.14/0.64    sK1 = k4_xboole_0(sK1,sK2) | ~spl5_8),
% 2.14/0.64    inference(avatar_component_clause,[],[f98])).
% 2.14/0.64  fof(f278,plain,(
% 2.14/0.64    spl5_11 | ~spl5_6),
% 2.14/0.64    inference(avatar_split_clause,[],[f219,f85,f275])).
% 2.14/0.64  fof(f85,plain,(
% 2.14/0.64    spl5_6 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.14/0.64  fof(f219,plain,(
% 2.14/0.64    k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) | ~spl5_6),
% 2.14/0.64    inference(forward_demodulation,[],[f195,f35])).
% 2.14/0.64  fof(f195,plain,(
% 2.14/0.64    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) | ~spl5_6),
% 2.14/0.64    inference(superposition,[],[f37,f87])).
% 2.14/0.64  fof(f87,plain,(
% 2.14/0.64    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_6),
% 2.14/0.64    inference(avatar_component_clause,[],[f85])).
% 2.14/0.64  fof(f123,plain,(
% 2.14/0.64    ~spl5_10 | spl5_3),
% 2.14/0.64    inference(avatar_split_clause,[],[f105,f62,f120])).
% 2.14/0.64  fof(f120,plain,(
% 2.14/0.64    spl5_10 <=> k2_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.14/0.64  fof(f105,plain,(
% 2.14/0.64    k2_xboole_0(sK0,sK2) != k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 2.14/0.64    inference(resolution,[],[f43,f64])).
% 2.14/0.64  fof(f112,plain,(
% 2.14/0.64    spl5_9 | ~spl5_8),
% 2.14/0.64    inference(avatar_split_clause,[],[f104,f98,f109])).
% 2.14/0.64  fof(f109,plain,(
% 2.14/0.64    spl5_9 <=> r1_tarski(sK1,sK1)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.14/0.64  fof(f104,plain,(
% 2.14/0.64    r1_tarski(sK1,sK1) | ~spl5_8),
% 2.14/0.64    inference(superposition,[],[f33,f100])).
% 2.14/0.64  fof(f101,plain,(
% 2.14/0.64    spl5_8 | ~spl5_5),
% 2.14/0.64    inference(avatar_split_clause,[],[f82,f74,f98])).
% 2.14/0.64  fof(f82,plain,(
% 2.14/0.64    sK1 = k4_xboole_0(sK1,sK2) | ~spl5_5),
% 2.14/0.64    inference(resolution,[],[f42,f76])).
% 2.14/0.64  fof(f96,plain,(
% 2.14/0.64    spl5_7 | ~spl5_6),
% 2.14/0.64    inference(avatar_split_clause,[],[f91,f85,f93])).
% 2.14/0.64  fof(f93,plain,(
% 2.14/0.64    spl5_7 <=> r1_tarski(sK2,sK2)),
% 2.14/0.64    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.14/0.64  fof(f91,plain,(
% 2.14/0.64    r1_tarski(sK2,sK2) | ~spl5_6),
% 2.14/0.64    inference(superposition,[],[f33,f87])).
% 2.14/0.64  fof(f88,plain,(
% 2.14/0.64    spl5_6 | ~spl5_2),
% 2.14/0.64    inference(avatar_split_clause,[],[f83,f57,f85])).
% 2.14/0.64  fof(f83,plain,(
% 2.14/0.64    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_2),
% 2.14/0.64    inference(resolution,[],[f42,f59])).
% 2.14/0.64  fof(f77,plain,(
% 2.14/0.64    spl5_5 | ~spl5_2),
% 2.14/0.64    inference(avatar_split_clause,[],[f71,f57,f74])).
% 2.14/0.64  fof(f71,plain,(
% 2.14/0.64    r1_xboole_0(sK1,sK2) | ~spl5_2),
% 2.14/0.64    inference(resolution,[],[f41,f59])).
% 2.14/0.64  fof(f70,plain,(
% 2.14/0.64    spl5_4),
% 2.14/0.64    inference(avatar_split_clause,[],[f28,f67])).
% 2.14/0.64  fof(f28,plain,(
% 2.14/0.64    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.14/0.64    inference(cnf_transformation,[],[f23])).
% 2.14/0.64  fof(f23,plain,(
% 2.14/0.64    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.14/0.64    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f22])).
% 2.14/0.64  fof(f22,plain,(
% 2.14/0.64    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 2.14/0.64    introduced(choice_axiom,[])).
% 2.14/0.64  fof(f17,plain,(
% 2.14/0.64    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.14/0.64    inference(flattening,[],[f16])).
% 2.14/0.64  fof(f16,plain,(
% 2.14/0.64    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.14/0.64    inference(ennf_transformation,[],[f14])).
% 2.14/0.64  fof(f14,negated_conjecture,(
% 2.14/0.64    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.14/0.64    inference(negated_conjecture,[],[f13])).
% 2.14/0.64  fof(f13,conjecture,(
% 2.14/0.64    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.14/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 2.14/0.64  fof(f65,plain,(
% 2.14/0.64    ~spl5_3),
% 2.14/0.64    inference(avatar_split_clause,[],[f31,f62])).
% 2.14/0.64  fof(f31,plain,(
% 2.14/0.64    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.14/0.64    inference(cnf_transformation,[],[f23])).
% 2.14/0.64  fof(f60,plain,(
% 2.14/0.64    spl5_2),
% 2.14/0.64    inference(avatar_split_clause,[],[f30,f57])).
% 2.14/0.64  fof(f30,plain,(
% 2.14/0.64    r1_xboole_0(sK2,sK1)),
% 2.14/0.64    inference(cnf_transformation,[],[f23])).
% 2.14/0.64  fof(f55,plain,(
% 2.14/0.64    spl5_1),
% 2.14/0.64    inference(avatar_split_clause,[],[f29,f52])).
% 2.14/0.64  fof(f29,plain,(
% 2.14/0.64    r2_hidden(sK3,sK2)),
% 2.14/0.64    inference(cnf_transformation,[],[f23])).
% 2.14/0.64  % SZS output end Proof for theBenchmark
% 2.14/0.64  % (21324)------------------------------
% 2.14/0.64  % (21324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.14/0.64  % (21324)Termination reason: Refutation
% 2.14/0.64  
% 2.14/0.64  % (21324)Memory used [KB]: 8187
% 2.14/0.64  % (21324)Time elapsed: 0.212 s
% 2.14/0.64  % (21324)------------------------------
% 2.14/0.64  % (21324)------------------------------
% 2.21/0.64  % (21323)Success in time 0.274 s
%------------------------------------------------------------------------------
