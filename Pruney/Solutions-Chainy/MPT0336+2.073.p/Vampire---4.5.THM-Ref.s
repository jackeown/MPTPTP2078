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
% DateTime   : Thu Dec  3 12:43:33 EST 2020

% Result     : Theorem 2.73s
% Output     : Refutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  209 ( 728 expanded)
%              Number of leaves         :   45 ( 261 expanded)
%              Depth                    :   14
%              Number of atoms          :  487 (1706 expanded)
%              Number of equality atoms :   63 ( 285 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6119,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f73,f85,f91,f96,f105,f110,f271,f289,f300,f320,f368,f374,f380,f913,f1987,f2660,f2717,f2724,f2812,f2866,f2873,f2880,f5690,f5698,f5731,f5736,f5745,f5758,f5763,f6118])).

fof(f6118,plain,
    ( spl5_3
    | ~ spl5_5
    | ~ spl5_29 ),
    inference(avatar_contradiction_clause,[],[f6117])).

fof(f6117,plain,
    ( $false
    | spl5_3
    | ~ spl5_5
    | ~ spl5_29 ),
    inference(subsumption_resolution,[],[f6116,f5730])).

fof(f5730,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f5728])).

fof(f5728,plain,
    ( spl5_29
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f6116,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f6109,f72])).

fof(f72,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl5_5
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f6109,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0)
    | spl5_3 ),
    inference(resolution,[],[f509,f61])).

fof(f61,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f59,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f509,plain,(
    ! [X10,X11,X9] :
      ( r1_xboole_0(k2_xboole_0(X10,X11),X9)
      | ~ r1_xboole_0(X9,X11)
      | ~ r1_xboole_0(X9,X10) ) ),
    inference(resolution,[],[f43,f40])).

fof(f40,plain,(
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

fof(f43,plain,(
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

fof(f5763,plain,
    ( spl5_33
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f5739,f5733,f5760])).

fof(f5760,plain,
    ( spl5_33
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f5733,plain,
    ( spl5_30
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f5739,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_30 ),
    inference(resolution,[],[f5735,f41])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k4_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

fof(f5735,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f5733])).

fof(f5758,plain,
    ( spl5_32
    | ~ spl5_29 ),
    inference(avatar_split_clause,[],[f5737,f5728,f5755])).

fof(f5755,plain,
    ( spl5_32
  <=> sK1 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f5737,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl5_29 ),
    inference(resolution,[],[f5730,f41])).

fof(f5745,plain,
    ( spl5_31
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f5707,f5695,f5742])).

fof(f5742,plain,
    ( spl5_31
  <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f5695,plain,
    ( spl5_28
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f5707,plain,
    ( r1_tarski(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_28 ),
    inference(superposition,[],[f258,f5697])).

fof(f5697,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f5695])).

fof(f258,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X1,X0),X0) ),
    inference(superposition,[],[f198,f33])).

fof(f33,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f198,plain,(
    ! [X10,X9] : r1_tarski(k3_xboole_0(X9,X10),X9) ),
    inference(superposition,[],[f32,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f32,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f5736,plain,
    ( spl5_30
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f5701,f5695,f5733])).

fof(f5701,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_28 ),
    inference(superposition,[],[f260,f5697])).

fof(f260,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),X2) ),
    inference(resolution,[],[f258,f47])).

fof(f47,plain,(
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

fof(f5731,plain,
    ( spl5_29
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f5699,f5695,f5728])).

fof(f5699,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_28 ),
    inference(superposition,[],[f1043,f5697])).

fof(f1043,plain,(
    ! [X4,X5,X3] : r1_xboole_0(X3,k3_xboole_0(X4,k4_xboole_0(X5,X3))) ),
    inference(resolution,[],[f260,f40])).

fof(f5698,plain,
    ( spl5_28
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f5461,f2877,f5695])).

fof(f2877,plain,
    ( spl5_26
  <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f5461,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_26 ),
    inference(superposition,[],[f5157,f194])).

fof(f194,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f35,f35])).

fof(f5157,plain,
    ( ! [X0] : k4_xboole_0(X0,k3_xboole_0(sK0,sK1)) = X0
    | ~ spl5_26 ),
    inference(resolution,[],[f5153,f41])).

fof(f5153,plain,
    ( ! [X1] : r1_xboole_0(X1,k3_xboole_0(sK0,sK1))
    | ~ spl5_26 ),
    inference(resolution,[],[f5133,f40])).

fof(f5133,plain,
    ( ! [X6] : r1_xboole_0(k3_xboole_0(sK0,sK1),X6)
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f5102,f258])).

fof(f5102,plain,
    ( ! [X6] :
        ( r1_xboole_0(k3_xboole_0(sK0,sK1),X6)
        | ~ r1_tarski(k3_xboole_0(sK0,sK1),sK1) )
    | ~ spl5_26 ),
    inference(resolution,[],[f5098,f2904])).

fof(f2904,plain,
    ( ! [X13] :
        ( r1_xboole_0(X13,k3_xboole_0(sK0,sK1))
        | ~ r1_tarski(X13,sK1) )
    | ~ spl5_26 ),
    inference(superposition,[],[f47,f2879])).

fof(f2879,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f2877])).

fof(f5098,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f5092])).

fof(f5092,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f361,f36])).

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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

fof(f361,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_hidden(sK4(X1,X2),X3)
      | ~ r1_xboole_0(X1,X3)
      | r1_xboole_0(X1,X2) ) ),
    inference(resolution,[],[f38,f36])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5690,plain,
    ( spl5_27
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f5469,f2877,f82,f5687])).

fof(f5687,plain,
    ( spl5_27
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f82,plain,
    ( spl5_6
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f5469,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(superposition,[],[f4716,f5157])).

fof(f4716,plain,
    ( ! [X10] : r1_tarski(k4_xboole_0(X10,X10),sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f261,f1287])).

fof(f1287,plain,
    ( ! [X1] : k3_xboole_0(X1,k4_xboole_0(sK2,X1)) = k4_xboole_0(X1,X1)
    | ~ spl5_6 ),
    inference(superposition,[],[f35,f1251])).

fof(f1251,plain,
    ( ! [X0] : k4_xboole_0(X0,k4_xboole_0(sK2,X0)) = X0
    | ~ spl5_6 ),
    inference(resolution,[],[f1231,f41])).

fof(f1231,plain,
    ( ! [X0] : r1_xboole_0(X0,k4_xboole_0(sK2,X0))
    | ~ spl5_6 ),
    inference(superposition,[],[f749,f128])).

fof(f128,plain,
    ( ! [X0] : k4_xboole_0(sK2,X0) = k4_xboole_0(k4_xboole_0(sK2,X0),sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f125,f41])).

fof(f125,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK2,X0),sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f123,f32])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | r1_xboole_0(X0,sK1) )
    | ~ spl5_6 ),
    inference(superposition,[],[f47,f84])).

fof(f84,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f749,plain,(
    ! [X4,X5,X3] : r1_xboole_0(X3,k4_xboole_0(k4_xboole_0(X4,X3),X5)) ),
    inference(resolution,[],[f121,f40])).

fof(f121,plain,(
    ! [X2,X0,X1] : r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1) ),
    inference(resolution,[],[f47,f32])).

fof(f261,plain,(
    ! [X4,X5,X3] : r1_tarski(k3_xboole_0(X3,k4_xboole_0(X4,X5)),X4) ),
    inference(resolution,[],[f258,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2880,plain,
    ( spl5_26
    | ~ spl5_25 ),
    inference(avatar_split_clause,[],[f2874,f2870,f2877])).

fof(f2870,plain,
    ( spl5_25
  <=> r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f2874,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_25 ),
    inference(resolution,[],[f2872,f41])).

fof(f2872,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f2870])).

fof(f2873,plain,
    ( spl5_25
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f2868,f2863,f2870])).

fof(f2863,plain,
    ( spl5_24
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f2868,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_24 ),
    inference(resolution,[],[f2865,f40])).

fof(f2865,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f2863])).

fof(f2866,plain,
    ( spl5_24
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f2849,f2657,f82,f64,f2863])).

fof(f64,plain,
    ( spl5_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f2657,plain,
    ( spl5_20
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f2849,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(resolution,[],[f2699,f66])).

fof(f66,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f64])).

fof(f2699,plain,
    ( ! [X23] :
        ( ~ r1_tarski(X23,k1_tarski(sK3))
        | r1_xboole_0(X23,sK1) )
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(superposition,[],[f1555,f2659])).

fof(f2659,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f2657])).

fof(f1555,plain,
    ( ! [X10,X11,X9] :
        ( r1_xboole_0(X11,k4_xboole_0(X10,X9))
        | ~ r1_tarski(X11,X9) )
    | ~ spl5_6 ),
    inference(superposition,[],[f47,f1368])).

fof(f1368,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0
    | ~ spl5_6 ),
    inference(resolution,[],[f1312,f41])).

fof(f1312,plain,
    ( ! [X37,X36] : r1_xboole_0(X37,k4_xboole_0(X36,X37))
    | ~ spl5_6 ),
    inference(superposition,[],[f749,f1251])).

fof(f2812,plain,
    ( spl5_23
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f2696,f2657,f82,f2809])).

fof(f2809,plain,
    ( spl5_23
  <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f2696,plain,
    ( k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(superposition,[],[f1368,f2659])).

fof(f2724,plain,
    ( spl5_22
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f2695,f2657,f82,f2721])).

fof(f2721,plain,
    ( spl5_22
  <=> r1_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f2695,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(superposition,[],[f1313,f2659])).

fof(f1313,plain,
    ( ! [X39,X38] : r1_xboole_0(k4_xboole_0(X38,X39),X39)
    | ~ spl5_6 ),
    inference(superposition,[],[f121,f1251])).

fof(f2717,plain,
    ( spl5_21
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f2694,f2657,f82,f2714])).

fof(f2714,plain,
    ( spl5_21
  <=> r1_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f2694,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_6
    | ~ spl5_20 ),
    inference(superposition,[],[f1312,f2659])).

fof(f2660,plain,
    ( spl5_20
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f2623,f54,f49,f2657])).

fof(f49,plain,
    ( spl5_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f54,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f2623,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f2258,f56])).

fof(f56,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f2258,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(sK2,X0)
        | k4_xboole_0(X0,k1_tarski(sK3)) = X0 )
    | ~ spl5_1 ),
    inference(resolution,[],[f2255,f41])).

fof(f2255,plain,
    ( ! [X1] :
        ( r1_xboole_0(X1,k1_tarski(sK3))
        | ~ r1_xboole_0(sK2,X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f2253,f40])).

fof(f2253,plain,
    ( ! [X0] :
        ( r1_xboole_0(k1_tarski(sK3),X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl5_1 ),
    inference(condensation,[],[f2250])).

fof(f2250,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(k1_tarski(sK3),X0)
        | ~ r1_xboole_0(sK2,X0)
        | ~ r1_xboole_0(sK2,X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f1762,f43])).

fof(f1762,plain,
    ( ! [X4,X5] :
        ( ~ r1_xboole_0(sK2,k2_xboole_0(X4,X5))
        | r1_xboole_0(k1_tarski(sK3),X4) )
    | ~ spl5_1 ),
    inference(resolution,[],[f112,f360])).

fof(f360,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f38,f51])).

fof(f51,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X3,k2_xboole_0(X4,X5))
      | r1_xboole_0(k1_tarski(X3),X4) ) ),
    inference(resolution,[],[f44,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
     => r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1987,plain,
    ( spl5_19
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f1275,f268,f82,f1984])).

fof(f1984,plain,
    ( spl5_19
  <=> r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f268,plain,
    ( spl5_11
  <=> k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f1275,plain,
    ( r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ spl5_6
    | ~ spl5_11 ),
    inference(superposition,[],[f1236,f270])).

fof(f270,plain,
    ( k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f268])).

fof(f1236,plain,
    ( ! [X5] : r1_tarski(k4_xboole_0(sK2,X5),k4_xboole_0(sK2,X5))
    | ~ spl5_6 ),
    inference(superposition,[],[f32,f128])).

fof(f913,plain,
    ( ~ spl5_18
    | spl5_3 ),
    inference(avatar_split_clause,[],[f903,f59,f910])).

fof(f910,plain,
    ( spl5_18
  <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f903,plain,
    ( sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl5_3 ),
    inference(resolution,[],[f100,f61])).

fof(f100,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | k4_xboole_0(X2,X3) != X2 ) ),
    inference(resolution,[],[f42,f40])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f380,plain,
    ( ~ spl5_17
    | ~ spl5_11
    | spl5_16 ),
    inference(avatar_split_clause,[],[f375,f371,f268,f377])).

fof(f377,plain,
    ( spl5_17
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f371,plain,
    ( spl5_16
  <=> sK2 = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f375,plain,
    ( sK2 != k3_xboole_0(sK1,sK2)
    | ~ spl5_11
    | spl5_16 ),
    inference(superposition,[],[f373,f270])).

fof(f373,plain,
    ( sK2 != k4_xboole_0(sK2,sK2)
    | spl5_16 ),
    inference(avatar_component_clause,[],[f371])).

fof(f374,plain,
    ( ~ spl5_16
    | spl5_15 ),
    inference(avatar_split_clause,[],[f369,f365,f371])).

fof(f365,plain,
    ( spl5_15
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f369,plain,
    ( sK2 != k4_xboole_0(sK2,sK2)
    | spl5_15 ),
    inference(resolution,[],[f367,f42])).

fof(f367,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl5_15 ),
    inference(avatar_component_clause,[],[f365])).

fof(f368,plain,
    ( ~ spl5_15
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f363,f49,f365])).

fof(f363,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f360,f51])).

fof(f320,plain,
    ( spl5_14
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f315,f297,f82,f317])).

fof(f317,plain,
    ( spl5_14
  <=> sK1 = k3_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f297,plain,
    ( spl5_13
  <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f315,plain,
    ( sK1 = k3_xboole_0(sK1,sK1)
    | ~ spl5_6
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f310,f245])).

fof(f245,plain,
    ( ! [X0] : sK1 = k4_xboole_0(sK1,k3_xboole_0(X0,sK2))
    | ~ spl5_6 ),
    inference(resolution,[],[f231,f41])).

fof(f231,plain,
    ( ! [X0] : r1_xboole_0(sK1,k3_xboole_0(X0,sK2))
    | ~ spl5_6 ),
    inference(superposition,[],[f213,f33])).

fof(f213,plain,
    ( ! [X36] : r1_xboole_0(sK1,k3_xboole_0(sK2,X36))
    | ~ spl5_6 ),
    inference(superposition,[],[f129,f35])).

fof(f129,plain,
    ( ! [X1] : r1_xboole_0(sK1,k4_xboole_0(sK2,X1))
    | ~ spl5_6 ),
    inference(resolution,[],[f125,f40])).

fof(f310,plain,
    ( k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK1)
    | ~ spl5_13 ),
    inference(superposition,[],[f35,f299])).

fof(f299,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f297])).

fof(f300,plain,
    ( spl5_13
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f192,f93,f297])).

fof(f93,plain,
    ( spl5_8
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f192,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl5_8 ),
    inference(superposition,[],[f35,f95])).

fof(f95,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f289,plain,
    ( spl5_12
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f284,f268,f93,f286])).

fof(f286,plain,
    ( spl5_12
  <=> sK2 = k3_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f284,plain,
    ( sK2 = k3_xboole_0(sK2,sK2)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(forward_demodulation,[],[f279,f207])).

fof(f207,plain,
    ( ! [X26] : sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,X26))
    | ~ spl5_8 ),
    inference(superposition,[],[f140,f35])).

fof(f140,plain,
    ( ! [X0] : sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,X0))
    | ~ spl5_8 ),
    inference(resolution,[],[f138,f41])).

fof(f138,plain,
    ( ! [X1] : r1_xboole_0(sK2,k4_xboole_0(sK1,X1))
    | ~ spl5_8 ),
    inference(resolution,[],[f134,f40])).

fof(f134,plain,
    ( ! [X0] : r1_xboole_0(k4_xboole_0(sK1,X0),sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f124,f32])).

fof(f124,plain,
    ( ! [X1] :
        ( ~ r1_tarski(X1,sK1)
        | r1_xboole_0(X1,sK2) )
    | ~ spl5_8 ),
    inference(superposition,[],[f47,f95])).

fof(f279,plain,
    ( k3_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_11 ),
    inference(superposition,[],[f35,f270])).

fof(f271,plain,
    ( spl5_11
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f218,f82,f268])).

fof(f218,plain,
    ( k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f190,f33])).

fof(f190,plain,
    ( k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f35,f84])).

fof(f110,plain,
    ( ~ spl5_10
    | spl5_3 ),
    inference(avatar_split_clause,[],[f98,f59,f107])).

fof(f107,plain,
    ( spl5_10
  <=> k2_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f98,plain,
    ( k2_xboole_0(sK0,sK2) != k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(resolution,[],[f42,f61])).

fof(f105,plain,
    ( spl5_9
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f97,f93,f102])).

fof(f102,plain,
    ( spl5_9
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f97,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl5_8 ),
    inference(superposition,[],[f32,f95])).

fof(f96,plain,
    ( spl5_8
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f79,f70,f93])).

fof(f79,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f41,f72])).

fof(f91,plain,
    ( spl5_7
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f86,f82,f88])).

fof(f88,plain,
    ( spl5_7
  <=> r1_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f86,plain,
    ( r1_tarski(sK2,sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f32,f84])).

fof(f85,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f80,f54,f82])).

fof(f80,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f41,f56])).

fof(f73,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f68,f54,f70])).

fof(f68,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f40,f56])).

fof(f67,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f27,f64])).

fof(f27,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f22])).

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

fof(f16,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1,X2,X3] :
      ( ~ r1_xboole_0(k2_xboole_0(X0,X2),X1)
      & r1_xboole_0(X2,X1)
      & r2_hidden(X3,X2)
      & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( r1_xboole_0(X2,X1)
          & r2_hidden(X3,X2)
          & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
       => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( r1_xboole_0(X2,X1)
        & r2_hidden(X3,X2)
        & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)) )
     => r1_xboole_0(k2_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

fof(f62,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f30,f59])).

fof(f30,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f57,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f29,f54])).

fof(f29,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f52,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f28,f49])).

fof(f28,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:33:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (4234)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.21/0.46  % (4243)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.21/0.46  % (4244)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.21/0.47  % (4235)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.21/0.47  % (4233)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.21/0.47  % (4236)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.47  % (4237)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.21/0.48  % (4248)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.21/0.48  % (4232)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.21/0.48  % (4242)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.48  % (4247)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.21/0.48  % (4245)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.21/0.49  % (4240)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.21/0.49  % (4241)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.21/0.49  % (4239)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.21/0.49  % (4238)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.49  % (4231)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.21/0.50  % (4246)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 2.73/0.74  % (4231)Refutation found. Thanks to Tanya!
% 2.73/0.74  % SZS status Theorem for theBenchmark
% 2.73/0.74  % SZS output start Proof for theBenchmark
% 2.73/0.74  fof(f6119,plain,(
% 2.73/0.74    $false),
% 2.73/0.74    inference(avatar_sat_refutation,[],[f52,f57,f62,f67,f73,f85,f91,f96,f105,f110,f271,f289,f300,f320,f368,f374,f380,f913,f1987,f2660,f2717,f2724,f2812,f2866,f2873,f2880,f5690,f5698,f5731,f5736,f5745,f5758,f5763,f6118])).
% 2.73/0.74  fof(f6118,plain,(
% 2.73/0.74    spl5_3 | ~spl5_5 | ~spl5_29),
% 2.73/0.74    inference(avatar_contradiction_clause,[],[f6117])).
% 2.73/0.74  fof(f6117,plain,(
% 2.73/0.74    $false | (spl5_3 | ~spl5_5 | ~spl5_29)),
% 2.73/0.74    inference(subsumption_resolution,[],[f6116,f5730])).
% 2.73/0.74  fof(f5730,plain,(
% 2.73/0.74    r1_xboole_0(sK1,sK0) | ~spl5_29),
% 2.73/0.74    inference(avatar_component_clause,[],[f5728])).
% 2.73/0.74  fof(f5728,plain,(
% 2.73/0.74    spl5_29 <=> r1_xboole_0(sK1,sK0)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 2.73/0.74  fof(f6116,plain,(
% 2.73/0.74    ~r1_xboole_0(sK1,sK0) | (spl5_3 | ~spl5_5)),
% 2.73/0.74    inference(subsumption_resolution,[],[f6109,f72])).
% 2.73/0.74  fof(f72,plain,(
% 2.73/0.74    r1_xboole_0(sK1,sK2) | ~spl5_5),
% 2.73/0.74    inference(avatar_component_clause,[],[f70])).
% 2.73/0.74  fof(f70,plain,(
% 2.73/0.74    spl5_5 <=> r1_xboole_0(sK1,sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 2.73/0.74  fof(f6109,plain,(
% 2.73/0.74    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0) | spl5_3),
% 2.73/0.74    inference(resolution,[],[f509,f61])).
% 2.73/0.74  fof(f61,plain,(
% 2.73/0.74    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 2.73/0.74    inference(avatar_component_clause,[],[f59])).
% 2.73/0.74  fof(f59,plain,(
% 2.73/0.74    spl5_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.73/0.74  fof(f509,plain,(
% 2.73/0.74    ( ! [X10,X11,X9] : (r1_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10)) )),
% 2.73/0.74    inference(resolution,[],[f43,f40])).
% 2.73/0.74  fof(f40,plain,(
% 2.73/0.74    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f19])).
% 2.73/0.74  fof(f19,plain,(
% 2.73/0.74    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 2.73/0.74    inference(ennf_transformation,[],[f2])).
% 2.73/0.74  fof(f2,axiom,(
% 2.73/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 2.73/0.74  fof(f43,plain,(
% 2.73/0.74    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f20])).
% 2.73/0.74  fof(f20,plain,(
% 2.73/0.74    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.73/0.74    inference(ennf_transformation,[],[f7])).
% 2.73/0.74  fof(f7,axiom,(
% 2.73/0.74    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 2.73/0.74  fof(f5763,plain,(
% 2.73/0.74    spl5_33 | ~spl5_30),
% 2.73/0.74    inference(avatar_split_clause,[],[f5739,f5733,f5760])).
% 2.73/0.74  fof(f5760,plain,(
% 2.73/0.74    spl5_33 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 2.73/0.74  fof(f5733,plain,(
% 2.73/0.74    spl5_30 <=> r1_xboole_0(sK0,sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 2.73/0.74  fof(f5739,plain,(
% 2.73/0.74    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_30),
% 2.73/0.74    inference(resolution,[],[f5735,f41])).
% 2.73/0.74  fof(f41,plain,(
% 2.73/0.74    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 2.73/0.74    inference(cnf_transformation,[],[f26])).
% 2.73/0.74  fof(f26,plain,(
% 2.73/0.74    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 2.73/0.74    inference(nnf_transformation,[],[f8])).
% 2.73/0.74  fof(f8,axiom,(
% 2.73/0.74    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 2.73/0.74  fof(f5735,plain,(
% 2.73/0.74    r1_xboole_0(sK0,sK1) | ~spl5_30),
% 2.73/0.74    inference(avatar_component_clause,[],[f5733])).
% 2.73/0.74  fof(f5758,plain,(
% 2.73/0.74    spl5_32 | ~spl5_29),
% 2.73/0.74    inference(avatar_split_clause,[],[f5737,f5728,f5755])).
% 2.73/0.74  fof(f5755,plain,(
% 2.73/0.74    spl5_32 <=> sK1 = k4_xboole_0(sK1,sK0)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 2.73/0.74  fof(f5737,plain,(
% 2.73/0.74    sK1 = k4_xboole_0(sK1,sK0) | ~spl5_29),
% 2.73/0.74    inference(resolution,[],[f5730,f41])).
% 2.73/0.74  fof(f5745,plain,(
% 2.73/0.74    spl5_31 | ~spl5_28),
% 2.73/0.74    inference(avatar_split_clause,[],[f5707,f5695,f5742])).
% 2.73/0.74  fof(f5742,plain,(
% 2.73/0.74    spl5_31 <=> r1_tarski(sK0,k4_xboole_0(sK0,sK1))),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.73/0.74  fof(f5695,plain,(
% 2.73/0.74    spl5_28 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 2.73/0.74  fof(f5707,plain,(
% 2.73/0.74    r1_tarski(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_28),
% 2.73/0.74    inference(superposition,[],[f258,f5697])).
% 2.73/0.74  fof(f5697,plain,(
% 2.73/0.74    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_28),
% 2.73/0.74    inference(avatar_component_clause,[],[f5695])).
% 2.73/0.74  fof(f258,plain,(
% 2.73/0.74    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X1,X0),X0)) )),
% 2.73/0.74    inference(superposition,[],[f198,f33])).
% 2.73/0.74  fof(f33,plain,(
% 2.73/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f1])).
% 2.73/0.74  fof(f1,axiom,(
% 2.73/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 2.73/0.74  fof(f198,plain,(
% 2.73/0.74    ( ! [X10,X9] : (r1_tarski(k3_xboole_0(X9,X10),X9)) )),
% 2.73/0.74    inference(superposition,[],[f32,f35])).
% 2.73/0.74  fof(f35,plain,(
% 2.73/0.74    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 2.73/0.74    inference(cnf_transformation,[],[f6])).
% 2.73/0.74  fof(f6,axiom,(
% 2.73/0.74    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.73/0.74  fof(f32,plain,(
% 2.73/0.74    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f5])).
% 2.73/0.74  fof(f5,axiom,(
% 2.73/0.74    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 2.73/0.74  fof(f5736,plain,(
% 2.73/0.74    spl5_30 | ~spl5_28),
% 2.73/0.74    inference(avatar_split_clause,[],[f5701,f5695,f5733])).
% 2.73/0.74  fof(f5701,plain,(
% 2.73/0.74    r1_xboole_0(sK0,sK1) | ~spl5_28),
% 2.73/0.74    inference(superposition,[],[f260,f5697])).
% 2.73/0.74  fof(f260,plain,(
% 2.73/0.74    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X0,k4_xboole_0(X1,X2)),X2)) )),
% 2.73/0.74    inference(resolution,[],[f258,f47])).
% 2.73/0.74  fof(f47,plain,(
% 2.73/0.74    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f21])).
% 2.73/0.74  fof(f21,plain,(
% 2.73/0.74    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 2.73/0.74    inference(ennf_transformation,[],[f4])).
% 2.73/0.74  fof(f4,axiom,(
% 2.73/0.74    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 2.73/0.74  fof(f5731,plain,(
% 2.73/0.74    spl5_29 | ~spl5_28),
% 2.73/0.74    inference(avatar_split_clause,[],[f5699,f5695,f5728])).
% 2.73/0.74  fof(f5699,plain,(
% 2.73/0.74    r1_xboole_0(sK1,sK0) | ~spl5_28),
% 2.73/0.74    inference(superposition,[],[f1043,f5697])).
% 2.73/0.74  fof(f1043,plain,(
% 2.73/0.74    ( ! [X4,X5,X3] : (r1_xboole_0(X3,k3_xboole_0(X4,k4_xboole_0(X5,X3)))) )),
% 2.73/0.74    inference(resolution,[],[f260,f40])).
% 2.73/0.74  fof(f5698,plain,(
% 2.73/0.74    spl5_28 | ~spl5_26),
% 2.73/0.74    inference(avatar_split_clause,[],[f5461,f2877,f5695])).
% 2.73/0.74  fof(f2877,plain,(
% 2.73/0.74    spl5_26 <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 2.73/0.74  fof(f5461,plain,(
% 2.73/0.74    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_26),
% 2.73/0.74    inference(superposition,[],[f5157,f194])).
% 2.73/0.74  fof(f194,plain,(
% 2.73/0.74    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 2.73/0.74    inference(superposition,[],[f35,f35])).
% 2.73/0.74  fof(f5157,plain,(
% 2.73/0.74    ( ! [X0] : (k4_xboole_0(X0,k3_xboole_0(sK0,sK1)) = X0) ) | ~spl5_26),
% 2.73/0.74    inference(resolution,[],[f5153,f41])).
% 2.73/0.74  fof(f5153,plain,(
% 2.73/0.74    ( ! [X1] : (r1_xboole_0(X1,k3_xboole_0(sK0,sK1))) ) | ~spl5_26),
% 2.73/0.74    inference(resolution,[],[f5133,f40])).
% 2.73/0.74  fof(f5133,plain,(
% 2.73/0.74    ( ! [X6] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X6)) ) | ~spl5_26),
% 2.73/0.74    inference(subsumption_resolution,[],[f5102,f258])).
% 2.73/0.74  fof(f5102,plain,(
% 2.73/0.74    ( ! [X6] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X6) | ~r1_tarski(k3_xboole_0(sK0,sK1),sK1)) ) | ~spl5_26),
% 2.73/0.74    inference(resolution,[],[f5098,f2904])).
% 2.73/0.74  fof(f2904,plain,(
% 2.73/0.74    ( ! [X13] : (r1_xboole_0(X13,k3_xboole_0(sK0,sK1)) | ~r1_tarski(X13,sK1)) ) | ~spl5_26),
% 2.73/0.74    inference(superposition,[],[f47,f2879])).
% 2.73/0.74  fof(f2879,plain,(
% 2.73/0.74    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_26),
% 2.73/0.74    inference(avatar_component_clause,[],[f2877])).
% 2.73/0.74  fof(f5098,plain,(
% 2.73/0.74    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 2.73/0.74    inference(duplicate_literal_removal,[],[f5092])).
% 2.73/0.74  fof(f5092,plain,(
% 2.73/0.74    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 2.73/0.74    inference(resolution,[],[f361,f36])).
% 2.73/0.74  fof(f36,plain,(
% 2.73/0.74    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f25])).
% 2.73/0.74  fof(f25,plain,(
% 2.73/0.74    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.73/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f17,f24])).
% 2.73/0.74  fof(f24,plain,(
% 2.73/0.74    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.73/0.74    introduced(choice_axiom,[])).
% 2.73/0.74  fof(f17,plain,(
% 2.73/0.74    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.73/0.74    inference(ennf_transformation,[],[f14])).
% 2.73/0.74  fof(f14,plain,(
% 2.73/0.74    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.73/0.74    inference(rectify,[],[f3])).
% 2.73/0.74  fof(f3,axiom,(
% 2.73/0.74    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 2.73/0.74  fof(f361,plain,(
% 2.73/0.74    ( ! [X2,X3,X1] : (~r2_hidden(sK4(X1,X2),X3) | ~r1_xboole_0(X1,X3) | r1_xboole_0(X1,X2)) )),
% 2.73/0.74    inference(resolution,[],[f38,f36])).
% 2.73/0.74  fof(f38,plain,(
% 2.73/0.74    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f25])).
% 2.73/0.74  fof(f5690,plain,(
% 2.73/0.74    spl5_27 | ~spl5_6 | ~spl5_26),
% 2.73/0.74    inference(avatar_split_clause,[],[f5469,f2877,f82,f5687])).
% 2.73/0.74  fof(f5687,plain,(
% 2.73/0.74    spl5_27 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 2.73/0.74  fof(f82,plain,(
% 2.73/0.74    spl5_6 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 2.73/0.74  fof(f5469,plain,(
% 2.73/0.74    r1_tarski(k3_xboole_0(sK0,sK1),sK2) | (~spl5_6 | ~spl5_26)),
% 2.73/0.74    inference(superposition,[],[f4716,f5157])).
% 2.73/0.74  fof(f4716,plain,(
% 2.73/0.74    ( ! [X10] : (r1_tarski(k4_xboole_0(X10,X10),sK2)) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f261,f1287])).
% 2.73/0.74  fof(f1287,plain,(
% 2.73/0.74    ( ! [X1] : (k3_xboole_0(X1,k4_xboole_0(sK2,X1)) = k4_xboole_0(X1,X1)) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f35,f1251])).
% 2.73/0.74  fof(f1251,plain,(
% 2.73/0.74    ( ! [X0] : (k4_xboole_0(X0,k4_xboole_0(sK2,X0)) = X0) ) | ~spl5_6),
% 2.73/0.74    inference(resolution,[],[f1231,f41])).
% 2.73/0.74  fof(f1231,plain,(
% 2.73/0.74    ( ! [X0] : (r1_xboole_0(X0,k4_xboole_0(sK2,X0))) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f749,f128])).
% 2.73/0.74  fof(f128,plain,(
% 2.73/0.74    ( ! [X0] : (k4_xboole_0(sK2,X0) = k4_xboole_0(k4_xboole_0(sK2,X0),sK1)) ) | ~spl5_6),
% 2.73/0.74    inference(resolution,[],[f125,f41])).
% 2.73/0.74  fof(f125,plain,(
% 2.73/0.74    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK2,X0),sK1)) ) | ~spl5_6),
% 2.73/0.74    inference(resolution,[],[f123,f32])).
% 2.73/0.74  fof(f123,plain,(
% 2.73/0.74    ( ! [X0] : (~r1_tarski(X0,sK2) | r1_xboole_0(X0,sK1)) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f47,f84])).
% 2.73/0.74  fof(f84,plain,(
% 2.73/0.74    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_6),
% 2.73/0.74    inference(avatar_component_clause,[],[f82])).
% 2.73/0.74  fof(f749,plain,(
% 2.73/0.74    ( ! [X4,X5,X3] : (r1_xboole_0(X3,k4_xboole_0(k4_xboole_0(X4,X3),X5))) )),
% 2.73/0.74    inference(resolution,[],[f121,f40])).
% 2.73/0.74  fof(f121,plain,(
% 2.73/0.74    ( ! [X2,X0,X1] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(X0,X1),X2),X1)) )),
% 2.73/0.74    inference(resolution,[],[f47,f32])).
% 2.73/0.74  fof(f261,plain,(
% 2.73/0.74    ( ! [X4,X5,X3] : (r1_tarski(k3_xboole_0(X3,k4_xboole_0(X4,X5)),X4)) )),
% 2.73/0.74    inference(resolution,[],[f258,f46])).
% 2.73/0.74  fof(f46,plain,(
% 2.73/0.74    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f21])).
% 2.73/0.74  fof(f2880,plain,(
% 2.73/0.74    spl5_26 | ~spl5_25),
% 2.73/0.74    inference(avatar_split_clause,[],[f2874,f2870,f2877])).
% 2.73/0.74  fof(f2870,plain,(
% 2.73/0.74    spl5_25 <=> r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.73/0.74  fof(f2874,plain,(
% 2.73/0.74    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_25),
% 2.73/0.74    inference(resolution,[],[f2872,f41])).
% 2.73/0.74  fof(f2872,plain,(
% 2.73/0.74    r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_25),
% 2.73/0.74    inference(avatar_component_clause,[],[f2870])).
% 2.73/0.74  fof(f2873,plain,(
% 2.73/0.74    spl5_25 | ~spl5_24),
% 2.73/0.74    inference(avatar_split_clause,[],[f2868,f2863,f2870])).
% 2.73/0.74  fof(f2863,plain,(
% 2.73/0.74    spl5_24 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 2.73/0.74  fof(f2868,plain,(
% 2.73/0.74    r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_24),
% 2.73/0.74    inference(resolution,[],[f2865,f40])).
% 2.73/0.74  fof(f2865,plain,(
% 2.73/0.74    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | ~spl5_24),
% 2.73/0.74    inference(avatar_component_clause,[],[f2863])).
% 2.73/0.74  fof(f2866,plain,(
% 2.73/0.74    spl5_24 | ~spl5_4 | ~spl5_6 | ~spl5_20),
% 2.73/0.74    inference(avatar_split_clause,[],[f2849,f2657,f82,f64,f2863])).
% 2.73/0.74  fof(f64,plain,(
% 2.73/0.74    spl5_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.73/0.74  fof(f2657,plain,(
% 2.73/0.74    spl5_20 <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK3))),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 2.73/0.74  fof(f2849,plain,(
% 2.73/0.74    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | (~spl5_4 | ~spl5_6 | ~spl5_20)),
% 2.73/0.74    inference(resolution,[],[f2699,f66])).
% 2.73/0.74  fof(f66,plain,(
% 2.73/0.74    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl5_4),
% 2.73/0.74    inference(avatar_component_clause,[],[f64])).
% 2.73/0.74  fof(f2699,plain,(
% 2.73/0.74    ( ! [X23] : (~r1_tarski(X23,k1_tarski(sK3)) | r1_xboole_0(X23,sK1)) ) | (~spl5_6 | ~spl5_20)),
% 2.73/0.74    inference(superposition,[],[f1555,f2659])).
% 2.73/0.74  fof(f2659,plain,(
% 2.73/0.74    sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_20),
% 2.73/0.74    inference(avatar_component_clause,[],[f2657])).
% 2.73/0.74  fof(f1555,plain,(
% 2.73/0.74    ( ! [X10,X11,X9] : (r1_xboole_0(X11,k4_xboole_0(X10,X9)) | ~r1_tarski(X11,X9)) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f47,f1368])).
% 2.73/0.74  fof(f1368,plain,(
% 2.73/0.74    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) ) | ~spl5_6),
% 2.73/0.74    inference(resolution,[],[f1312,f41])).
% 2.73/0.74  fof(f1312,plain,(
% 2.73/0.74    ( ! [X37,X36] : (r1_xboole_0(X37,k4_xboole_0(X36,X37))) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f749,f1251])).
% 2.73/0.74  fof(f2812,plain,(
% 2.73/0.74    spl5_23 | ~spl5_6 | ~spl5_20),
% 2.73/0.74    inference(avatar_split_clause,[],[f2696,f2657,f82,f2809])).
% 2.73/0.74  fof(f2809,plain,(
% 2.73/0.74    spl5_23 <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 2.73/0.74  fof(f2696,plain,(
% 2.73/0.74    k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) | (~spl5_6 | ~spl5_20)),
% 2.73/0.74    inference(superposition,[],[f1368,f2659])).
% 2.73/0.74  fof(f2724,plain,(
% 2.73/0.74    spl5_22 | ~spl5_6 | ~spl5_20),
% 2.73/0.74    inference(avatar_split_clause,[],[f2695,f2657,f82,f2721])).
% 2.73/0.74  fof(f2721,plain,(
% 2.73/0.74    spl5_22 <=> r1_xboole_0(sK1,k1_tarski(sK3))),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 2.73/0.74  fof(f2695,plain,(
% 2.73/0.74    r1_xboole_0(sK1,k1_tarski(sK3)) | (~spl5_6 | ~spl5_20)),
% 2.73/0.74    inference(superposition,[],[f1313,f2659])).
% 2.73/0.74  fof(f1313,plain,(
% 2.73/0.74    ( ! [X39,X38] : (r1_xboole_0(k4_xboole_0(X38,X39),X39)) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f121,f1251])).
% 2.73/0.74  fof(f2717,plain,(
% 2.73/0.74    spl5_21 | ~spl5_6 | ~spl5_20),
% 2.73/0.74    inference(avatar_split_clause,[],[f2694,f2657,f82,f2714])).
% 2.73/0.74  fof(f2714,plain,(
% 2.73/0.74    spl5_21 <=> r1_xboole_0(k1_tarski(sK3),sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.73/0.74  fof(f2694,plain,(
% 2.73/0.74    r1_xboole_0(k1_tarski(sK3),sK1) | (~spl5_6 | ~spl5_20)),
% 2.73/0.74    inference(superposition,[],[f1312,f2659])).
% 2.73/0.74  fof(f2660,plain,(
% 2.73/0.74    spl5_20 | ~spl5_1 | ~spl5_2),
% 2.73/0.74    inference(avatar_split_clause,[],[f2623,f54,f49,f2657])).
% 2.73/0.74  fof(f49,plain,(
% 2.73/0.74    spl5_1 <=> r2_hidden(sK3,sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.73/0.74  fof(f54,plain,(
% 2.73/0.74    spl5_2 <=> r1_xboole_0(sK2,sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 2.73/0.74  fof(f2623,plain,(
% 2.73/0.74    sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) | (~spl5_1 | ~spl5_2)),
% 2.73/0.74    inference(resolution,[],[f2258,f56])).
% 2.73/0.74  fof(f56,plain,(
% 2.73/0.74    r1_xboole_0(sK2,sK1) | ~spl5_2),
% 2.73/0.74    inference(avatar_component_clause,[],[f54])).
% 2.73/0.74  fof(f2258,plain,(
% 2.73/0.74    ( ! [X0] : (~r1_xboole_0(sK2,X0) | k4_xboole_0(X0,k1_tarski(sK3)) = X0) ) | ~spl5_1),
% 2.73/0.74    inference(resolution,[],[f2255,f41])).
% 2.73/0.74  fof(f2255,plain,(
% 2.73/0.74    ( ! [X1] : (r1_xboole_0(X1,k1_tarski(sK3)) | ~r1_xboole_0(sK2,X1)) ) | ~spl5_1),
% 2.73/0.74    inference(resolution,[],[f2253,f40])).
% 2.73/0.74  fof(f2253,plain,(
% 2.73/0.74    ( ! [X0] : (r1_xboole_0(k1_tarski(sK3),X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl5_1),
% 2.73/0.74    inference(condensation,[],[f2250])).
% 2.73/0.74  fof(f2250,plain,(
% 2.73/0.74    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(sK3),X0) | ~r1_xboole_0(sK2,X0) | ~r1_xboole_0(sK2,X1)) ) | ~spl5_1),
% 2.73/0.74    inference(resolution,[],[f1762,f43])).
% 2.73/0.74  fof(f1762,plain,(
% 2.73/0.74    ( ! [X4,X5] : (~r1_xboole_0(sK2,k2_xboole_0(X4,X5)) | r1_xboole_0(k1_tarski(sK3),X4)) ) | ~spl5_1),
% 2.73/0.74    inference(resolution,[],[f112,f360])).
% 2.73/0.74  fof(f360,plain,(
% 2.73/0.74    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl5_1),
% 2.73/0.74    inference(resolution,[],[f38,f51])).
% 2.73/0.74  fof(f51,plain,(
% 2.73/0.74    r2_hidden(sK3,sK2) | ~spl5_1),
% 2.73/0.74    inference(avatar_component_clause,[],[f49])).
% 2.73/0.74  fof(f112,plain,(
% 2.73/0.74    ( ! [X4,X5,X3] : (r2_hidden(X3,k2_xboole_0(X4,X5)) | r1_xboole_0(k1_tarski(X3),X4)) )),
% 2.73/0.74    inference(resolution,[],[f44,f39])).
% 2.73/0.74  fof(f39,plain,(
% 2.73/0.74    ( ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f18])).
% 2.73/0.74  fof(f18,plain,(
% 2.73/0.74    ! [X0,X1] : (r1_xboole_0(k1_tarski(X0),X1) | r2_hidden(X0,X1))),
% 2.73/0.74    inference(ennf_transformation,[],[f11])).
% 2.73/0.74  fof(f11,axiom,(
% 2.73/0.74    ! [X0,X1] : (~r2_hidden(X0,X1) => r1_xboole_0(k1_tarski(X0),X1))),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).
% 2.73/0.74  fof(f44,plain,(
% 2.73/0.74    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 2.73/0.74    inference(cnf_transformation,[],[f20])).
% 2.73/0.74  fof(f1987,plain,(
% 2.73/0.74    spl5_19 | ~spl5_6 | ~spl5_11),
% 2.73/0.74    inference(avatar_split_clause,[],[f1275,f268,f82,f1984])).
% 2.73/0.74  fof(f1984,plain,(
% 2.73/0.74    spl5_19 <=> r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 2.73/0.74  fof(f268,plain,(
% 2.73/0.74    spl5_11 <=> k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 2.73/0.74  fof(f1275,plain,(
% 2.73/0.74    r1_tarski(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | (~spl5_6 | ~spl5_11)),
% 2.73/0.74    inference(superposition,[],[f1236,f270])).
% 2.73/0.74  fof(f270,plain,(
% 2.73/0.74    k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) | ~spl5_11),
% 2.73/0.74    inference(avatar_component_clause,[],[f268])).
% 2.73/0.74  fof(f1236,plain,(
% 2.73/0.74    ( ! [X5] : (r1_tarski(k4_xboole_0(sK2,X5),k4_xboole_0(sK2,X5))) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f32,f128])).
% 2.73/0.74  fof(f913,plain,(
% 2.73/0.74    ~spl5_18 | spl5_3),
% 2.73/0.74    inference(avatar_split_clause,[],[f903,f59,f910])).
% 2.73/0.74  fof(f910,plain,(
% 2.73/0.74    spl5_18 <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 2.73/0.74  fof(f903,plain,(
% 2.73/0.74    sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl5_3),
% 2.73/0.74    inference(resolution,[],[f100,f61])).
% 2.73/0.74  fof(f100,plain,(
% 2.73/0.74    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | k4_xboole_0(X2,X3) != X2) )),
% 2.73/0.74    inference(resolution,[],[f42,f40])).
% 2.73/0.74  fof(f42,plain,(
% 2.73/0.74    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 2.73/0.74    inference(cnf_transformation,[],[f26])).
% 2.73/0.74  fof(f380,plain,(
% 2.73/0.74    ~spl5_17 | ~spl5_11 | spl5_16),
% 2.73/0.74    inference(avatar_split_clause,[],[f375,f371,f268,f377])).
% 2.73/0.74  fof(f377,plain,(
% 2.73/0.74    spl5_17 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 2.73/0.74  fof(f371,plain,(
% 2.73/0.74    spl5_16 <=> sK2 = k4_xboole_0(sK2,sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 2.73/0.74  fof(f375,plain,(
% 2.73/0.74    sK2 != k3_xboole_0(sK1,sK2) | (~spl5_11 | spl5_16)),
% 2.73/0.74    inference(superposition,[],[f373,f270])).
% 2.73/0.74  fof(f373,plain,(
% 2.73/0.74    sK2 != k4_xboole_0(sK2,sK2) | spl5_16),
% 2.73/0.74    inference(avatar_component_clause,[],[f371])).
% 2.73/0.74  fof(f374,plain,(
% 2.73/0.74    ~spl5_16 | spl5_15),
% 2.73/0.74    inference(avatar_split_clause,[],[f369,f365,f371])).
% 2.73/0.74  fof(f365,plain,(
% 2.73/0.74    spl5_15 <=> r1_xboole_0(sK2,sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 2.73/0.74  fof(f369,plain,(
% 2.73/0.74    sK2 != k4_xboole_0(sK2,sK2) | spl5_15),
% 2.73/0.74    inference(resolution,[],[f367,f42])).
% 2.73/0.74  fof(f367,plain,(
% 2.73/0.74    ~r1_xboole_0(sK2,sK2) | spl5_15),
% 2.73/0.74    inference(avatar_component_clause,[],[f365])).
% 2.73/0.74  fof(f368,plain,(
% 2.73/0.74    ~spl5_15 | ~spl5_1),
% 2.73/0.74    inference(avatar_split_clause,[],[f363,f49,f365])).
% 2.73/0.74  fof(f363,plain,(
% 2.73/0.74    ~r1_xboole_0(sK2,sK2) | ~spl5_1),
% 2.73/0.74    inference(resolution,[],[f360,f51])).
% 2.73/0.74  fof(f320,plain,(
% 2.73/0.74    spl5_14 | ~spl5_6 | ~spl5_13),
% 2.73/0.74    inference(avatar_split_clause,[],[f315,f297,f82,f317])).
% 2.73/0.74  fof(f317,plain,(
% 2.73/0.74    spl5_14 <=> sK1 = k3_xboole_0(sK1,sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.73/0.74  fof(f297,plain,(
% 2.73/0.74    spl5_13 <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.73/0.74  fof(f315,plain,(
% 2.73/0.74    sK1 = k3_xboole_0(sK1,sK1) | (~spl5_6 | ~spl5_13)),
% 2.73/0.74    inference(forward_demodulation,[],[f310,f245])).
% 2.73/0.74  fof(f245,plain,(
% 2.73/0.74    ( ! [X0] : (sK1 = k4_xboole_0(sK1,k3_xboole_0(X0,sK2))) ) | ~spl5_6),
% 2.73/0.74    inference(resolution,[],[f231,f41])).
% 2.73/0.74  fof(f231,plain,(
% 2.73/0.74    ( ! [X0] : (r1_xboole_0(sK1,k3_xboole_0(X0,sK2))) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f213,f33])).
% 2.73/0.74  fof(f213,plain,(
% 2.73/0.74    ( ! [X36] : (r1_xboole_0(sK1,k3_xboole_0(sK2,X36))) ) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f129,f35])).
% 2.73/0.74  fof(f129,plain,(
% 2.73/0.74    ( ! [X1] : (r1_xboole_0(sK1,k4_xboole_0(sK2,X1))) ) | ~spl5_6),
% 2.73/0.74    inference(resolution,[],[f125,f40])).
% 2.73/0.74  fof(f310,plain,(
% 2.73/0.74    k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) = k3_xboole_0(sK1,sK1) | ~spl5_13),
% 2.73/0.74    inference(superposition,[],[f35,f299])).
% 2.73/0.74  fof(f299,plain,(
% 2.73/0.74    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | ~spl5_13),
% 2.73/0.74    inference(avatar_component_clause,[],[f297])).
% 2.73/0.74  fof(f300,plain,(
% 2.73/0.74    spl5_13 | ~spl5_8),
% 2.73/0.74    inference(avatar_split_clause,[],[f192,f93,f297])).
% 2.73/0.74  fof(f93,plain,(
% 2.73/0.74    spl5_8 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 2.73/0.74  fof(f192,plain,(
% 2.73/0.74    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | ~spl5_8),
% 2.73/0.74    inference(superposition,[],[f35,f95])).
% 2.73/0.74  fof(f95,plain,(
% 2.73/0.74    sK1 = k4_xboole_0(sK1,sK2) | ~spl5_8),
% 2.73/0.74    inference(avatar_component_clause,[],[f93])).
% 2.73/0.74  fof(f289,plain,(
% 2.73/0.74    spl5_12 | ~spl5_8 | ~spl5_11),
% 2.73/0.74    inference(avatar_split_clause,[],[f284,f268,f93,f286])).
% 2.73/0.74  fof(f286,plain,(
% 2.73/0.74    spl5_12 <=> sK2 = k3_xboole_0(sK2,sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.73/0.74  fof(f284,plain,(
% 2.73/0.74    sK2 = k3_xboole_0(sK2,sK2) | (~spl5_8 | ~spl5_11)),
% 2.73/0.74    inference(forward_demodulation,[],[f279,f207])).
% 2.73/0.74  fof(f207,plain,(
% 2.73/0.74    ( ! [X26] : (sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,X26))) ) | ~spl5_8),
% 2.73/0.74    inference(superposition,[],[f140,f35])).
% 2.73/0.74  fof(f140,plain,(
% 2.73/0.74    ( ! [X0] : (sK2 = k4_xboole_0(sK2,k4_xboole_0(sK1,X0))) ) | ~spl5_8),
% 2.73/0.74    inference(resolution,[],[f138,f41])).
% 2.73/0.74  fof(f138,plain,(
% 2.73/0.74    ( ! [X1] : (r1_xboole_0(sK2,k4_xboole_0(sK1,X1))) ) | ~spl5_8),
% 2.73/0.74    inference(resolution,[],[f134,f40])).
% 2.73/0.74  fof(f134,plain,(
% 2.73/0.74    ( ! [X0] : (r1_xboole_0(k4_xboole_0(sK1,X0),sK2)) ) | ~spl5_8),
% 2.73/0.74    inference(resolution,[],[f124,f32])).
% 2.73/0.74  fof(f124,plain,(
% 2.73/0.74    ( ! [X1] : (~r1_tarski(X1,sK1) | r1_xboole_0(X1,sK2)) ) | ~spl5_8),
% 2.73/0.74    inference(superposition,[],[f47,f95])).
% 2.73/0.74  fof(f279,plain,(
% 2.73/0.74    k3_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_11),
% 2.73/0.74    inference(superposition,[],[f35,f270])).
% 2.73/0.74  fof(f271,plain,(
% 2.73/0.74    spl5_11 | ~spl5_6),
% 2.73/0.74    inference(avatar_split_clause,[],[f218,f82,f268])).
% 2.73/0.74  fof(f218,plain,(
% 2.73/0.74    k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) | ~spl5_6),
% 2.73/0.74    inference(forward_demodulation,[],[f190,f33])).
% 2.73/0.74  fof(f190,plain,(
% 2.73/0.74    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f35,f84])).
% 2.73/0.74  fof(f110,plain,(
% 2.73/0.74    ~spl5_10 | spl5_3),
% 2.73/0.74    inference(avatar_split_clause,[],[f98,f59,f107])).
% 2.73/0.74  fof(f107,plain,(
% 2.73/0.74    spl5_10 <=> k2_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.73/0.74  fof(f98,plain,(
% 2.73/0.74    k2_xboole_0(sK0,sK2) != k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 2.73/0.74    inference(resolution,[],[f42,f61])).
% 2.73/0.74  fof(f105,plain,(
% 2.73/0.74    spl5_9 | ~spl5_8),
% 2.73/0.74    inference(avatar_split_clause,[],[f97,f93,f102])).
% 2.73/0.74  fof(f102,plain,(
% 2.73/0.74    spl5_9 <=> r1_tarski(sK1,sK1)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 2.73/0.74  fof(f97,plain,(
% 2.73/0.74    r1_tarski(sK1,sK1) | ~spl5_8),
% 2.73/0.74    inference(superposition,[],[f32,f95])).
% 2.73/0.74  fof(f96,plain,(
% 2.73/0.74    spl5_8 | ~spl5_5),
% 2.73/0.74    inference(avatar_split_clause,[],[f79,f70,f93])).
% 2.73/0.74  fof(f79,plain,(
% 2.73/0.74    sK1 = k4_xboole_0(sK1,sK2) | ~spl5_5),
% 2.73/0.74    inference(resolution,[],[f41,f72])).
% 2.73/0.74  fof(f91,plain,(
% 2.73/0.74    spl5_7 | ~spl5_6),
% 2.73/0.74    inference(avatar_split_clause,[],[f86,f82,f88])).
% 2.73/0.74  fof(f88,plain,(
% 2.73/0.74    spl5_7 <=> r1_tarski(sK2,sK2)),
% 2.73/0.74    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 2.73/0.74  fof(f86,plain,(
% 2.73/0.74    r1_tarski(sK2,sK2) | ~spl5_6),
% 2.73/0.74    inference(superposition,[],[f32,f84])).
% 2.73/0.74  fof(f85,plain,(
% 2.73/0.74    spl5_6 | ~spl5_2),
% 2.73/0.74    inference(avatar_split_clause,[],[f80,f54,f82])).
% 2.73/0.74  fof(f80,plain,(
% 2.73/0.74    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_2),
% 2.73/0.74    inference(resolution,[],[f41,f56])).
% 2.73/0.74  fof(f73,plain,(
% 2.73/0.74    spl5_5 | ~spl5_2),
% 2.73/0.74    inference(avatar_split_clause,[],[f68,f54,f70])).
% 2.73/0.74  fof(f68,plain,(
% 2.73/0.74    r1_xboole_0(sK1,sK2) | ~spl5_2),
% 2.73/0.74    inference(resolution,[],[f40,f56])).
% 2.73/0.74  fof(f67,plain,(
% 2.73/0.74    spl5_4),
% 2.73/0.74    inference(avatar_split_clause,[],[f27,f64])).
% 2.73/0.74  fof(f27,plain,(
% 2.73/0.74    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.73/0.74    inference(cnf_transformation,[],[f23])).
% 2.73/0.74  fof(f23,plain,(
% 2.73/0.74    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 2.73/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f16,f22])).
% 2.73/0.74  fof(f22,plain,(
% 2.73/0.74    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 2.73/0.74    introduced(choice_axiom,[])).
% 2.73/0.74  fof(f16,plain,(
% 2.73/0.74    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 2.73/0.74    inference(flattening,[],[f15])).
% 2.73/0.74  fof(f15,plain,(
% 2.73/0.74    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 2.73/0.74    inference(ennf_transformation,[],[f13])).
% 2.73/0.74  fof(f13,negated_conjecture,(
% 2.73/0.74    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.73/0.74    inference(negated_conjecture,[],[f12])).
% 2.73/0.74  fof(f12,conjecture,(
% 2.73/0.74    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 2.73/0.74    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 2.73/0.74  fof(f62,plain,(
% 2.73/0.74    ~spl5_3),
% 2.73/0.74    inference(avatar_split_clause,[],[f30,f59])).
% 2.73/0.74  fof(f30,plain,(
% 2.73/0.74    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 2.73/0.74    inference(cnf_transformation,[],[f23])).
% 2.73/0.74  fof(f57,plain,(
% 2.73/0.74    spl5_2),
% 2.73/0.74    inference(avatar_split_clause,[],[f29,f54])).
% 2.73/0.74  fof(f29,plain,(
% 2.73/0.74    r1_xboole_0(sK2,sK1)),
% 2.73/0.74    inference(cnf_transformation,[],[f23])).
% 2.73/0.74  fof(f52,plain,(
% 2.73/0.74    spl5_1),
% 2.73/0.74    inference(avatar_split_clause,[],[f28,f49])).
% 2.73/0.74  fof(f28,plain,(
% 2.73/0.74    r2_hidden(sK3,sK2)),
% 2.73/0.74    inference(cnf_transformation,[],[f23])).
% 2.73/0.74  % SZS output end Proof for theBenchmark
% 2.73/0.74  % (4231)------------------------------
% 2.73/0.74  % (4231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.73/0.74  % (4231)Termination reason: Refutation
% 2.73/0.74  
% 2.73/0.74  % (4231)Memory used [KB]: 9210
% 2.73/0.74  % (4231)Time elapsed: 0.294 s
% 2.73/0.74  % (4231)------------------------------
% 2.73/0.74  % (4231)------------------------------
% 2.73/0.75  % (4230)Success in time 0.389 s
%------------------------------------------------------------------------------
