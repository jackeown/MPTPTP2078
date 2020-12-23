%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:43:35 EST 2020

% Result     : Theorem 1.81s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  316 (1007 expanded)
%              Number of leaves         :   71 ( 387 expanded)
%              Depth                    :   14
%              Number of atoms          :  702 (2190 expanded)
%              Number of equality atoms :  109 ( 473 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2719,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f78,f89,f96,f111,f147,f189,f204,f209,f219,f226,f232,f237,f242,f254,f259,f275,f371,f394,f399,f429,f446,f474,f500,f511,f516,f525,f532,f539,f563,f585,f592,f599,f835,f840,f893,f899,f950,f1000,f1025,f1038,f1113,f1160,f1165,f1174,f1179,f2350,f2358,f2363,f2395,f2519,f2527,f2535,f2558,f2716])).

fof(f2716,plain,
    ( spl5_3
    | ~ spl5_5
    | ~ spl5_55 ),
    inference(avatar_contradiction_clause,[],[f2715])).

fof(f2715,plain,
    ( $false
    | spl5_3
    | ~ spl5_5
    | ~ spl5_55 ),
    inference(subsumption_resolution,[],[f2714,f2518])).

fof(f2518,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f2516])).

fof(f2516,plain,
    ( spl5_55
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f2714,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl5_3
    | ~ spl5_5 ),
    inference(subsumption_resolution,[],[f2698,f77])).

fof(f77,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl5_5
  <=> r1_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f2698,plain,
    ( ~ r1_xboole_0(sK1,sK2)
    | ~ r1_xboole_0(sK1,sK0)
    | spl5_3 ),
    inference(resolution,[],[f505,f65])).

fof(f65,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl5_3
  <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f505,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f2558,plain,
    ( spl5_58
    | ~ spl5_56 ),
    inference(avatar_split_clause,[],[f2529,f2524,f2555])).

fof(f2555,plain,
    ( spl5_58
  <=> sK0 = k4_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).

fof(f2524,plain,
    ( spl5_56
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).

fof(f2529,plain,
    ( sK0 = k4_xboole_0(sK0,sK1)
    | ~ spl5_56 ),
    inference(resolution,[],[f2526,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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

fof(f2526,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_56 ),
    inference(avatar_component_clause,[],[f2524])).

fof(f2535,plain,
    ( spl5_57
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f2521,f2516,f2532])).

fof(f2532,plain,
    ( spl5_57
  <=> sK1 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).

fof(f2521,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl5_55 ),
    inference(resolution,[],[f2518,f42])).

fof(f2527,plain,
    ( spl5_56
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f2522,f2516,f2524])).

fof(f2522,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl5_55 ),
    inference(resolution,[],[f2518,f41])).

fof(f2519,plain,
    ( spl5_55
    | ~ spl5_54 ),
    inference(avatar_split_clause,[],[f2490,f2392,f2516])).

fof(f2392,plain,
    ( spl5_54
  <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f2490,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl5_54 ),
    inference(resolution,[],[f2398,f73])).

fof(f73,plain,(
    ! [X0,X1] : r1_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(resolution,[],[f41,f34])).

fof(f34,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f2398,plain,
    ( ! [X2] :
        ( ~ r1_xboole_0(X2,k4_xboole_0(sK0,sK1))
        | r1_xboole_0(X2,sK0) )
    | ~ spl5_54 ),
    inference(superposition,[],[f136,f2394])).

fof(f2394,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f2392])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X2,k3_xboole_0(X1,X0))
      | ~ r1_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f51,f35])).

fof(f35,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k3_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ~ ( r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

fof(f2395,plain,
    ( spl5_54
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f2364,f1035,f58,f2392])).

fof(f58,plain,
    ( spl5_2
  <=> r1_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f1035,plain,
    ( spl5_44
  <=> r1_tarski(k3_xboole_0(sK0,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f2364,plain,
    ( sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(superposition,[],[f2269,f172])).

fof(f172,plain,(
    ! [X2,X3] : k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f37,f37])).

fof(f37,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f2269,plain,
    ( ! [X4] : k4_xboole_0(X4,k3_xboole_0(sK0,sK1)) = X4
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(resolution,[],[f2251,f42])).

fof(f2251,plain,
    ( ! [X4] : r1_xboole_0(X4,k3_xboole_0(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(resolution,[],[f2211,f41])).

fof(f2211,plain,
    ( ! [X18] : r1_xboole_0(k3_xboole_0(sK0,sK1),X18)
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(resolution,[],[f2200,f1545])).

fof(f1545,plain,
    ( ! [X3] : r1_xboole_0(k3_xboole_0(X3,sK1),k3_xboole_0(sK0,sK1))
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(resolution,[],[f1453,f41])).

fof(f1453,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X0,sK1))
    | ~ spl5_2
    | ~ spl5_44 ),
    inference(resolution,[],[f1435,f1037])).

fof(f1037,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f1035])).

fof(f1435,plain,
    ( ! [X4,X5] :
        ( ~ r1_tarski(X5,sK2)
        | r1_xboole_0(X5,k3_xboole_0(X4,sK1)) )
    | ~ spl5_2 ),
    inference(superposition,[],[f50,f1343])).

fof(f1343,plain,
    ( ! [X0] : sK2 = k4_xboole_0(sK2,k3_xboole_0(X0,sK1))
    | ~ spl5_2 ),
    inference(superposition,[],[f1281,f35])).

fof(f1281,plain,
    ( ! [X155] : sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,X155))
    | ~ spl5_2 ),
    inference(resolution,[],[f134,f60])).

fof(f60,plain,
    ( r1_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,k3_xboole_0(X1,X2)) = X0 ) ),
    inference(resolution,[],[f51,f42])).

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

fof(f2200,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f2196])).

fof(f2196,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X0)
      | r1_xboole_0(X0,X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f198,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f25])).

fof(f25,plain,(
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

fof(f198,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f2363,plain,
    ( ~ spl5_53
    | spl5_50 ),
    inference(avatar_split_clause,[],[f2353,f2344,f2360])).

fof(f2360,plain,
    ( spl5_53
  <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f2344,plain,
    ( spl5_50
  <=> r1_xboole_0(k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f2353,plain,
    ( k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK2)
    | spl5_50 ),
    inference(resolution,[],[f2346,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k4_xboole_0(X0,X1) != X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f2346,plain,
    ( ~ r1_xboole_0(k1_tarski(sK3),sK2)
    | spl5_50 ),
    inference(avatar_component_clause,[],[f2344])).

fof(f2358,plain,
    ( ~ spl5_52
    | spl5_50 ),
    inference(avatar_split_clause,[],[f2352,f2344,f2355])).

fof(f2355,plain,
    ( spl5_52
  <=> sK2 = k4_xboole_0(sK2,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f2352,plain,
    ( sK2 != k4_xboole_0(sK2,k1_tarski(sK3))
    | spl5_50 ),
    inference(resolution,[],[f2346,f106])).

fof(f106,plain,(
    ! [X2,X3] :
      ( r1_xboole_0(X3,X2)
      | k4_xboole_0(X2,X3) != X2 ) ),
    inference(resolution,[],[f43,f41])).

fof(f2350,plain,
    ( ~ spl5_50
    | spl5_51
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f2209,f997,f2348,f2344])).

fof(f2348,plain,
    ( spl5_51
  <=> ! [X16] : r1_xboole_0(k1_tarski(sK3),X16) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f997,plain,
    ( spl5_42
  <=> k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f2209,plain,
    ( ! [X16] :
        ( r1_xboole_0(k1_tarski(sK3),X16)
        | ~ r1_xboole_0(k1_tarski(sK3),sK2) )
    | ~ spl5_42 ),
    inference(resolution,[],[f2200,f1009])).

fof(f1009,plain,
    ( ! [X2] :
        ( r1_xboole_0(X2,k1_tarski(sK3))
        | ~ r1_xboole_0(X2,sK2) )
    | ~ spl5_42 ),
    inference(superposition,[],[f136,f999])).

fof(f999,plain,
    ( k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2)
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f997])).

fof(f1179,plain,
    ( spl5_49
    | ~ spl5_47 ),
    inference(avatar_split_clause,[],[f1169,f1162,f1176])).

fof(f1176,plain,
    ( spl5_49
  <=> r1_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f1162,plain,
    ( spl5_47
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f1169,plain,
    ( r1_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))
    | ~ spl5_47 ),
    inference(resolution,[],[f1164,f41])).

fof(f1164,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK0))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f1162])).

fof(f1174,plain,
    ( spl5_48
    | ~ spl5_46 ),
    inference(avatar_split_clause,[],[f1167,f1157,f1171])).

fof(f1171,plain,
    ( spl5_48
  <=> r1_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f1157,plain,
    ( spl5_46
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).

fof(f1167,plain,
    ( r1_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK2))
    | ~ spl5_46 ),
    inference(resolution,[],[f1159,f41])).

fof(f1159,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK0))
    | ~ spl5_46 ),
    inference(avatar_component_clause,[],[f1157])).

fof(f1165,plain,
    ( spl5_47
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f1148,f1110,f1162])).

fof(f1110,plain,
    ( spl5_45
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f1148,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK0))
    | ~ spl5_45 ),
    inference(resolution,[],[f1119,f312])).

fof(f312,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f178,f35])).

fof(f178,plain,(
    ! [X10,X9] : r1_xboole_0(k4_xboole_0(X9,X10),k3_xboole_0(X9,X10)) ),
    inference(superposition,[],[f73,f37])).

fof(f1119,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(X3,k3_xboole_0(sK0,sK1))
        | r1_xboole_0(k3_xboole_0(sK1,sK2),X3) )
    | ~ spl5_45 ),
    inference(superposition,[],[f152,f1112])).

fof(f1112,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f1110])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(k3_xboole_0(X1,X0),X2)
      | ~ r1_xboole_0(X2,X0) ) ),
    inference(superposition,[],[f135,f35])).

fof(f135,plain,(
    ! [X4,X5,X3] :
      ( r1_xboole_0(k3_xboole_0(X4,X5),X3)
      | ~ r1_xboole_0(X3,X4) ) ),
    inference(resolution,[],[f51,f41])).

fof(f1160,plain,
    ( spl5_46
    | ~ spl5_45 ),
    inference(avatar_split_clause,[],[f1146,f1110,f1157])).

fof(f1146,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK0))
    | ~ spl5_45 ),
    inference(resolution,[],[f1119,f747])).

fof(f747,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X1,X1),k3_xboole_0(X1,X0)) ),
    inference(superposition,[],[f683,f35])).

fof(f683,plain,(
    ! [X2,X3] : r1_xboole_0(k4_xboole_0(X3,X3),k3_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f669,f654])).

fof(f654,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(X3,X3) ),
    inference(forward_demodulation,[],[f653,f171])).

fof(f171,plain,(
    ! [X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,X0) ),
    inference(superposition,[],[f37,f81])).

fof(f81,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0 ),
    inference(resolution,[],[f42,f73])).

fof(f653,plain,(
    ! [X2,X3] : k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k3_xboole_0(X3,k4_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f636,f35])).

fof(f636,plain,(
    ! [X2,X3] : k3_xboole_0(k4_xboole_0(X2,X3),X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) ),
    inference(superposition,[],[f37,f82])).

fof(f82,plain,(
    ! [X2,X3] : k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),X3) ),
    inference(resolution,[],[f42,f34])).

fof(f669,plain,(
    ! [X2,X3] : r1_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),k3_xboole_0(X2,X3)) ),
    inference(superposition,[],[f658,f37])).

fof(f658,plain,(
    ! [X17,X16] : r1_xboole_0(k4_xboole_0(X17,X17),k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f657,f171])).

fof(f657,plain,(
    ! [X17,X16] : r1_xboole_0(k3_xboole_0(X17,k4_xboole_0(X16,X17)),k4_xboole_0(X16,X17)) ),
    inference(forward_demodulation,[],[f642,f35])).

fof(f642,plain,(
    ! [X17,X16] : r1_xboole_0(k3_xboole_0(k4_xboole_0(X16,X17),X17),k4_xboole_0(X16,X17)) ),
    inference(superposition,[],[f179,f82])).

fof(f179,plain,(
    ! [X12,X11] : r1_xboole_0(k3_xboole_0(X11,X12),k4_xboole_0(X11,X12)) ),
    inference(superposition,[],[f34,f37])).

fof(f1113,plain,
    ( spl5_45
    | ~ spl5_16
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f574,f560,f234,f1110])).

fof(f234,plain,
    ( spl5_16
  <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f560,plain,
    ( spl5_33
  <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f574,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_16
    | ~ spl5_33 ),
    inference(forward_demodulation,[],[f565,f236])).

fof(f236,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f234])).

fof(f565,plain,
    ( k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_33 ),
    inference(superposition,[],[f37,f562])).

fof(f562,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_33 ),
    inference(avatar_component_clause,[],[f560])).

fof(f1038,plain,
    ( spl5_44
    | ~ spl5_4
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1033,f997,f68,f1035])).

fof(f68,plain,
    ( spl5_4
  <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f1033,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),sK2)
    | ~ spl5_4
    | ~ spl5_42 ),
    inference(resolution,[],[f1016,f70])).

fof(f70,plain,
    ( r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f68])).

fof(f1016,plain,
    ( ! [X5] :
        ( ~ r1_tarski(X5,k1_tarski(sK3))
        | r1_tarski(X5,sK2) )
    | ~ spl5_42 ),
    inference(superposition,[],[f419,f999])).

fof(f419,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k3_xboole_0(X1,X0))
      | r1_tarski(X2,X0) ) ),
    inference(superposition,[],[f176,f35])).

fof(f176,plain,(
    ! [X6,X4,X5] :
      ( ~ r1_tarski(X6,k3_xboole_0(X4,X5))
      | r1_tarski(X6,X4) ) ),
    inference(superposition,[],[f49,f37])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k4_xboole_0(X1,X2))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1025,plain,
    ( spl5_43
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f1001,f997,f1022])).

fof(f1022,plain,
    ( spl5_43
  <=> k1_tarski(sK3) = k3_xboole_0(sK2,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f1001,plain,
    ( k1_tarski(sK3) = k3_xboole_0(sK2,k1_tarski(sK3))
    | ~ spl5_42 ),
    inference(superposition,[],[f999,f35])).

fof(f1000,plain,
    ( spl5_42
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f972,f53,f997])).

fof(f53,plain,
    ( spl5_1
  <=> r2_hidden(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f972,plain,
    ( k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2)
    | ~ spl5_1 ),
    inference(superposition,[],[f914,f37])).

fof(f914,plain,
    ( ! [X11] : k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),k4_xboole_0(X11,sK2))
    | ~ spl5_1 ),
    inference(superposition,[],[f81,f463])).

fof(f463,plain,
    ( ! [X0] : k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(X0,sK2),k1_tarski(sK3))
    | ~ spl5_1 ),
    inference(resolution,[],[f460,f73])).

fof(f460,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(sK2,X3)
        | k4_xboole_0(X3,k1_tarski(sK3)) = X3 )
    | ~ spl5_1 ),
    inference(resolution,[],[f45,f197])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3,X0)
        | ~ r1_xboole_0(sK2,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f40,f55])).

fof(f55,plain,
    ( r2_hidden(sK3,sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | k4_xboole_0(X0,k1_tarski(X1)) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f950,plain,
    ( ~ spl5_41
    | ~ spl5_1
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f930,f368,f53,f947])).

fof(f947,plain,
    ( spl5_41
  <=> r2_hidden(sK3,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).

fof(f368,plain,
    ( spl5_21
  <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f930,plain,
    ( ~ r2_hidden(sK3,k3_xboole_0(sK1,sK2))
    | ~ spl5_1
    | ~ spl5_21 ),
    inference(superposition,[],[f907,f370])).

fof(f370,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK2)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f368])).

fof(f907,plain,
    ( ! [X2] : ~ r2_hidden(sK3,k4_xboole_0(X2,sK2))
    | ~ spl5_1 ),
    inference(superposition,[],[f652,f463])).

fof(f652,plain,(
    ! [X37,X36] : ~ r2_hidden(X37,k4_xboole_0(X36,k1_tarski(X37))) ),
    inference(trivial_inequality_removal,[],[f651])).

fof(f651,plain,(
    ! [X37,X36] :
      ( k4_xboole_0(X36,k1_tarski(X37)) != k4_xboole_0(X36,k1_tarski(X37))
      | ~ r2_hidden(X37,k4_xboole_0(X36,k1_tarski(X37))) ) ),
    inference(superposition,[],[f44,f82])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k1_tarski(X1)) != X0
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f899,plain,
    ( spl5_40
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f726,f560,f896])).

fof(f896,plain,
    ( spl5_40
  <=> r1_xboole_0(sK1,k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f726,plain,
    ( r1_xboole_0(sK1,k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))
    | ~ spl5_33 ),
    inference(superposition,[],[f656,f562])).

fof(f656,plain,(
    ! [X14,X15] : r1_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X15)) ),
    inference(forward_demodulation,[],[f655,f171])).

fof(f655,plain,(
    ! [X14,X15] : r1_xboole_0(k4_xboole_0(X14,X15),k3_xboole_0(X15,k4_xboole_0(X14,X15))) ),
    inference(forward_demodulation,[],[f641,f35])).

fof(f641,plain,(
    ! [X14,X15] : r1_xboole_0(k4_xboole_0(X14,X15),k3_xboole_0(k4_xboole_0(X14,X15),X15)) ),
    inference(superposition,[],[f178,f82])).

fof(f893,plain,
    ( spl5_39
    | ~ spl5_33 ),
    inference(avatar_split_clause,[],[f675,f560,f890])).

fof(f890,plain,
    ( spl5_39
  <=> r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f675,plain,
    ( r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)
    | ~ spl5_33 ),
    inference(superposition,[],[f658,f562])).

fof(f840,plain,
    ( spl5_38
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f586,f582,f837])).

fof(f837,plain,
    ( spl5_38
  <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f582,plain,
    ( spl5_34
  <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f586,plain,
    ( k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2))
    | ~ spl5_34 ),
    inference(resolution,[],[f584,f42])).

fof(f584,plain,
    ( r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2))
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f582])).

fof(f835,plain,
    ( spl5_37
    | ~ spl5_30 ),
    inference(avatar_split_clause,[],[f526,f522,f832])).

fof(f832,plain,
    ( spl5_37
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f522,plain,
    ( spl5_30
  <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f526,plain,
    ( k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_30 ),
    inference(resolution,[],[f524,f42])).

fof(f524,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f522])).

fof(f599,plain,
    ( spl5_36
    | ~ spl5_16
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f489,f471,f234,f596])).

fof(f596,plain,
    ( spl5_36
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f471,plain,
    ( spl5_26
  <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f489,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_16
    | ~ spl5_26 ),
    inference(forward_demodulation,[],[f479,f236])).

fof(f479,plain,
    ( k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_26 ),
    inference(superposition,[],[f37,f473])).

fof(f473,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f471])).

fof(f592,plain,
    ( spl5_35
    | ~ spl5_16
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f555,f536,f471,f234,f589])).

fof(f589,plain,
    ( spl5_35
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).

fof(f536,plain,
    ( spl5_32
  <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f555,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK3))
    | ~ spl5_16
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f554,f489])).

fof(f554,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,k1_tarski(sK3)),k1_tarski(sK3))
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f547,f35])).

fof(f547,plain,
    ( r1_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3))
    | ~ spl5_32 ),
    inference(superposition,[],[f179,f538])).

fof(f538,plain,
    ( k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f536])).

fof(f585,plain,
    ( spl5_34
    | ~ spl5_16
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f553,f536,f471,f234,f582])).

fof(f553,plain,
    ( r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2))
    | ~ spl5_16
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f552,f489])).

fof(f552,plain,
    ( r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,k1_tarski(sK3)))
    | ~ spl5_32 ),
    inference(forward_demodulation,[],[f546,f35])).

fof(f546,plain,
    ( r1_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),sK1))
    | ~ spl5_32 ),
    inference(superposition,[],[f178,f538])).

fof(f563,plain,
    ( spl5_33
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f533,f529,f560])).

fof(f529,plain,
    ( spl5_31
  <=> r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f533,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_31 ),
    inference(resolution,[],[f531,f42])).

fof(f531,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f529])).

fof(f539,plain,
    ( spl5_32
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f483,f471,f536])).

fof(f483,plain,
    ( k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_26 ),
    inference(superposition,[],[f81,f473])).

fof(f532,plain,
    ( spl5_31
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f475,f471,f68,f529])).

fof(f475,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(superposition,[],[f166,f473])).

fof(f166,plain,
    ( ! [X1] : r1_xboole_0(k4_xboole_0(X1,k1_tarski(sK3)),k3_xboole_0(sK0,sK1))
    | ~ spl5_4 ),
    inference(resolution,[],[f164,f41])).

fof(f164,plain,
    ( ! [X0] : r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK3)))
    | ~ spl5_4 ),
    inference(resolution,[],[f133,f70])).

fof(f133,plain,(
    ! [X4,X2,X3] :
      ( ~ r1_tarski(X4,X2)
      | r1_xboole_0(X4,k4_xboole_0(X3,X2)) ) ),
    inference(superposition,[],[f50,f81])).

fof(f525,plain,
    ( spl5_30
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f476,f471,f68,f522])).

fof(f476,plain,
    ( r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)
    | ~ spl5_4
    | ~ spl5_26 ),
    inference(superposition,[],[f164,f473])).

fof(f516,plain,
    ( spl5_29
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f482,f471,f513])).

fof(f513,plain,
    ( spl5_29
  <=> r1_xboole_0(k1_tarski(sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f482,plain,
    ( r1_xboole_0(k1_tarski(sK3),sK1)
    | ~ spl5_26 ),
    inference(superposition,[],[f73,f473])).

fof(f511,plain,
    ( spl5_28
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f478,f471,f508])).

fof(f508,plain,
    ( spl5_28
  <=> r1_xboole_0(sK1,k1_tarski(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f478,plain,
    ( r1_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_26 ),
    inference(superposition,[],[f34,f473])).

fof(f500,plain,
    ( ~ spl5_27
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f488,f471,f497])).

fof(f497,plain,
    ( spl5_27
  <=> r2_hidden(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f488,plain,
    ( ~ r2_hidden(sK3,sK1)
    | ~ spl5_26 ),
    inference(trivial_inequality_removal,[],[f477])).

fof(f477,plain,
    ( sK1 != sK1
    | ~ r2_hidden(sK3,sK1)
    | ~ spl5_26 ),
    inference(superposition,[],[f44,f473])).

fof(f474,plain,
    ( spl5_26
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f461,f58,f53,f471])).

fof(f461,plain,
    ( sK1 = k4_xboole_0(sK1,k1_tarski(sK3))
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f460,f60])).

fof(f446,plain,
    ( spl5_25
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f282,f272,f234,f443])).

fof(f443,plain,
    ( spl5_25
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f272,plain,
    ( spl5_20
  <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f282,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_16
    | ~ spl5_20 ),
    inference(forward_demodulation,[],[f276,f236])).

fof(f276,plain,
    ( k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_20 ),
    inference(superposition,[],[f37,f274])).

fof(f274,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f272])).

fof(f429,plain,
    ( spl5_24
    | ~ spl5_10
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f270,f239,f186,f426])).

fof(f426,plain,
    ( spl5_24
  <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f186,plain,
    ( spl5_10
  <=> k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f239,plain,
    ( spl5_17
  <=> sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f270,plain,
    ( k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_10
    | ~ spl5_17 ),
    inference(forward_demodulation,[],[f264,f188])).

fof(f188,plain,
    ( k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f186])).

fof(f264,plain,
    ( k4_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_17 ),
    inference(superposition,[],[f37,f241])).

fof(f241,plain,
    ( sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f239])).

fof(f399,plain,
    ( spl5_23
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f385,f368,f239,f186,f396])).

fof(f396,plain,
    ( spl5_23
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f385,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))
    | ~ spl5_10
    | ~ spl5_17
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f384,f270])).

fof(f384,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)))
    | ~ spl5_21 ),
    inference(forward_demodulation,[],[f378,f35])).

fof(f378,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(sK1,sK2),sK2))
    | ~ spl5_21 ),
    inference(superposition,[],[f178,f370])).

fof(f394,plain,
    ( spl5_22
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f262,f256,f391])).

fof(f391,plain,
    ( spl5_22
  <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f256,plain,
    ( spl5_19
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f262,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl5_19 ),
    inference(resolution,[],[f258,f42])).

fof(f258,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f256])).

fof(f371,plain,
    ( spl5_21
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f212,f206,f368])).

fof(f206,plain,
    ( spl5_12
  <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f212,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK2)
    | ~ spl5_12 ),
    inference(resolution,[],[f208,f42])).

fof(f208,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK2)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f206])).

fof(f275,plain,
    ( spl5_20
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f249,f234,f272])).

fof(f249,plain,
    ( sK1 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_16 ),
    inference(forward_demodulation,[],[f243,f173])).

fof(f173,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(superposition,[],[f37,f81])).

fof(f243,plain,
    ( k3_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_16 ),
    inference(superposition,[],[f37,f236])).

fof(f259,plain,
    ( spl5_19
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f248,f234,f256])).

fof(f248,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK1)
    | ~ spl5_16 ),
    inference(superposition,[],[f34,f236])).

fof(f254,plain,
    ( spl5_18
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f247,f234,f251])).

fof(f251,plain,
    ( spl5_18
  <=> r1_xboole_0(sK1,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f247,plain,
    ( r1_xboole_0(sK1,k3_xboole_0(sK1,sK2))
    | ~ spl5_16 ),
    inference(superposition,[],[f73,f236])).

fof(f242,plain,
    ( spl5_17
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f196,f186,f239])).

fof(f196,plain,
    ( sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_10 ),
    inference(forward_demodulation,[],[f190,f173])).

fof(f190,plain,
    ( k3_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_10 ),
    inference(superposition,[],[f37,f188])).

fof(f237,plain,
    ( spl5_16
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f170,f93,f234])).

fof(f93,plain,
    ( spl5_7
  <=> sK1 = k4_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f170,plain,
    ( k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)
    | ~ spl5_7 ),
    inference(superposition,[],[f37,f95])).

fof(f95,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f232,plain,
    ( ~ spl5_15
    | ~ spl5_10
    | spl5_14 ),
    inference(avatar_split_clause,[],[f227,f223,f186,f229])).

fof(f229,plain,
    ( spl5_15
  <=> sK2 = k3_xboole_0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f223,plain,
    ( spl5_14
  <=> sK2 = k4_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f227,plain,
    ( sK2 != k3_xboole_0(sK1,sK2)
    | ~ spl5_10
    | spl5_14 ),
    inference(superposition,[],[f225,f188])).

fof(f225,plain,
    ( sK2 != k4_xboole_0(sK2,sK2)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f223])).

fof(f226,plain,
    ( ~ spl5_14
    | spl5_13 ),
    inference(avatar_split_clause,[],[f220,f216,f223])).

fof(f216,plain,
    ( spl5_13
  <=> r1_xboole_0(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f220,plain,
    ( sK2 != k4_xboole_0(sK2,sK2)
    | spl5_13 ),
    inference(resolution,[],[f218,f106])).

fof(f218,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f216])).

fof(f219,plain,
    ( ~ spl5_13
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f214,f53,f216])).

fof(f214,plain,
    ( ~ r1_xboole_0(sK2,sK2)
    | ~ spl5_1 ),
    inference(resolution,[],[f197,f55])).

fof(f209,plain,
    ( spl5_12
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f195,f186,f206])).

fof(f195,plain,
    ( r1_xboole_0(k3_xboole_0(sK1,sK2),sK2)
    | ~ spl5_10 ),
    inference(superposition,[],[f34,f188])).

fof(f204,plain,
    ( spl5_11
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f194,f186,f201])).

fof(f201,plain,
    ( spl5_11
  <=> r1_xboole_0(sK2,k3_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f194,plain,
    ( r1_xboole_0(sK2,k3_xboole_0(sK1,sK2))
    | ~ spl5_10 ),
    inference(superposition,[],[f73,f188])).

fof(f189,plain,
    ( spl5_10
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f180,f86,f186])).

fof(f86,plain,
    ( spl5_6
  <=> sK2 = k4_xboole_0(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f180,plain,
    ( k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)
    | ~ spl5_6 ),
    inference(forward_demodulation,[],[f169,f35])).

fof(f169,plain,
    ( k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2)
    | ~ spl5_6 ),
    inference(superposition,[],[f37,f88])).

fof(f88,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f147,plain,
    ( ~ spl5_9
    | spl5_3 ),
    inference(avatar_split_clause,[],[f138,f63,f144])).

fof(f144,plain,
    ( spl5_9
  <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f138,plain,
    ( sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))
    | spl5_3 ),
    inference(resolution,[],[f106,f65])).

fof(f111,plain,
    ( ~ spl5_8
    | spl5_3 ),
    inference(avatar_split_clause,[],[f104,f63,f108])).

fof(f108,plain,
    ( spl5_8
  <=> k2_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f104,plain,
    ( k2_xboole_0(sK0,sK2) != k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    | spl5_3 ),
    inference(resolution,[],[f43,f65])).

fof(f96,plain,
    ( spl5_7
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f83,f75,f93])).

fof(f83,plain,
    ( sK1 = k4_xboole_0(sK1,sK2)
    | ~ spl5_5 ),
    inference(resolution,[],[f42,f77])).

fof(f89,plain,
    ( spl5_6
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f84,f58,f86])).

fof(f84,plain,
    ( sK2 = k4_xboole_0(sK2,sK1)
    | ~ spl5_2 ),
    inference(resolution,[],[f42,f60])).

fof(f78,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f72,f58,f75])).

fof(f72,plain,
    ( r1_xboole_0(sK1,sK2)
    | ~ spl5_2 ),
    inference(resolution,[],[f41,f60])).

fof(f71,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f29,f68])).

fof(f29,plain,(
    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)
    & r1_xboole_0(sK2,sK1)
    & r2_hidden(sK3,sK2)
    & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f23])).

fof(f23,plain,
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

fof(f66,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f32,f63])).

fof(f32,plain,(
    ~ r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f61,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f31,f58])).

fof(f31,plain,(
    r1_xboole_0(sK2,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f56,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f30,f53])).

fof(f30,plain,(
    r2_hidden(sK3,sK2) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.45  % (18490)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.20/0.46  % (18475)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.46  % (18476)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.46  % (18479)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.47  % (18482)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.47  % (18487)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.47  % (18486)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.47  % (18489)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.47  % (18478)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.47  % (18480)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.47  % (18492)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.48  % (18491)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.48  % (18484)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.49  % (18483)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.49  % (18485)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 0.20/0.49  % (18477)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.49  % (18488)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.49  % (18481)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.56  % (18486)Refutation not found, incomplete strategy% (18486)------------------------------
% 0.20/0.56  % (18486)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18486)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18486)Memory used [KB]: 11897
% 0.20/0.56  % (18486)Time elapsed: 0.144 s
% 0.20/0.56  % (18486)------------------------------
% 0.20/0.56  % (18486)------------------------------
% 1.81/0.61  % (18475)Refutation found. Thanks to Tanya!
% 1.81/0.61  % SZS status Theorem for theBenchmark
% 1.81/0.61  % SZS output start Proof for theBenchmark
% 1.81/0.61  fof(f2719,plain,(
% 1.81/0.61    $false),
% 1.81/0.61    inference(avatar_sat_refutation,[],[f56,f61,f66,f71,f78,f89,f96,f111,f147,f189,f204,f209,f219,f226,f232,f237,f242,f254,f259,f275,f371,f394,f399,f429,f446,f474,f500,f511,f516,f525,f532,f539,f563,f585,f592,f599,f835,f840,f893,f899,f950,f1000,f1025,f1038,f1113,f1160,f1165,f1174,f1179,f2350,f2358,f2363,f2395,f2519,f2527,f2535,f2558,f2716])).
% 1.81/0.61  fof(f2716,plain,(
% 1.81/0.61    spl5_3 | ~spl5_5 | ~spl5_55),
% 1.81/0.61    inference(avatar_contradiction_clause,[],[f2715])).
% 1.81/0.61  fof(f2715,plain,(
% 1.81/0.61    $false | (spl5_3 | ~spl5_5 | ~spl5_55)),
% 1.81/0.61    inference(subsumption_resolution,[],[f2714,f2518])).
% 1.81/0.61  fof(f2518,plain,(
% 1.81/0.61    r1_xboole_0(sK1,sK0) | ~spl5_55),
% 1.81/0.61    inference(avatar_component_clause,[],[f2516])).
% 1.81/0.61  fof(f2516,plain,(
% 1.81/0.61    spl5_55 <=> r1_xboole_0(sK1,sK0)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 1.81/0.61  fof(f2714,plain,(
% 1.81/0.61    ~r1_xboole_0(sK1,sK0) | (spl5_3 | ~spl5_5)),
% 1.81/0.61    inference(subsumption_resolution,[],[f2698,f77])).
% 1.81/0.61  fof(f77,plain,(
% 1.81/0.61    r1_xboole_0(sK1,sK2) | ~spl5_5),
% 1.81/0.61    inference(avatar_component_clause,[],[f75])).
% 1.81/0.61  fof(f75,plain,(
% 1.81/0.61    spl5_5 <=> r1_xboole_0(sK1,sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.81/0.61  fof(f2698,plain,(
% 1.81/0.61    ~r1_xboole_0(sK1,sK2) | ~r1_xboole_0(sK1,sK0) | spl5_3),
% 1.81/0.61    inference(resolution,[],[f505,f65])).
% 1.81/0.61  fof(f65,plain,(
% 1.81/0.61    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 1.81/0.61    inference(avatar_component_clause,[],[f63])).
% 1.81/0.61  fof(f63,plain,(
% 1.81/0.61    spl5_3 <=> r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.81/0.61  fof(f505,plain,(
% 1.81/0.61    ( ! [X10,X11,X9] : (r1_xboole_0(k2_xboole_0(X10,X11),X9) | ~r1_xboole_0(X9,X11) | ~r1_xboole_0(X9,X10)) )),
% 1.81/0.61    inference(resolution,[],[f46,f41])).
% 1.81/0.61  fof(f41,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f19])).
% 1.81/0.61  fof(f19,plain,(
% 1.81/0.61    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.81/0.61    inference(ennf_transformation,[],[f2])).
% 1.81/0.61  fof(f2,axiom,(
% 1.81/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.81/0.61  fof(f46,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f20])).
% 1.81/0.61  fof(f20,plain,(
% 1.81/0.61    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.81/0.61    inference(ennf_transformation,[],[f6])).
% 1.81/0.61  fof(f6,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.81/0.61  fof(f2558,plain,(
% 1.81/0.61    spl5_58 | ~spl5_56),
% 1.81/0.61    inference(avatar_split_clause,[],[f2529,f2524,f2555])).
% 1.81/0.61  fof(f2555,plain,(
% 1.81/0.61    spl5_58 <=> sK0 = k4_xboole_0(sK0,sK1)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_58])])).
% 1.81/0.61  fof(f2524,plain,(
% 1.81/0.61    spl5_56 <=> r1_xboole_0(sK0,sK1)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_56])])).
% 1.81/0.61  fof(f2529,plain,(
% 1.81/0.61    sK0 = k4_xboole_0(sK0,sK1) | ~spl5_56),
% 1.81/0.61    inference(resolution,[],[f2526,f42])).
% 1.81/0.61  fof(f42,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) = X0) )),
% 1.81/0.61    inference(cnf_transformation,[],[f27])).
% 1.81/0.61  fof(f27,plain,(
% 1.81/0.61    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) & (k4_xboole_0(X0,X1) = X0 | ~r1_xboole_0(X0,X1)))),
% 1.81/0.61    inference(nnf_transformation,[],[f9])).
% 1.81/0.61  fof(f9,axiom,(
% 1.81/0.61    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k4_xboole_0(X0,X1) = X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).
% 1.81/0.61  fof(f2526,plain,(
% 1.81/0.61    r1_xboole_0(sK0,sK1) | ~spl5_56),
% 1.81/0.61    inference(avatar_component_clause,[],[f2524])).
% 1.81/0.61  fof(f2535,plain,(
% 1.81/0.61    spl5_57 | ~spl5_55),
% 1.81/0.61    inference(avatar_split_clause,[],[f2521,f2516,f2532])).
% 1.81/0.61  fof(f2532,plain,(
% 1.81/0.61    spl5_57 <=> sK1 = k4_xboole_0(sK1,sK0)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_57])])).
% 1.81/0.61  fof(f2521,plain,(
% 1.81/0.61    sK1 = k4_xboole_0(sK1,sK0) | ~spl5_55),
% 1.81/0.61    inference(resolution,[],[f2518,f42])).
% 1.81/0.61  fof(f2527,plain,(
% 1.81/0.61    spl5_56 | ~spl5_55),
% 1.81/0.61    inference(avatar_split_clause,[],[f2522,f2516,f2524])).
% 1.81/0.61  fof(f2522,plain,(
% 1.81/0.61    r1_xboole_0(sK0,sK1) | ~spl5_55),
% 1.81/0.61    inference(resolution,[],[f2518,f41])).
% 1.81/0.61  fof(f2519,plain,(
% 1.81/0.61    spl5_55 | ~spl5_54),
% 1.81/0.61    inference(avatar_split_clause,[],[f2490,f2392,f2516])).
% 1.81/0.61  fof(f2392,plain,(
% 1.81/0.61    spl5_54 <=> sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 1.81/0.61  fof(f2490,plain,(
% 1.81/0.61    r1_xboole_0(sK1,sK0) | ~spl5_54),
% 1.81/0.61    inference(resolution,[],[f2398,f73])).
% 1.81/0.61  fof(f73,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.81/0.61    inference(resolution,[],[f41,f34])).
% 1.81/0.61  fof(f34,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f8])).
% 1.81/0.61  fof(f8,axiom,(
% 1.81/0.61    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 1.81/0.61  fof(f2398,plain,(
% 1.81/0.61    ( ! [X2] : (~r1_xboole_0(X2,k4_xboole_0(sK0,sK1)) | r1_xboole_0(X2,sK0)) ) | ~spl5_54),
% 1.81/0.61    inference(superposition,[],[f136,f2394])).
% 1.81/0.61  fof(f2394,plain,(
% 1.81/0.61    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | ~spl5_54),
% 1.81/0.61    inference(avatar_component_clause,[],[f2392])).
% 1.81/0.61  fof(f136,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X2,k3_xboole_0(X1,X0)) | ~r1_xboole_0(X2,X0)) )),
% 1.81/0.61    inference(superposition,[],[f51,f35])).
% 1.81/0.61  fof(f35,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f1])).
% 1.81/0.61  fof(f1,axiom,(
% 1.81/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0)),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).
% 1.81/0.61  fof(f51,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k3_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f22])).
% 1.81/0.61  fof(f22,plain,(
% 1.81/0.61    ! [X0,X1,X2] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.81/0.61    inference(ennf_transformation,[],[f7])).
% 1.81/0.61  fof(f7,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : ~(r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k3_xboole_0(X1,X2)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).
% 1.81/0.61  fof(f2395,plain,(
% 1.81/0.61    spl5_54 | ~spl5_2 | ~spl5_44),
% 1.81/0.61    inference(avatar_split_clause,[],[f2364,f1035,f58,f2392])).
% 1.81/0.61  fof(f58,plain,(
% 1.81/0.61    spl5_2 <=> r1_xboole_0(sK2,sK1)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.81/0.61  fof(f1035,plain,(
% 1.81/0.61    spl5_44 <=> r1_tarski(k3_xboole_0(sK0,sK1),sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 1.81/0.61  fof(f2364,plain,(
% 1.81/0.61    sK0 = k3_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | (~spl5_2 | ~spl5_44)),
% 1.81/0.61    inference(superposition,[],[f2269,f172])).
% 1.81/0.61  fof(f172,plain,(
% 1.81/0.61    ( ! [X2,X3] : (k3_xboole_0(X2,k4_xboole_0(X2,X3)) = k4_xboole_0(X2,k3_xboole_0(X2,X3))) )),
% 1.81/0.61    inference(superposition,[],[f37,f37])).
% 1.81/0.61  fof(f37,plain,(
% 1.81/0.61    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.81/0.61    inference(cnf_transformation,[],[f5])).
% 1.81/0.61  fof(f5,axiom,(
% 1.81/0.61    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.81/0.61  fof(f2269,plain,(
% 1.81/0.61    ( ! [X4] : (k4_xboole_0(X4,k3_xboole_0(sK0,sK1)) = X4) ) | (~spl5_2 | ~spl5_44)),
% 1.81/0.61    inference(resolution,[],[f2251,f42])).
% 1.81/0.61  fof(f2251,plain,(
% 1.81/0.61    ( ! [X4] : (r1_xboole_0(X4,k3_xboole_0(sK0,sK1))) ) | (~spl5_2 | ~spl5_44)),
% 1.81/0.61    inference(resolution,[],[f2211,f41])).
% 1.81/0.61  fof(f2211,plain,(
% 1.81/0.61    ( ! [X18] : (r1_xboole_0(k3_xboole_0(sK0,sK1),X18)) ) | (~spl5_2 | ~spl5_44)),
% 1.81/0.61    inference(resolution,[],[f2200,f1545])).
% 1.81/0.61  fof(f1545,plain,(
% 1.81/0.61    ( ! [X3] : (r1_xboole_0(k3_xboole_0(X3,sK1),k3_xboole_0(sK0,sK1))) ) | (~spl5_2 | ~spl5_44)),
% 1.81/0.61    inference(resolution,[],[f1453,f41])).
% 1.81/0.61  fof(f1453,plain,(
% 1.81/0.61    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(X0,sK1))) ) | (~spl5_2 | ~spl5_44)),
% 1.81/0.61    inference(resolution,[],[f1435,f1037])).
% 1.81/0.61  fof(f1037,plain,(
% 1.81/0.61    r1_tarski(k3_xboole_0(sK0,sK1),sK2) | ~spl5_44),
% 1.81/0.61    inference(avatar_component_clause,[],[f1035])).
% 1.81/0.61  fof(f1435,plain,(
% 1.81/0.61    ( ! [X4,X5] : (~r1_tarski(X5,sK2) | r1_xboole_0(X5,k3_xboole_0(X4,sK1))) ) | ~spl5_2),
% 1.81/0.61    inference(superposition,[],[f50,f1343])).
% 1.81/0.61  fof(f1343,plain,(
% 1.81/0.61    ( ! [X0] : (sK2 = k4_xboole_0(sK2,k3_xboole_0(X0,sK1))) ) | ~spl5_2),
% 1.81/0.61    inference(superposition,[],[f1281,f35])).
% 1.81/0.61  fof(f1281,plain,(
% 1.81/0.61    ( ! [X155] : (sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,X155))) ) | ~spl5_2),
% 1.81/0.61    inference(resolution,[],[f134,f60])).
% 1.81/0.61  fof(f60,plain,(
% 1.81/0.61    r1_xboole_0(sK2,sK1) | ~spl5_2),
% 1.81/0.61    inference(avatar_component_clause,[],[f58])).
% 1.81/0.61  fof(f134,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | k4_xboole_0(X0,k3_xboole_0(X1,X2)) = X0) )),
% 1.81/0.61    inference(resolution,[],[f51,f42])).
% 1.81/0.61  fof(f50,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f21])).
% 1.81/0.61  fof(f21,plain,(
% 1.81/0.61    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) | ~r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 1.81/0.61    inference(ennf_transformation,[],[f4])).
% 1.81/0.61  fof(f4,axiom,(
% 1.81/0.61    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) => (r1_xboole_0(X0,X2) & r1_tarski(X0,X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_xboole_1)).
% 1.81/0.61  fof(f2200,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1)) )),
% 1.81/0.61    inference(duplicate_literal_removal,[],[f2196])).
% 1.81/0.61  fof(f2196,plain,(
% 1.81/0.61    ( ! [X0,X1] : (~r1_xboole_0(X0,X0) | r1_xboole_0(X0,X1) | r1_xboole_0(X0,X1)) )),
% 1.81/0.61    inference(resolution,[],[f198,f38])).
% 1.81/0.61  fof(f38,plain,(
% 1.81/0.61    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f26])).
% 1.81/0.61  fof(f26,plain,(
% 1.81/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 1.81/0.61    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f18,f25])).
% 1.81/0.61  fof(f25,plain,(
% 1.81/0.61    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 1.81/0.61    introduced(choice_axiom,[])).
% 1.81/0.61  fof(f18,plain,(
% 1.81/0.61    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 1.81/0.61    inference(ennf_transformation,[],[f15])).
% 1.81/0.61  fof(f15,plain,(
% 1.81/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.81/0.61    inference(rectify,[],[f3])).
% 1.81/0.61  fof(f3,axiom,(
% 1.81/0.61    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 1.81/0.61    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).
% 1.81/0.61  fof(f198,plain,(
% 1.81/0.61    ( ! [X2,X3,X1] : (~r2_hidden(sK4(X1,X2),X3) | ~r1_xboole_0(X1,X3) | r1_xboole_0(X1,X2)) )),
% 1.81/0.61    inference(resolution,[],[f40,f38])).
% 1.81/0.61  fof(f40,plain,(
% 1.81/0.61    ( ! [X2,X0,X1] : (~r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~r1_xboole_0(X0,X1)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f26])).
% 1.81/0.61  fof(f2363,plain,(
% 1.81/0.61    ~spl5_53 | spl5_50),
% 1.81/0.61    inference(avatar_split_clause,[],[f2353,f2344,f2360])).
% 1.81/0.61  fof(f2360,plain,(
% 1.81/0.61    spl5_53 <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 1.81/0.62  fof(f2344,plain,(
% 1.81/0.62    spl5_50 <=> r1_xboole_0(k1_tarski(sK3),sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 1.81/0.62  fof(f2353,plain,(
% 1.81/0.62    k1_tarski(sK3) != k4_xboole_0(k1_tarski(sK3),sK2) | spl5_50),
% 1.81/0.62    inference(resolution,[],[f2346,f43])).
% 1.81/0.62  fof(f43,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k4_xboole_0(X0,X1) != X0) )),
% 1.81/0.62    inference(cnf_transformation,[],[f27])).
% 1.81/0.62  fof(f2346,plain,(
% 1.81/0.62    ~r1_xboole_0(k1_tarski(sK3),sK2) | spl5_50),
% 1.81/0.62    inference(avatar_component_clause,[],[f2344])).
% 1.81/0.62  fof(f2358,plain,(
% 1.81/0.62    ~spl5_52 | spl5_50),
% 1.81/0.62    inference(avatar_split_clause,[],[f2352,f2344,f2355])).
% 1.81/0.62  fof(f2355,plain,(
% 1.81/0.62    spl5_52 <=> sK2 = k4_xboole_0(sK2,k1_tarski(sK3))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 1.81/0.62  fof(f2352,plain,(
% 1.81/0.62    sK2 != k4_xboole_0(sK2,k1_tarski(sK3)) | spl5_50),
% 1.81/0.62    inference(resolution,[],[f2346,f106])).
% 1.81/0.62  fof(f106,plain,(
% 1.81/0.62    ( ! [X2,X3] : (r1_xboole_0(X3,X2) | k4_xboole_0(X2,X3) != X2) )),
% 1.81/0.62    inference(resolution,[],[f43,f41])).
% 1.81/0.62  fof(f2350,plain,(
% 1.81/0.62    ~spl5_50 | spl5_51 | ~spl5_42),
% 1.81/0.62    inference(avatar_split_clause,[],[f2209,f997,f2348,f2344])).
% 1.81/0.62  fof(f2348,plain,(
% 1.81/0.62    spl5_51 <=> ! [X16] : r1_xboole_0(k1_tarski(sK3),X16)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 1.81/0.62  fof(f997,plain,(
% 1.81/0.62    spl5_42 <=> k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 1.81/0.62  fof(f2209,plain,(
% 1.81/0.62    ( ! [X16] : (r1_xboole_0(k1_tarski(sK3),X16) | ~r1_xboole_0(k1_tarski(sK3),sK2)) ) | ~spl5_42),
% 1.81/0.62    inference(resolution,[],[f2200,f1009])).
% 1.81/0.62  fof(f1009,plain,(
% 1.81/0.62    ( ! [X2] : (r1_xboole_0(X2,k1_tarski(sK3)) | ~r1_xboole_0(X2,sK2)) ) | ~spl5_42),
% 1.81/0.62    inference(superposition,[],[f136,f999])).
% 1.81/0.62  fof(f999,plain,(
% 1.81/0.62    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2) | ~spl5_42),
% 1.81/0.62    inference(avatar_component_clause,[],[f997])).
% 1.81/0.62  fof(f1179,plain,(
% 1.81/0.62    spl5_49 | ~spl5_47),
% 1.81/0.62    inference(avatar_split_clause,[],[f1169,f1162,f1176])).
% 1.81/0.62  fof(f1176,plain,(
% 1.81/0.62    spl5_49 <=> r1_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 1.81/0.62  fof(f1162,plain,(
% 1.81/0.62    spl5_47 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK0))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 1.81/0.62  fof(f1169,plain,(
% 1.81/0.62    r1_xboole_0(k4_xboole_0(sK1,sK0),k3_xboole_0(sK1,sK2)) | ~spl5_47),
% 1.81/0.62    inference(resolution,[],[f1164,f41])).
% 1.81/0.62  fof(f1164,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK0)) | ~spl5_47),
% 1.81/0.62    inference(avatar_component_clause,[],[f1162])).
% 1.81/0.62  fof(f1174,plain,(
% 1.81/0.62    spl5_48 | ~spl5_46),
% 1.81/0.62    inference(avatar_split_clause,[],[f1167,f1157,f1171])).
% 1.81/0.62  fof(f1171,plain,(
% 1.81/0.62    spl5_48 <=> r1_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 1.81/0.62  fof(f1157,plain,(
% 1.81/0.62    spl5_46 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK0))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_46])])).
% 1.81/0.62  fof(f1167,plain,(
% 1.81/0.62    r1_xboole_0(k4_xboole_0(sK0,sK0),k3_xboole_0(sK1,sK2)) | ~spl5_46),
% 1.81/0.62    inference(resolution,[],[f1159,f41])).
% 1.81/0.62  fof(f1159,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK0)) | ~spl5_46),
% 1.81/0.62    inference(avatar_component_clause,[],[f1157])).
% 1.81/0.62  fof(f1165,plain,(
% 1.81/0.62    spl5_47 | ~spl5_45),
% 1.81/0.62    inference(avatar_split_clause,[],[f1148,f1110,f1162])).
% 1.81/0.62  fof(f1110,plain,(
% 1.81/0.62    spl5_45 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 1.81/0.62  fof(f1148,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK1,sK0)) | ~spl5_45),
% 1.81/0.62    inference(resolution,[],[f1119,f312])).
% 1.81/0.62  fof(f312,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),k3_xboole_0(X1,X0))) )),
% 1.81/0.62    inference(superposition,[],[f178,f35])).
% 1.81/0.62  fof(f178,plain,(
% 1.81/0.62    ( ! [X10,X9] : (r1_xboole_0(k4_xboole_0(X9,X10),k3_xboole_0(X9,X10))) )),
% 1.81/0.62    inference(superposition,[],[f73,f37])).
% 1.81/0.62  fof(f1119,plain,(
% 1.81/0.62    ( ! [X3] : (~r1_xboole_0(X3,k3_xboole_0(sK0,sK1)) | r1_xboole_0(k3_xboole_0(sK1,sK2),X3)) ) | ~spl5_45),
% 1.81/0.62    inference(superposition,[],[f152,f1112])).
% 1.81/0.62  fof(f1112,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_45),
% 1.81/0.62    inference(avatar_component_clause,[],[f1110])).
% 1.81/0.62  fof(f152,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (r1_xboole_0(k3_xboole_0(X1,X0),X2) | ~r1_xboole_0(X2,X0)) )),
% 1.81/0.62    inference(superposition,[],[f135,f35])).
% 1.81/0.62  fof(f135,plain,(
% 1.81/0.62    ( ! [X4,X5,X3] : (r1_xboole_0(k3_xboole_0(X4,X5),X3) | ~r1_xboole_0(X3,X4)) )),
% 1.81/0.62    inference(resolution,[],[f51,f41])).
% 1.81/0.62  fof(f1160,plain,(
% 1.81/0.62    spl5_46 | ~spl5_45),
% 1.81/0.62    inference(avatar_split_clause,[],[f1146,f1110,f1157])).
% 1.81/0.62  fof(f1146,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),k4_xboole_0(sK0,sK0)) | ~spl5_45),
% 1.81/0.62    inference(resolution,[],[f1119,f747])).
% 1.81/0.62  fof(f747,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X1,X1),k3_xboole_0(X1,X0))) )),
% 1.81/0.62    inference(superposition,[],[f683,f35])).
% 1.81/0.62  fof(f683,plain,(
% 1.81/0.62    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(X3,X3),k3_xboole_0(X2,X3))) )),
% 1.81/0.62    inference(forward_demodulation,[],[f669,f654])).
% 1.81/0.62  fof(f654,plain,(
% 1.81/0.62    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k4_xboole_0(X3,X3)) )),
% 1.81/0.62    inference(forward_demodulation,[],[f653,f171])).
% 1.81/0.62  fof(f171,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k3_xboole_0(X0,k4_xboole_0(X1,X0)) = k4_xboole_0(X0,X0)) )),
% 1.81/0.62    inference(superposition,[],[f37,f81])).
% 1.81/0.62  fof(f81,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X1,X0)) = X0) )),
% 1.81/0.62    inference(resolution,[],[f42,f73])).
% 1.81/0.62  fof(f653,plain,(
% 1.81/0.62    ( ! [X2,X3] : (k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)) = k3_xboole_0(X3,k4_xboole_0(X2,X3))) )),
% 1.81/0.62    inference(forward_demodulation,[],[f636,f35])).
% 1.81/0.62  fof(f636,plain,(
% 1.81/0.62    ( ! [X2,X3] : (k3_xboole_0(k4_xboole_0(X2,X3),X3) = k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3))) )),
% 1.81/0.62    inference(superposition,[],[f37,f82])).
% 1.81/0.62  fof(f82,plain,(
% 1.81/0.62    ( ! [X2,X3] : (k4_xboole_0(X2,X3) = k4_xboole_0(k4_xboole_0(X2,X3),X3)) )),
% 1.81/0.62    inference(resolution,[],[f42,f34])).
% 1.81/0.62  fof(f669,plain,(
% 1.81/0.62    ( ! [X2,X3] : (r1_xboole_0(k4_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,X3)),k3_xboole_0(X2,X3))) )),
% 1.81/0.62    inference(superposition,[],[f658,f37])).
% 1.81/0.62  fof(f658,plain,(
% 1.81/0.62    ( ! [X17,X16] : (r1_xboole_0(k4_xboole_0(X17,X17),k4_xboole_0(X16,X17))) )),
% 1.81/0.62    inference(forward_demodulation,[],[f657,f171])).
% 1.81/0.62  fof(f657,plain,(
% 1.81/0.62    ( ! [X17,X16] : (r1_xboole_0(k3_xboole_0(X17,k4_xboole_0(X16,X17)),k4_xboole_0(X16,X17))) )),
% 1.81/0.62    inference(forward_demodulation,[],[f642,f35])).
% 1.81/0.62  fof(f642,plain,(
% 1.81/0.62    ( ! [X17,X16] : (r1_xboole_0(k3_xboole_0(k4_xboole_0(X16,X17),X17),k4_xboole_0(X16,X17))) )),
% 1.81/0.62    inference(superposition,[],[f179,f82])).
% 1.81/0.62  fof(f179,plain,(
% 1.81/0.62    ( ! [X12,X11] : (r1_xboole_0(k3_xboole_0(X11,X12),k4_xboole_0(X11,X12))) )),
% 1.81/0.62    inference(superposition,[],[f34,f37])).
% 1.81/0.62  fof(f1113,plain,(
% 1.81/0.62    spl5_45 | ~spl5_16 | ~spl5_33),
% 1.81/0.62    inference(avatar_split_clause,[],[f574,f560,f234,f1110])).
% 1.81/0.62  fof(f234,plain,(
% 1.81/0.62    spl5_16 <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.81/0.62  fof(f560,plain,(
% 1.81/0.62    spl5_33 <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.81/0.62  fof(f574,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | (~spl5_16 | ~spl5_33)),
% 1.81/0.62    inference(forward_demodulation,[],[f565,f236])).
% 1.81/0.62  fof(f236,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | ~spl5_16),
% 1.81/0.62    inference(avatar_component_clause,[],[f234])).
% 1.81/0.62  fof(f565,plain,(
% 1.81/0.62    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_33),
% 1.81/0.62    inference(superposition,[],[f37,f562])).
% 1.81/0.62  fof(f562,plain,(
% 1.81/0.62    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_33),
% 1.81/0.62    inference(avatar_component_clause,[],[f560])).
% 1.81/0.62  fof(f1038,plain,(
% 1.81/0.62    spl5_44 | ~spl5_4 | ~spl5_42),
% 1.81/0.62    inference(avatar_split_clause,[],[f1033,f997,f68,f1035])).
% 1.81/0.62  fof(f68,plain,(
% 1.81/0.62    spl5_4 <=> r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.81/0.62  fof(f1033,plain,(
% 1.81/0.62    r1_tarski(k3_xboole_0(sK0,sK1),sK2) | (~spl5_4 | ~spl5_42)),
% 1.81/0.62    inference(resolution,[],[f1016,f70])).
% 1.81/0.62  fof(f70,plain,(
% 1.81/0.62    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)) | ~spl5_4),
% 1.81/0.62    inference(avatar_component_clause,[],[f68])).
% 1.81/0.62  fof(f1016,plain,(
% 1.81/0.62    ( ! [X5] : (~r1_tarski(X5,k1_tarski(sK3)) | r1_tarski(X5,sK2)) ) | ~spl5_42),
% 1.81/0.62    inference(superposition,[],[f419,f999])).
% 1.81/0.62  fof(f419,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X2,k3_xboole_0(X1,X0)) | r1_tarski(X2,X0)) )),
% 1.81/0.62    inference(superposition,[],[f176,f35])).
% 1.81/0.62  fof(f176,plain,(
% 1.81/0.62    ( ! [X6,X4,X5] : (~r1_tarski(X6,k3_xboole_0(X4,X5)) | r1_tarski(X6,X4)) )),
% 1.81/0.62    inference(superposition,[],[f49,f37])).
% 1.81/0.62  fof(f49,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~r1_tarski(X0,k4_xboole_0(X1,X2)) | r1_tarski(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f21])).
% 1.81/0.62  fof(f1025,plain,(
% 1.81/0.62    spl5_43 | ~spl5_42),
% 1.81/0.62    inference(avatar_split_clause,[],[f1001,f997,f1022])).
% 1.81/0.62  fof(f1022,plain,(
% 1.81/0.62    spl5_43 <=> k1_tarski(sK3) = k3_xboole_0(sK2,k1_tarski(sK3))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 1.81/0.62  fof(f1001,plain,(
% 1.81/0.62    k1_tarski(sK3) = k3_xboole_0(sK2,k1_tarski(sK3)) | ~spl5_42),
% 1.81/0.62    inference(superposition,[],[f999,f35])).
% 1.81/0.62  fof(f1000,plain,(
% 1.81/0.62    spl5_42 | ~spl5_1),
% 1.81/0.62    inference(avatar_split_clause,[],[f972,f53,f997])).
% 1.81/0.62  fof(f53,plain,(
% 1.81/0.62    spl5_1 <=> r2_hidden(sK3,sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.81/0.62  fof(f972,plain,(
% 1.81/0.62    k1_tarski(sK3) = k3_xboole_0(k1_tarski(sK3),sK2) | ~spl5_1),
% 1.81/0.62    inference(superposition,[],[f914,f37])).
% 1.81/0.62  fof(f914,plain,(
% 1.81/0.62    ( ! [X11] : (k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),k4_xboole_0(X11,sK2))) ) | ~spl5_1),
% 1.81/0.62    inference(superposition,[],[f81,f463])).
% 1.81/0.62  fof(f463,plain,(
% 1.81/0.62    ( ! [X0] : (k4_xboole_0(X0,sK2) = k4_xboole_0(k4_xboole_0(X0,sK2),k1_tarski(sK3))) ) | ~spl5_1),
% 1.81/0.62    inference(resolution,[],[f460,f73])).
% 1.81/0.62  fof(f460,plain,(
% 1.81/0.62    ( ! [X3] : (~r1_xboole_0(sK2,X3) | k4_xboole_0(X3,k1_tarski(sK3)) = X3) ) | ~spl5_1),
% 1.81/0.62    inference(resolution,[],[f45,f197])).
% 1.81/0.62  fof(f197,plain,(
% 1.81/0.62    ( ! [X0] : (~r2_hidden(sK3,X0) | ~r1_xboole_0(sK2,X0)) ) | ~spl5_1),
% 1.81/0.62    inference(resolution,[],[f40,f55])).
% 1.81/0.62  fof(f55,plain,(
% 1.81/0.62    r2_hidden(sK3,sK2) | ~spl5_1),
% 1.81/0.62    inference(avatar_component_clause,[],[f53])).
% 1.81/0.62  fof(f45,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) = X0) )),
% 1.81/0.62    inference(cnf_transformation,[],[f28])).
% 1.81/0.62  fof(f28,plain,(
% 1.81/0.62    ! [X0,X1] : ((k4_xboole_0(X0,k1_tarski(X1)) = X0 | r2_hidden(X1,X0)) & (~r2_hidden(X1,X0) | k4_xboole_0(X0,k1_tarski(X1)) != X0))),
% 1.81/0.62    inference(nnf_transformation,[],[f12])).
% 1.81/0.62  fof(f12,axiom,(
% 1.81/0.62    ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) = X0 <=> ~r2_hidden(X1,X0))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).
% 1.81/0.62  fof(f950,plain,(
% 1.81/0.62    ~spl5_41 | ~spl5_1 | ~spl5_21),
% 1.81/0.62    inference(avatar_split_clause,[],[f930,f368,f53,f947])).
% 1.81/0.62  fof(f947,plain,(
% 1.81/0.62    spl5_41 <=> r2_hidden(sK3,k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_41])])).
% 1.81/0.62  fof(f368,plain,(
% 1.81/0.62    spl5_21 <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 1.81/0.62  fof(f930,plain,(
% 1.81/0.62    ~r2_hidden(sK3,k3_xboole_0(sK1,sK2)) | (~spl5_1 | ~spl5_21)),
% 1.81/0.62    inference(superposition,[],[f907,f370])).
% 1.81/0.62  fof(f370,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK2) | ~spl5_21),
% 1.81/0.62    inference(avatar_component_clause,[],[f368])).
% 1.81/0.62  fof(f907,plain,(
% 1.81/0.62    ( ! [X2] : (~r2_hidden(sK3,k4_xboole_0(X2,sK2))) ) | ~spl5_1),
% 1.81/0.62    inference(superposition,[],[f652,f463])).
% 1.81/0.62  fof(f652,plain,(
% 1.81/0.62    ( ! [X37,X36] : (~r2_hidden(X37,k4_xboole_0(X36,k1_tarski(X37)))) )),
% 1.81/0.62    inference(trivial_inequality_removal,[],[f651])).
% 1.81/0.62  fof(f651,plain,(
% 1.81/0.62    ( ! [X37,X36] : (k4_xboole_0(X36,k1_tarski(X37)) != k4_xboole_0(X36,k1_tarski(X37)) | ~r2_hidden(X37,k4_xboole_0(X36,k1_tarski(X37)))) )),
% 1.81/0.62    inference(superposition,[],[f44,f82])).
% 1.81/0.62  fof(f44,plain,(
% 1.81/0.62    ( ! [X0,X1] : (k4_xboole_0(X0,k1_tarski(X1)) != X0 | ~r2_hidden(X1,X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f28])).
% 1.81/0.62  fof(f899,plain,(
% 1.81/0.62    spl5_40 | ~spl5_33),
% 1.81/0.62    inference(avatar_split_clause,[],[f726,f560,f896])).
% 1.81/0.62  fof(f896,plain,(
% 1.81/0.62    spl5_40 <=> r1_xboole_0(sK1,k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 1.81/0.62  fof(f726,plain,(
% 1.81/0.62    r1_xboole_0(sK1,k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1))) | ~spl5_33),
% 1.81/0.62    inference(superposition,[],[f656,f562])).
% 1.81/0.62  fof(f656,plain,(
% 1.81/0.62    ( ! [X14,X15] : (r1_xboole_0(k4_xboole_0(X14,X15),k4_xboole_0(X15,X15))) )),
% 1.81/0.62    inference(forward_demodulation,[],[f655,f171])).
% 1.81/0.62  fof(f655,plain,(
% 1.81/0.62    ( ! [X14,X15] : (r1_xboole_0(k4_xboole_0(X14,X15),k3_xboole_0(X15,k4_xboole_0(X14,X15)))) )),
% 1.81/0.62    inference(forward_demodulation,[],[f641,f35])).
% 1.81/0.62  fof(f641,plain,(
% 1.81/0.62    ( ! [X14,X15] : (r1_xboole_0(k4_xboole_0(X14,X15),k3_xboole_0(k4_xboole_0(X14,X15),X15))) )),
% 1.81/0.62    inference(superposition,[],[f178,f82])).
% 1.81/0.62  fof(f893,plain,(
% 1.81/0.62    spl5_39 | ~spl5_33),
% 1.81/0.62    inference(avatar_split_clause,[],[f675,f560,f890])).
% 1.81/0.62  fof(f890,plain,(
% 1.81/0.62    spl5_39 <=> r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 1.81/0.62  fof(f675,plain,(
% 1.81/0.62    r1_xboole_0(k4_xboole_0(k3_xboole_0(sK0,sK1),k3_xboole_0(sK0,sK1)),sK1) | ~spl5_33),
% 1.81/0.62    inference(superposition,[],[f658,f562])).
% 1.81/0.62  fof(f840,plain,(
% 1.81/0.62    spl5_38 | ~spl5_34),
% 1.81/0.62    inference(avatar_split_clause,[],[f586,f582,f837])).
% 1.81/0.62  fof(f837,plain,(
% 1.81/0.62    spl5_38 <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 1.81/0.62  fof(f582,plain,(
% 1.81/0.62    spl5_34 <=> r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 1.81/0.62  fof(f586,plain,(
% 1.81/0.62    k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2)) | ~spl5_34),
% 1.81/0.62    inference(resolution,[],[f584,f42])).
% 1.81/0.62  fof(f584,plain,(
% 1.81/0.62    r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2)) | ~spl5_34),
% 1.81/0.62    inference(avatar_component_clause,[],[f582])).
% 1.81/0.62  fof(f835,plain,(
% 1.81/0.62    spl5_37 | ~spl5_30),
% 1.81/0.62    inference(avatar_split_clause,[],[f526,f522,f832])).
% 1.81/0.62  fof(f832,plain,(
% 1.81/0.62    spl5_37 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 1.81/0.62  fof(f522,plain,(
% 1.81/0.62    spl5_30 <=> r1_xboole_0(k3_xboole_0(sK0,sK1),sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 1.81/0.62  fof(f526,plain,(
% 1.81/0.62    k3_xboole_0(sK0,sK1) = k4_xboole_0(k3_xboole_0(sK0,sK1),sK1) | ~spl5_30),
% 1.81/0.62    inference(resolution,[],[f524,f42])).
% 1.81/0.62  fof(f524,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | ~spl5_30),
% 1.81/0.62    inference(avatar_component_clause,[],[f522])).
% 1.81/0.62  fof(f599,plain,(
% 1.81/0.62    spl5_36 | ~spl5_16 | ~spl5_26),
% 1.81/0.62    inference(avatar_split_clause,[],[f489,f471,f234,f596])).
% 1.81/0.62  fof(f596,plain,(
% 1.81/0.62    spl5_36 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 1.81/0.62  fof(f471,plain,(
% 1.81/0.62    spl5_26 <=> sK1 = k4_xboole_0(sK1,k1_tarski(sK3))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 1.81/0.62  fof(f489,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k1_tarski(sK3)) | (~spl5_16 | ~spl5_26)),
% 1.81/0.62    inference(forward_demodulation,[],[f479,f236])).
% 1.81/0.62  fof(f479,plain,(
% 1.81/0.62    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_26),
% 1.81/0.62    inference(superposition,[],[f37,f473])).
% 1.81/0.62  fof(f473,plain,(
% 1.81/0.62    sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_26),
% 1.81/0.62    inference(avatar_component_clause,[],[f471])).
% 1.81/0.62  fof(f592,plain,(
% 1.81/0.62    spl5_35 | ~spl5_16 | ~spl5_26 | ~spl5_32),
% 1.81/0.62    inference(avatar_split_clause,[],[f555,f536,f471,f234,f589])).
% 1.81/0.62  fof(f589,plain,(
% 1.81/0.62    spl5_35 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK3))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_35])])).
% 1.81/0.62  fof(f536,plain,(
% 1.81/0.62    spl5_32 <=> k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.81/0.62  fof(f555,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),k1_tarski(sK3)) | (~spl5_16 | ~spl5_26 | ~spl5_32)),
% 1.81/0.62    inference(forward_demodulation,[],[f554,f489])).
% 1.81/0.62  fof(f554,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,k1_tarski(sK3)),k1_tarski(sK3)) | ~spl5_32),
% 1.81/0.62    inference(forward_demodulation,[],[f547,f35])).
% 1.81/0.62  fof(f547,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(k1_tarski(sK3),sK1),k1_tarski(sK3)) | ~spl5_32),
% 1.81/0.62    inference(superposition,[],[f179,f538])).
% 1.81/0.62  fof(f538,plain,(
% 1.81/0.62    k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) | ~spl5_32),
% 1.81/0.62    inference(avatar_component_clause,[],[f536])).
% 1.81/0.62  fof(f585,plain,(
% 1.81/0.62    spl5_34 | ~spl5_16 | ~spl5_26 | ~spl5_32),
% 1.81/0.62    inference(avatar_split_clause,[],[f553,f536,f471,f234,f582])).
% 1.81/0.62  fof(f553,plain,(
% 1.81/0.62    r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,sK2)) | (~spl5_16 | ~spl5_26 | ~spl5_32)),
% 1.81/0.62    inference(forward_demodulation,[],[f552,f489])).
% 1.81/0.62  fof(f552,plain,(
% 1.81/0.62    r1_xboole_0(k1_tarski(sK3),k3_xboole_0(sK1,k1_tarski(sK3))) | ~spl5_32),
% 1.81/0.62    inference(forward_demodulation,[],[f546,f35])).
% 1.81/0.62  fof(f546,plain,(
% 1.81/0.62    r1_xboole_0(k1_tarski(sK3),k3_xboole_0(k1_tarski(sK3),sK1)) | ~spl5_32),
% 1.81/0.62    inference(superposition,[],[f178,f538])).
% 1.81/0.62  fof(f563,plain,(
% 1.81/0.62    spl5_33 | ~spl5_31),
% 1.81/0.62    inference(avatar_split_clause,[],[f533,f529,f560])).
% 1.81/0.62  fof(f529,plain,(
% 1.81/0.62    spl5_31 <=> r1_xboole_0(sK1,k3_xboole_0(sK0,sK1))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 1.81/0.62  fof(f533,plain,(
% 1.81/0.62    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_31),
% 1.81/0.62    inference(resolution,[],[f531,f42])).
% 1.81/0.62  fof(f531,plain,(
% 1.81/0.62    r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | ~spl5_31),
% 1.81/0.62    inference(avatar_component_clause,[],[f529])).
% 1.81/0.62  fof(f539,plain,(
% 1.81/0.62    spl5_32 | ~spl5_26),
% 1.81/0.62    inference(avatar_split_clause,[],[f483,f471,f536])).
% 1.81/0.62  fof(f483,plain,(
% 1.81/0.62    k1_tarski(sK3) = k4_xboole_0(k1_tarski(sK3),sK1) | ~spl5_26),
% 1.81/0.62    inference(superposition,[],[f81,f473])).
% 1.81/0.62  fof(f532,plain,(
% 1.81/0.62    spl5_31 | ~spl5_4 | ~spl5_26),
% 1.81/0.62    inference(avatar_split_clause,[],[f475,f471,f68,f529])).
% 1.81/0.62  fof(f475,plain,(
% 1.81/0.62    r1_xboole_0(sK1,k3_xboole_0(sK0,sK1)) | (~spl5_4 | ~spl5_26)),
% 1.81/0.62    inference(superposition,[],[f166,f473])).
% 1.81/0.62  fof(f166,plain,(
% 1.81/0.62    ( ! [X1] : (r1_xboole_0(k4_xboole_0(X1,k1_tarski(sK3)),k3_xboole_0(sK0,sK1))) ) | ~spl5_4),
% 1.81/0.62    inference(resolution,[],[f164,f41])).
% 1.81/0.62  fof(f164,plain,(
% 1.81/0.62    ( ! [X0] : (r1_xboole_0(k3_xboole_0(sK0,sK1),k4_xboole_0(X0,k1_tarski(sK3)))) ) | ~spl5_4),
% 1.81/0.62    inference(resolution,[],[f133,f70])).
% 1.81/0.62  fof(f133,plain,(
% 1.81/0.62    ( ! [X4,X2,X3] : (~r1_tarski(X4,X2) | r1_xboole_0(X4,k4_xboole_0(X3,X2))) )),
% 1.81/0.62    inference(superposition,[],[f50,f81])).
% 1.81/0.62  fof(f525,plain,(
% 1.81/0.62    spl5_30 | ~spl5_4 | ~spl5_26),
% 1.81/0.62    inference(avatar_split_clause,[],[f476,f471,f68,f522])).
% 1.81/0.62  fof(f476,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK0,sK1),sK1) | (~spl5_4 | ~spl5_26)),
% 1.81/0.62    inference(superposition,[],[f164,f473])).
% 1.81/0.62  fof(f516,plain,(
% 1.81/0.62    spl5_29 | ~spl5_26),
% 1.81/0.62    inference(avatar_split_clause,[],[f482,f471,f513])).
% 1.81/0.62  fof(f513,plain,(
% 1.81/0.62    spl5_29 <=> r1_xboole_0(k1_tarski(sK3),sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 1.81/0.62  fof(f482,plain,(
% 1.81/0.62    r1_xboole_0(k1_tarski(sK3),sK1) | ~spl5_26),
% 1.81/0.62    inference(superposition,[],[f73,f473])).
% 1.81/0.62  fof(f511,plain,(
% 1.81/0.62    spl5_28 | ~spl5_26),
% 1.81/0.62    inference(avatar_split_clause,[],[f478,f471,f508])).
% 1.81/0.62  fof(f508,plain,(
% 1.81/0.62    spl5_28 <=> r1_xboole_0(sK1,k1_tarski(sK3))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 1.81/0.62  fof(f478,plain,(
% 1.81/0.62    r1_xboole_0(sK1,k1_tarski(sK3)) | ~spl5_26),
% 1.81/0.62    inference(superposition,[],[f34,f473])).
% 1.81/0.62  fof(f500,plain,(
% 1.81/0.62    ~spl5_27 | ~spl5_26),
% 1.81/0.62    inference(avatar_split_clause,[],[f488,f471,f497])).
% 1.81/0.62  fof(f497,plain,(
% 1.81/0.62    spl5_27 <=> r2_hidden(sK3,sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.81/0.62  fof(f488,plain,(
% 1.81/0.62    ~r2_hidden(sK3,sK1) | ~spl5_26),
% 1.81/0.62    inference(trivial_inequality_removal,[],[f477])).
% 1.81/0.62  fof(f477,plain,(
% 1.81/0.62    sK1 != sK1 | ~r2_hidden(sK3,sK1) | ~spl5_26),
% 1.81/0.62    inference(superposition,[],[f44,f473])).
% 1.81/0.62  fof(f474,plain,(
% 1.81/0.62    spl5_26 | ~spl5_1 | ~spl5_2),
% 1.81/0.62    inference(avatar_split_clause,[],[f461,f58,f53,f471])).
% 1.81/0.62  fof(f461,plain,(
% 1.81/0.62    sK1 = k4_xboole_0(sK1,k1_tarski(sK3)) | (~spl5_1 | ~spl5_2)),
% 1.81/0.62    inference(resolution,[],[f460,f60])).
% 1.81/0.62  fof(f446,plain,(
% 1.81/0.62    spl5_25 | ~spl5_16 | ~spl5_20),
% 1.81/0.62    inference(avatar_split_clause,[],[f282,f272,f234,f443])).
% 1.81/0.62  fof(f443,plain,(
% 1.81/0.62    spl5_25 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 1.81/0.62  fof(f272,plain,(
% 1.81/0.62    spl5_20 <=> sK1 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.81/0.62  fof(f282,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | (~spl5_16 | ~spl5_20)),
% 1.81/0.62    inference(forward_demodulation,[],[f276,f236])).
% 1.81/0.62  fof(f276,plain,(
% 1.81/0.62    k4_xboole_0(sK1,sK1) = k3_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl5_20),
% 1.81/0.62    inference(superposition,[],[f37,f274])).
% 1.81/0.62  fof(f274,plain,(
% 1.81/0.62    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl5_20),
% 1.81/0.62    inference(avatar_component_clause,[],[f272])).
% 1.81/0.62  fof(f429,plain,(
% 1.81/0.62    spl5_24 | ~spl5_10 | ~spl5_17),
% 1.81/0.62    inference(avatar_split_clause,[],[f270,f239,f186,f426])).
% 1.81/0.62  fof(f426,plain,(
% 1.81/0.62    spl5_24 <=> k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.81/0.62  fof(f186,plain,(
% 1.81/0.62    spl5_10 <=> k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.81/0.62  fof(f239,plain,(
% 1.81/0.62    spl5_17 <=> sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.81/0.62  fof(f270,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | (~spl5_10 | ~spl5_17)),
% 1.81/0.62    inference(forward_demodulation,[],[f264,f188])).
% 1.81/0.62  fof(f188,plain,(
% 1.81/0.62    k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) | ~spl5_10),
% 1.81/0.62    inference(avatar_component_clause,[],[f186])).
% 1.81/0.62  fof(f264,plain,(
% 1.81/0.62    k4_xboole_0(sK2,sK2) = k3_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_17),
% 1.81/0.62    inference(superposition,[],[f37,f241])).
% 1.81/0.62  fof(f241,plain,(
% 1.81/0.62    sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_17),
% 1.81/0.62    inference(avatar_component_clause,[],[f239])).
% 1.81/0.62  fof(f399,plain,(
% 1.81/0.62    spl5_23 | ~spl5_10 | ~spl5_17 | ~spl5_21),
% 1.81/0.62    inference(avatar_split_clause,[],[f385,f368,f239,f186,f396])).
% 1.81/0.62  fof(f396,plain,(
% 1.81/0.62    spl5_23 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 1.81/0.62  fof(f385,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK1,sK2)) | (~spl5_10 | ~spl5_17 | ~spl5_21)),
% 1.81/0.62    inference(forward_demodulation,[],[f384,f270])).
% 1.81/0.62  fof(f384,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(sK2,k3_xboole_0(sK1,sK2))) | ~spl5_21),
% 1.81/0.62    inference(forward_demodulation,[],[f378,f35])).
% 1.81/0.62  fof(f378,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),k3_xboole_0(k3_xboole_0(sK1,sK2),sK2)) | ~spl5_21),
% 1.81/0.62    inference(superposition,[],[f178,f370])).
% 1.81/0.62  fof(f394,plain,(
% 1.81/0.62    spl5_22 | ~spl5_19),
% 1.81/0.62    inference(avatar_split_clause,[],[f262,f256,f391])).
% 1.81/0.62  fof(f391,plain,(
% 1.81/0.62    spl5_22 <=> k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 1.81/0.62  fof(f256,plain,(
% 1.81/0.62    spl5_19 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 1.81/0.62  fof(f262,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK1) | ~spl5_19),
% 1.81/0.62    inference(resolution,[],[f258,f42])).
% 1.81/0.62  fof(f258,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),sK1) | ~spl5_19),
% 1.81/0.62    inference(avatar_component_clause,[],[f256])).
% 1.81/0.62  fof(f371,plain,(
% 1.81/0.62    spl5_21 | ~spl5_12),
% 1.81/0.62    inference(avatar_split_clause,[],[f212,f206,f368])).
% 1.81/0.62  fof(f206,plain,(
% 1.81/0.62    spl5_12 <=> r1_xboole_0(k3_xboole_0(sK1,sK2),sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.81/0.62  fof(f212,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k4_xboole_0(k3_xboole_0(sK1,sK2),sK2) | ~spl5_12),
% 1.81/0.62    inference(resolution,[],[f208,f42])).
% 1.81/0.62  fof(f208,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),sK2) | ~spl5_12),
% 1.81/0.62    inference(avatar_component_clause,[],[f206])).
% 1.81/0.62  fof(f275,plain,(
% 1.81/0.62    spl5_20 | ~spl5_16),
% 1.81/0.62    inference(avatar_split_clause,[],[f249,f234,f272])).
% 1.81/0.62  fof(f249,plain,(
% 1.81/0.62    sK1 = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl5_16),
% 1.81/0.62    inference(forward_demodulation,[],[f243,f173])).
% 1.81/0.62  fof(f173,plain,(
% 1.81/0.62    ( ! [X0] : (k3_xboole_0(X0,X0) = X0) )),
% 1.81/0.62    inference(superposition,[],[f37,f81])).
% 1.81/0.62  fof(f243,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK1) = k4_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl5_16),
% 1.81/0.62    inference(superposition,[],[f37,f236])).
% 1.81/0.62  fof(f259,plain,(
% 1.81/0.62    spl5_19 | ~spl5_16),
% 1.81/0.62    inference(avatar_split_clause,[],[f248,f234,f256])).
% 1.81/0.62  fof(f248,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),sK1) | ~spl5_16),
% 1.81/0.62    inference(superposition,[],[f34,f236])).
% 1.81/0.62  fof(f254,plain,(
% 1.81/0.62    spl5_18 | ~spl5_16),
% 1.81/0.62    inference(avatar_split_clause,[],[f247,f234,f251])).
% 1.81/0.62  fof(f251,plain,(
% 1.81/0.62    spl5_18 <=> r1_xboole_0(sK1,k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.81/0.62  fof(f247,plain,(
% 1.81/0.62    r1_xboole_0(sK1,k3_xboole_0(sK1,sK2)) | ~spl5_16),
% 1.81/0.62    inference(superposition,[],[f73,f236])).
% 1.81/0.62  fof(f242,plain,(
% 1.81/0.62    spl5_17 | ~spl5_10),
% 1.81/0.62    inference(avatar_split_clause,[],[f196,f186,f239])).
% 1.81/0.62  fof(f196,plain,(
% 1.81/0.62    sK2 = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_10),
% 1.81/0.62    inference(forward_demodulation,[],[f190,f173])).
% 1.81/0.62  fof(f190,plain,(
% 1.81/0.62    k3_xboole_0(sK2,sK2) = k4_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_10),
% 1.81/0.62    inference(superposition,[],[f37,f188])).
% 1.81/0.62  fof(f237,plain,(
% 1.81/0.62    spl5_16 | ~spl5_7),
% 1.81/0.62    inference(avatar_split_clause,[],[f170,f93,f234])).
% 1.81/0.62  fof(f93,plain,(
% 1.81/0.62    spl5_7 <=> sK1 = k4_xboole_0(sK1,sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.81/0.62  fof(f170,plain,(
% 1.81/0.62    k3_xboole_0(sK1,sK2) = k4_xboole_0(sK1,sK1) | ~spl5_7),
% 1.81/0.62    inference(superposition,[],[f37,f95])).
% 1.81/0.62  fof(f95,plain,(
% 1.81/0.62    sK1 = k4_xboole_0(sK1,sK2) | ~spl5_7),
% 1.81/0.62    inference(avatar_component_clause,[],[f93])).
% 1.81/0.62  fof(f232,plain,(
% 1.81/0.62    ~spl5_15 | ~spl5_10 | spl5_14),
% 1.81/0.62    inference(avatar_split_clause,[],[f227,f223,f186,f229])).
% 1.81/0.62  fof(f229,plain,(
% 1.81/0.62    spl5_15 <=> sK2 = k3_xboole_0(sK1,sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.81/0.62  fof(f223,plain,(
% 1.81/0.62    spl5_14 <=> sK2 = k4_xboole_0(sK2,sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.81/0.62  fof(f227,plain,(
% 1.81/0.62    sK2 != k3_xboole_0(sK1,sK2) | (~spl5_10 | spl5_14)),
% 1.81/0.62    inference(superposition,[],[f225,f188])).
% 1.81/0.62  fof(f225,plain,(
% 1.81/0.62    sK2 != k4_xboole_0(sK2,sK2) | spl5_14),
% 1.81/0.62    inference(avatar_component_clause,[],[f223])).
% 1.81/0.62  fof(f226,plain,(
% 1.81/0.62    ~spl5_14 | spl5_13),
% 1.81/0.62    inference(avatar_split_clause,[],[f220,f216,f223])).
% 1.81/0.62  fof(f216,plain,(
% 1.81/0.62    spl5_13 <=> r1_xboole_0(sK2,sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.81/0.62  fof(f220,plain,(
% 1.81/0.62    sK2 != k4_xboole_0(sK2,sK2) | spl5_13),
% 1.81/0.62    inference(resolution,[],[f218,f106])).
% 1.81/0.62  fof(f218,plain,(
% 1.81/0.62    ~r1_xboole_0(sK2,sK2) | spl5_13),
% 1.81/0.62    inference(avatar_component_clause,[],[f216])).
% 1.81/0.62  fof(f219,plain,(
% 1.81/0.62    ~spl5_13 | ~spl5_1),
% 1.81/0.62    inference(avatar_split_clause,[],[f214,f53,f216])).
% 1.81/0.62  fof(f214,plain,(
% 1.81/0.62    ~r1_xboole_0(sK2,sK2) | ~spl5_1),
% 1.81/0.62    inference(resolution,[],[f197,f55])).
% 1.81/0.62  fof(f209,plain,(
% 1.81/0.62    spl5_12 | ~spl5_10),
% 1.81/0.62    inference(avatar_split_clause,[],[f195,f186,f206])).
% 1.81/0.62  fof(f195,plain,(
% 1.81/0.62    r1_xboole_0(k3_xboole_0(sK1,sK2),sK2) | ~spl5_10),
% 1.81/0.62    inference(superposition,[],[f34,f188])).
% 1.81/0.62  fof(f204,plain,(
% 1.81/0.62    spl5_11 | ~spl5_10),
% 1.81/0.62    inference(avatar_split_clause,[],[f194,f186,f201])).
% 1.81/0.62  fof(f201,plain,(
% 1.81/0.62    spl5_11 <=> r1_xboole_0(sK2,k3_xboole_0(sK1,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.81/0.62  fof(f194,plain,(
% 1.81/0.62    r1_xboole_0(sK2,k3_xboole_0(sK1,sK2)) | ~spl5_10),
% 1.81/0.62    inference(superposition,[],[f73,f188])).
% 1.81/0.62  fof(f189,plain,(
% 1.81/0.62    spl5_10 | ~spl5_6),
% 1.81/0.62    inference(avatar_split_clause,[],[f180,f86,f186])).
% 1.81/0.62  fof(f86,plain,(
% 1.81/0.62    spl5_6 <=> sK2 = k4_xboole_0(sK2,sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.81/0.62  fof(f180,plain,(
% 1.81/0.62    k4_xboole_0(sK2,sK2) = k3_xboole_0(sK1,sK2) | ~spl5_6),
% 1.81/0.62    inference(forward_demodulation,[],[f169,f35])).
% 1.81/0.62  fof(f169,plain,(
% 1.81/0.62    k3_xboole_0(sK2,sK1) = k4_xboole_0(sK2,sK2) | ~spl5_6),
% 1.81/0.62    inference(superposition,[],[f37,f88])).
% 1.81/0.62  fof(f88,plain,(
% 1.81/0.62    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_6),
% 1.81/0.62    inference(avatar_component_clause,[],[f86])).
% 1.81/0.62  fof(f147,plain,(
% 1.81/0.62    ~spl5_9 | spl5_3),
% 1.81/0.62    inference(avatar_split_clause,[],[f138,f63,f144])).
% 1.81/0.62  fof(f144,plain,(
% 1.81/0.62    spl5_9 <=> sK1 = k4_xboole_0(sK1,k2_xboole_0(sK0,sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.81/0.62  fof(f138,plain,(
% 1.81/0.62    sK1 != k4_xboole_0(sK1,k2_xboole_0(sK0,sK2)) | spl5_3),
% 1.81/0.62    inference(resolution,[],[f106,f65])).
% 1.81/0.62  fof(f111,plain,(
% 1.81/0.62    ~spl5_8 | spl5_3),
% 1.81/0.62    inference(avatar_split_clause,[],[f104,f63,f108])).
% 1.81/0.62  fof(f108,plain,(
% 1.81/0.62    spl5_8 <=> k2_xboole_0(sK0,sK2) = k4_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.81/0.62  fof(f104,plain,(
% 1.81/0.62    k2_xboole_0(sK0,sK2) != k4_xboole_0(k2_xboole_0(sK0,sK2),sK1) | spl5_3),
% 1.81/0.62    inference(resolution,[],[f43,f65])).
% 1.81/0.62  fof(f96,plain,(
% 1.81/0.62    spl5_7 | ~spl5_5),
% 1.81/0.62    inference(avatar_split_clause,[],[f83,f75,f93])).
% 1.81/0.62  fof(f83,plain,(
% 1.81/0.62    sK1 = k4_xboole_0(sK1,sK2) | ~spl5_5),
% 1.81/0.62    inference(resolution,[],[f42,f77])).
% 1.81/0.62  fof(f89,plain,(
% 1.81/0.62    spl5_6 | ~spl5_2),
% 1.81/0.62    inference(avatar_split_clause,[],[f84,f58,f86])).
% 1.81/0.62  fof(f84,plain,(
% 1.81/0.62    sK2 = k4_xboole_0(sK2,sK1) | ~spl5_2),
% 1.81/0.62    inference(resolution,[],[f42,f60])).
% 1.81/0.62  fof(f78,plain,(
% 1.81/0.62    spl5_5 | ~spl5_2),
% 1.81/0.62    inference(avatar_split_clause,[],[f72,f58,f75])).
% 1.81/0.62  fof(f72,plain,(
% 1.81/0.62    r1_xboole_0(sK1,sK2) | ~spl5_2),
% 1.81/0.62    inference(resolution,[],[f41,f60])).
% 1.81/0.62  fof(f71,plain,(
% 1.81/0.62    spl5_4),
% 1.81/0.62    inference(avatar_split_clause,[],[f29,f68])).
% 1.81/0.62  fof(f29,plain,(
% 1.81/0.62    r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.81/0.62    inference(cnf_transformation,[],[f24])).
% 1.81/0.62  fof(f24,plain,(
% 1.81/0.62    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3))),
% 1.81/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f23])).
% 1.81/0.62  fof(f23,plain,(
% 1.81/0.62    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => (~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1) & r1_xboole_0(sK2,sK1) & r2_hidden(sK3,sK2) & r1_tarski(k3_xboole_0(sK0,sK1),k1_tarski(sK3)))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f17,plain,(
% 1.81/0.62    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3)))),
% 1.81/0.62    inference(flattening,[],[f16])).
% 1.81/0.62  fof(f16,plain,(
% 1.81/0.62    ? [X0,X1,X2,X3] : (~r1_xboole_0(k2_xboole_0(X0,X2),X1) & (r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))))),
% 1.81/0.62    inference(ennf_transformation,[],[f14])).
% 1.81/0.62  fof(f14,negated_conjecture,(
% 1.81/0.62    ~! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.81/0.62    inference(negated_conjecture,[],[f13])).
% 1.81/0.62  fof(f13,conjecture,(
% 1.81/0.62    ! [X0,X1,X2,X3] : ((r1_xboole_0(X2,X1) & r2_hidden(X3,X2) & r1_tarski(k3_xboole_0(X0,X1),k1_tarski(X3))) => r1_xboole_0(k2_xboole_0(X0,X2),X1))),
% 1.81/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).
% 1.81/0.62  fof(f66,plain,(
% 1.81/0.62    ~spl5_3),
% 1.81/0.62    inference(avatar_split_clause,[],[f32,f63])).
% 1.81/0.62  fof(f32,plain,(
% 1.81/0.62    ~r1_xboole_0(k2_xboole_0(sK0,sK2),sK1)),
% 1.81/0.62    inference(cnf_transformation,[],[f24])).
% 1.81/0.62  fof(f61,plain,(
% 1.81/0.62    spl5_2),
% 1.81/0.62    inference(avatar_split_clause,[],[f31,f58])).
% 1.81/0.62  fof(f31,plain,(
% 1.81/0.62    r1_xboole_0(sK2,sK1)),
% 1.81/0.62    inference(cnf_transformation,[],[f24])).
% 1.81/0.62  fof(f56,plain,(
% 1.81/0.62    spl5_1),
% 1.81/0.62    inference(avatar_split_clause,[],[f30,f53])).
% 1.81/0.62  fof(f30,plain,(
% 1.81/0.62    r2_hidden(sK3,sK2)),
% 1.81/0.62    inference(cnf_transformation,[],[f24])).
% 1.81/0.62  % SZS output end Proof for theBenchmark
% 1.81/0.62  % (18475)------------------------------
% 1.81/0.62  % (18475)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (18475)Termination reason: Refutation
% 1.81/0.62  
% 1.81/0.62  % (18475)Memory used [KB]: 7291
% 1.81/0.62  % (18475)Time elapsed: 0.214 s
% 1.81/0.62  % (18475)------------------------------
% 1.81/0.62  % (18475)------------------------------
% 1.81/0.62  % (18474)Success in time 0.267 s
%------------------------------------------------------------------------------
