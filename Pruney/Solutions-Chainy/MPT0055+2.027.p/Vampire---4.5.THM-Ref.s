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
% DateTime   : Thu Dec  3 12:30:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 123 expanded)
%              Number of leaves         :   23 (  60 expanded)
%              Depth                    :    6
%              Number of atoms          :  204 ( 313 expanded)
%              Number of equality atoms :   60 (  96 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2786,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f41,f49,f53,f69,f85,f89,f99,f168,f198,f244,f280,f314,f807,f1344,f2422,f2621,f2677])).

fof(f2677,plain,
    ( spl5_1
    | ~ spl5_92 ),
    inference(avatar_contradiction_clause,[],[f2622])).

fof(f2622,plain,
    ( $false
    | spl5_1
    | ~ spl5_92 ),
    inference(unit_resulting_resolution,[],[f40,f2620])).

fof(f2620,plain,
    ( ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_92 ),
    inference(avatar_component_clause,[],[f2619])).

fof(f2619,plain,
    ( spl5_92
  <=> ! [X5,X4] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).

fof(f40,plain,
    ( k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f39,plain,
    ( spl5_1
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2621,plain,
    ( spl5_92
    | ~ spl5_54
    | ~ spl5_66
    | ~ spl5_91 ),
    inference(avatar_split_clause,[],[f2583,f2420,f1342,f805,f2619])).

fof(f805,plain,
    ( spl5_54
  <=> ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f1342,plain,
    ( spl5_66
  <=> ! [X5,X4] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f2420,plain,
    ( spl5_91
  <=> ! [X18,X20,X19] :
        ( k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20)
        | ~ r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).

fof(f2583,plain,
    ( ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_54
    | ~ spl5_66
    | ~ spl5_91 ),
    inference(backward_demodulation,[],[f1343,f2580])).

fof(f2580,plain,
    ( ! [X4,X3] : k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))
    | ~ spl5_54
    | ~ spl5_91 ),
    inference(duplicate_literal_removal,[],[f2555])).

fof(f2555,plain,
    ( ! [X4,X3] :
        ( k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))
        | k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4)) )
    | ~ spl5_54
    | ~ spl5_91 ),
    inference(resolution,[],[f2421,f806])).

fof(f806,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK4(X1,X2,X1),X2)
        | k4_xboole_0(X1,X2) = X1 )
    | ~ spl5_54 ),
    inference(avatar_component_clause,[],[f805])).

fof(f2421,plain,
    ( ! [X19,X20,X18] :
        ( ~ r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19))
        | k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20) )
    | ~ spl5_91 ),
    inference(avatar_component_clause,[],[f2420])).

fof(f1343,plain,
    ( ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f1342])).

fof(f2422,plain,
    ( spl5_91
    | ~ spl5_29
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f292,f278,f242,f2420])).

fof(f242,plain,
    ( spl5_29
  <=> ! [X5,X7,X6] :
        ( ~ r2_hidden(X7,k4_xboole_0(X5,X6))
        | ~ r2_hidden(X7,k3_xboole_0(X5,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f278,plain,
    ( spl5_32
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f292,plain,
    ( ! [X19,X20,X18] :
        ( k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20)
        | ~ r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)) )
    | ~ spl5_29
    | ~ spl5_32 ),
    inference(resolution,[],[f279,f243])).

fof(f243,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(X7,k3_xboole_0(X5,X6))
        | ~ r2_hidden(X7,k4_xboole_0(X5,X6)) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f242])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f278])).

fof(f1344,plain,
    ( spl5_66
    | ~ spl5_13
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f328,f312,f97,f1342])).

fof(f97,plain,
    ( spl5_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f312,plain,
    ( spl5_34
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f328,plain,
    ( ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_13
    | ~ spl5_34 ),
    inference(superposition,[],[f98,f313])).

fof(f313,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f312])).

fof(f98,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f807,plain,
    ( spl5_54
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f297,f278,f196,f805])).

fof(f196,plain,
    ( spl5_26
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f297,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2) )
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(subsumption_resolution,[],[f295,f279])).

fof(f295,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2)
        | ~ r2_hidden(sK4(X1,X2,X1),X1) )
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(duplicate_literal_removal,[],[f286])).

fof(f286,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2)
        | ~ r2_hidden(sK4(X1,X2,X1),X1)
        | k4_xboole_0(X1,X2) = X1 )
    | ~ spl5_26
    | ~ spl5_32 ),
    inference(resolution,[],[f279,f197])).

fof(f197,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f196])).

fof(f314,plain,
    ( spl5_34
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f131,f87,f83,f51,f47,f312])).

fof(f47,plain,
    ( spl5_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f51,plain,
    ( spl5_4
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f83,plain,
    ( spl5_11
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f87,plain,
    ( spl5_12
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f131,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f130,f52])).

fof(f52,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f51])).

fof(f130,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl5_3
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(forward_demodulation,[],[f126,f48])).

fof(f48,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f126,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(superposition,[],[f84,f88])).

fof(f88,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f87])).

fof(f84,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f83])).

fof(f280,plain,
    ( spl5_32
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f188,f166,f278])).

fof(f166,plain,
    ( spl5_22
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK4(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f188,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl5_22 ),
    inference(factoring,[],[f167])).

fof(f167,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f166])).

fof(f244,plain,
    ( spl5_29
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f128,f87,f67,f242])).

fof(f67,plain,
    ( spl5_8
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f128,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(X7,k4_xboole_0(X5,X6))
        | ~ r2_hidden(X7,k3_xboole_0(X5,X6)) )
    | ~ spl5_8
    | ~ spl5_12 ),
    inference(superposition,[],[f68,f88])).

fof(f68,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X1) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f67])).

fof(f198,plain,(
    spl5_26 ),
    inference(avatar_split_clause,[],[f29,f196])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | ~ r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f168,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f30,f166])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f99,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f23,f97])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f89,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f22,f87])).

fof(f22,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f85,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f21,f83])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f69,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f36,f67])).

fof(f36,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f53,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f20,f51])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f49,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f41,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f17,f39])).

fof(f17,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:55:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (12219)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (12219)Refutation not found, incomplete strategy% (12219)------------------------------
% 0.21/0.47  % (12219)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (12227)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (12219)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (12219)Memory used [KB]: 10490
% 0.21/0.47  % (12219)Time elapsed: 0.050 s
% 0.21/0.47  % (12219)------------------------------
% 0.21/0.47  % (12219)------------------------------
% 0.21/0.47  % (12237)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (12236)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (12221)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (12221)Refutation not found, incomplete strategy% (12221)------------------------------
% 0.21/0.48  % (12221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12221)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12221)Memory used [KB]: 10618
% 0.21/0.48  % (12221)Time elapsed: 0.059 s
% 0.21/0.48  % (12221)------------------------------
% 0.21/0.48  % (12221)------------------------------
% 0.21/0.48  % (12223)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (12238)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.48  % (12222)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (12238)Refutation not found, incomplete strategy% (12238)------------------------------
% 0.21/0.48  % (12238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (12238)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (12238)Memory used [KB]: 10490
% 0.21/0.48  % (12238)Time elapsed: 0.079 s
% 0.21/0.48  % (12238)------------------------------
% 0.21/0.48  % (12238)------------------------------
% 0.21/0.49  % (12229)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (12232)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (12233)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (12229)Refutation not found, incomplete strategy% (12229)------------------------------
% 0.21/0.49  % (12229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12229)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12229)Memory used [KB]: 10618
% 0.21/0.49  % (12229)Time elapsed: 0.073 s
% 0.21/0.49  % (12229)------------------------------
% 0.21/0.49  % (12229)------------------------------
% 0.21/0.49  % (12233)Refutation not found, incomplete strategy% (12233)------------------------------
% 0.21/0.49  % (12233)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (12233)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (12233)Memory used [KB]: 6140
% 0.21/0.49  % (12233)Time elapsed: 0.063 s
% 0.21/0.49  % (12233)------------------------------
% 0.21/0.49  % (12233)------------------------------
% 0.21/0.49  % (12225)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (12226)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (12234)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (12235)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (12230)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (12228)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.50  % (12218)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (12224)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (12218)Refutation not found, incomplete strategy% (12218)------------------------------
% 0.21/0.51  % (12218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12218)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12218)Memory used [KB]: 6140
% 0.21/0.51  % (12218)Time elapsed: 0.080 s
% 0.21/0.51  % (12218)------------------------------
% 0.21/0.51  % (12218)------------------------------
% 0.21/0.51  % (12230)Refutation not found, incomplete strategy% (12230)------------------------------
% 0.21/0.51  % (12230)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (12230)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (12230)Memory used [KB]: 6012
% 0.21/0.51  % (12230)Time elapsed: 0.005 s
% 0.21/0.51  % (12230)------------------------------
% 0.21/0.51  % (12230)------------------------------
% 0.21/0.51  % (12220)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.52  % (12231)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.52  % (12228)Refutation not found, incomplete strategy% (12228)------------------------------
% 0.21/0.52  % (12228)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12228)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12228)Memory used [KB]: 6012
% 0.21/0.52  % (12228)Time elapsed: 0.110 s
% 0.21/0.52  % (12228)------------------------------
% 0.21/0.52  % (12228)------------------------------
% 0.21/0.52  % (12231)Refutation not found, incomplete strategy% (12231)------------------------------
% 0.21/0.52  % (12231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12231)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12231)Memory used [KB]: 1535
% 0.21/0.52  % (12231)Time elapsed: 0.109 s
% 0.21/0.52  % (12231)------------------------------
% 0.21/0.52  % (12231)------------------------------
% 0.21/0.52  % (12227)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f2786,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f41,f49,f53,f69,f85,f89,f99,f168,f198,f244,f280,f314,f807,f1344,f2422,f2621,f2677])).
% 0.21/0.52  fof(f2677,plain,(
% 0.21/0.52    spl5_1 | ~spl5_92),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f2622])).
% 0.21/0.52  fof(f2622,plain,(
% 0.21/0.52    $false | (spl5_1 | ~spl5_92)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f40,f2620])).
% 0.21/0.52  fof(f2620,plain,(
% 0.21/0.52    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl5_92),
% 0.21/0.52    inference(avatar_component_clause,[],[f2619])).
% 0.21/0.52  fof(f2619,plain,(
% 0.21/0.52    spl5_92 <=> ! [X5,X4] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_92])])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl5_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    spl5_1 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.52  fof(f2621,plain,(
% 0.21/0.52    spl5_92 | ~spl5_54 | ~spl5_66 | ~spl5_91),
% 0.21/0.52    inference(avatar_split_clause,[],[f2583,f2420,f1342,f805,f2619])).
% 0.21/0.52  fof(f805,plain,(
% 0.21/0.52    spl5_54 <=> ! [X1,X2] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.21/0.52  fof(f1342,plain,(
% 0.21/0.52    spl5_66 <=> ! [X5,X4] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 0.21/0.52  fof(f2420,plain,(
% 0.21/0.52    spl5_91 <=> ! [X18,X20,X19] : (k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20) | ~r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_91])])).
% 0.21/0.52  fof(f2583,plain,(
% 0.21/0.52    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl5_54 | ~spl5_66 | ~spl5_91)),
% 0.21/0.52    inference(backward_demodulation,[],[f1343,f2580])).
% 0.21/0.52  fof(f2580,plain,(
% 0.21/0.52    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))) ) | (~spl5_54 | ~spl5_91)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f2555])).
% 0.21/0.52  fof(f2555,plain,(
% 0.21/0.52    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4)) | k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))) ) | (~spl5_54 | ~spl5_91)),
% 0.21/0.52    inference(resolution,[],[f2421,f806])).
% 0.21/0.52  fof(f806,plain,(
% 0.21/0.52    ( ! [X2,X1] : (r2_hidden(sK4(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) ) | ~spl5_54),
% 0.21/0.52    inference(avatar_component_clause,[],[f805])).
% 0.21/0.52  fof(f2421,plain,(
% 0.21/0.52    ( ! [X19,X20,X18] : (~r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)) | k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20)) ) | ~spl5_91),
% 0.21/0.52    inference(avatar_component_clause,[],[f2420])).
% 0.21/0.52  fof(f1343,plain,(
% 0.21/0.52    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl5_66),
% 0.21/0.52    inference(avatar_component_clause,[],[f1342])).
% 0.21/0.52  fof(f2422,plain,(
% 0.21/0.52    spl5_91 | ~spl5_29 | ~spl5_32),
% 0.21/0.52    inference(avatar_split_clause,[],[f292,f278,f242,f2420])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    spl5_29 <=> ! [X5,X7,X6] : (~r2_hidden(X7,k4_xboole_0(X5,X6)) | ~r2_hidden(X7,k3_xboole_0(X5,X6)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.52  fof(f278,plain,(
% 0.21/0.52    spl5_32 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.52  fof(f292,plain,(
% 0.21/0.52    ( ! [X19,X20,X18] : (k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20) | ~r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19))) ) | (~spl5_29 | ~spl5_32)),
% 0.21/0.52    inference(resolution,[],[f279,f243])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (~r2_hidden(X7,k3_xboole_0(X5,X6)) | ~r2_hidden(X7,k4_xboole_0(X5,X6))) ) | ~spl5_29),
% 0.21/0.52    inference(avatar_component_clause,[],[f242])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl5_32),
% 0.21/0.52    inference(avatar_component_clause,[],[f278])).
% 0.21/0.52  fof(f1344,plain,(
% 0.21/0.52    spl5_66 | ~spl5_13 | ~spl5_34),
% 0.21/0.52    inference(avatar_split_clause,[],[f328,f312,f97,f1342])).
% 0.21/0.52  fof(f97,plain,(
% 0.21/0.52    spl5_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.52  fof(f312,plain,(
% 0.21/0.52    spl5_34 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.52  fof(f328,plain,(
% 0.21/0.52    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl5_13 | ~spl5_34)),
% 0.21/0.52    inference(superposition,[],[f98,f313])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl5_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f312])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl5_13),
% 0.21/0.52    inference(avatar_component_clause,[],[f97])).
% 0.21/0.52  fof(f807,plain,(
% 0.21/0.52    spl5_54 | ~spl5_26 | ~spl5_32),
% 0.21/0.52    inference(avatar_split_clause,[],[f297,f278,f196,f805])).
% 0.21/0.52  fof(f196,plain,(
% 0.21/0.52    spl5_26 <=> ! [X1,X0,X2] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.52  fof(f297,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2)) ) | (~spl5_26 | ~spl5_32)),
% 0.21/0.52    inference(subsumption_resolution,[],[f295,f279])).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1)) ) | (~spl5_26 | ~spl5_32)),
% 0.21/0.52    inference(duplicate_literal_removal,[],[f286])).
% 0.21/0.52  fof(f286,plain,(
% 0.21/0.52    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1) | k4_xboole_0(X1,X2) = X1) ) | (~spl5_26 | ~spl5_32)),
% 0.21/0.52    inference(resolution,[],[f279,f197])).
% 0.21/0.52  fof(f197,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl5_26),
% 0.21/0.52    inference(avatar_component_clause,[],[f196])).
% 0.21/0.52  fof(f314,plain,(
% 0.21/0.52    spl5_34 | ~spl5_3 | ~spl5_4 | ~spl5_11 | ~spl5_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f131,f87,f83,f51,f47,f312])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    spl5_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    spl5_4 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    spl5_11 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.52  fof(f87,plain,(
% 0.21/0.52    spl5_12 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | (~spl5_3 | ~spl5_4 | ~spl5_11 | ~spl5_12)),
% 0.21/0.52    inference(forward_demodulation,[],[f130,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl5_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f51])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl5_3 | ~spl5_11 | ~spl5_12)),
% 0.21/0.52    inference(forward_demodulation,[],[f126,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f47])).
% 0.21/0.52  fof(f126,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl5_11 | ~spl5_12)),
% 0.21/0.52    inference(superposition,[],[f84,f88])).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl5_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f87])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl5_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f83])).
% 0.21/0.52  fof(f280,plain,(
% 0.21/0.52    spl5_32 | ~spl5_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f188,f166,f278])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    spl5_22 <=> ! [X1,X0,X2] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.52  fof(f188,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl5_22),
% 0.21/0.52    inference(factoring,[],[f167])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl5_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f166])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    spl5_29 | ~spl5_8 | ~spl5_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f128,f87,f67,f242])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl5_8 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    ( ! [X6,X7,X5] : (~r2_hidden(X7,k4_xboole_0(X5,X6)) | ~r2_hidden(X7,k3_xboole_0(X5,X6))) ) | (~spl5_8 | ~spl5_12)),
% 0.21/0.52    inference(superposition,[],[f68,f88])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) ) | ~spl5_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f67])).
% 0.21/0.52  fof(f198,plain,(
% 0.21/0.52    spl5_26),
% 0.21/0.52    inference(avatar_split_clause,[],[f29,f196])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.52  fof(f168,plain,(
% 0.21/0.52    spl5_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f30,f166])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl5_13),
% 0.21/0.52    inference(avatar_split_clause,[],[f23,f97])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl5_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f22,f87])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl5_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f21,f83])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    spl5_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f36,f67])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.52    inference(equality_resolution,[],[f33])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.52    inference(cnf_transformation,[],[f2])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    spl5_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f20,f51])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    spl5_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f19,f47])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    ~spl5_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f17,f39])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,negated_conjecture,(
% 0.21/0.52    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    inference(negated_conjecture,[],[f10])).
% 0.21/0.52  fof(f10,conjecture,(
% 0.21/0.52    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (12227)------------------------------
% 0.21/0.52  % (12227)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12227)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (12227)Memory used [KB]: 12409
% 0.21/0.52  % (12227)Time elapsed: 0.110 s
% 0.21/0.52  % (12227)------------------------------
% 0.21/0.52  % (12227)------------------------------
% 0.21/0.52  % (12217)Success in time 0.165 s
%------------------------------------------------------------------------------
