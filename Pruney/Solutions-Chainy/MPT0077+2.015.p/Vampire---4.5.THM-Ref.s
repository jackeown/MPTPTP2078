%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:30:45 EST 2020

% Result     : Theorem 1.50s
% Output     : Refutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 392 expanded)
%              Number of leaves         :   27 ( 140 expanded)
%              Depth                    :   15
%              Number of atoms          :  326 ( 713 expanded)
%              Number of equality atoms :   67 ( 230 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2398,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f81,f147,f149,f162,f179,f195,f204,f205,f603,f608,f1260,f1500,f1645,f2362,f2388,f2397])).

fof(f2397,plain,
    ( ~ spl4_1
    | spl4_3 ),
    inference(avatar_contradiction_clause,[],[f2396])).

fof(f2396,plain,
    ( $false
    | ~ spl4_1
    | spl4_3 ),
    inference(subsumption_resolution,[],[f80,f156])).

fof(f156,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl4_1 ),
    inference(resolution,[],[f59,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f59,plain,
    ( r1_xboole_0(sK0,sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl4_1
  <=> r1_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f80,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl4_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl4_3
  <=> r1_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f2388,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f2387])).

fof(f2387,plain,
    ( $false
    | ~ spl4_5
    | spl4_6 ),
    inference(subsumption_resolution,[],[f178,f211])).

fof(f211,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl4_5 ),
    inference(resolution,[],[f160,f43])).

fof(f160,plain,
    ( r1_xboole_0(sK0,sK2)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f159,plain,
    ( spl4_5
  <=> r1_xboole_0(sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f178,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl4_6
  <=> r1_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f2362,plain,
    ( ~ spl4_21
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f2361])).

fof(f2361,plain,
    ( $false
    | ~ spl4_21
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f2360,f136])).

fof(f136,plain,(
    ! [X0] : r1_xboole_0(k1_xboole_0,X0) ),
    inference(unit_resulting_resolution,[],[f95,f43])).

fof(f95,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f93,f54])).

fof(f54,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f48,f34])).

fof(f34,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f48,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f33,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f33,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f93,plain,(
    ! [X0] :
      ( k1_xboole_0 != k4_xboole_0(X0,X0)
      | r1_xboole_0(X0,k1_xboole_0) ) ),
    inference(superposition,[],[f52,f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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

fof(f2360,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ spl4_21
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f2359,f1428])).

fof(f1428,plain,(
    ! [X19,X18] : k1_xboole_0 = k4_xboole_0(X18,k2_xboole_0(X19,X18)) ),
    inference(backward_demodulation,[],[f1117,f1343])).

fof(f1343,plain,(
    ! [X14,X15] : k1_xboole_0 = k4_xboole_0(k2_xboole_0(X15,X14),k2_xboole_0(X14,X15)) ),
    inference(superposition,[],[f519,f54])).

fof(f519,plain,(
    ! [X4,X5,X3] : k4_xboole_0(k2_xboole_0(X3,X5),X4) = k4_xboole_0(k2_xboole_0(X5,X3),X4) ),
    inference(superposition,[],[f123,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).

fof(f123,plain,(
    ! [X4,X5,X3] : k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4) ),
    inference(superposition,[],[f46,f37])).

fof(f37,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f1117,plain,(
    ! [X19,X18] : k4_xboole_0(X18,k2_xboole_0(X19,X18)) = k4_xboole_0(k2_xboole_0(X18,X19),k2_xboole_0(X19,X18)) ),
    inference(superposition,[],[f131,f461])).

fof(f461,plain,(
    ! [X4,X3] : k2_xboole_0(X4,X3) = k2_xboole_0(X4,k2_xboole_0(X3,X4)) ),
    inference(forward_demodulation,[],[f446,f39])).

fof(f39,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f446,plain,(
    ! [X4,X3] : k2_xboole_0(X4,k2_xboole_0(X3,X4)) = k2_xboole_0(X4,k4_xboole_0(X3,X4)) ),
    inference(superposition,[],[f39,f131])).

fof(f131,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X3,X2),X2) ),
    inference(forward_demodulation,[],[f122,f35])).

fof(f35,plain,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

fof(f122,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0) ),
    inference(superposition,[],[f46,f54])).

fof(f2359,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k2_xboole_0(sK1,sK2)))
    | ~ spl4_21
    | ~ spl4_23
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f2358,f1644])).

fof(f1644,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f1642])).

fof(f1642,plain,
    ( spl4_25
  <=> sK2 = k4_xboole_0(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f2358,plain,
    ( ~ r1_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))),k4_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))))
    | ~ spl4_21
    | ~ spl4_23 ),
    inference(forward_demodulation,[],[f2354,f2121])).

fof(f2121,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k2_xboole_0(X8,X10),k2_xboole_0(X8,X9)) = k4_xboole_0(X10,k2_xboole_0(X8,X9)) ),
    inference(forward_demodulation,[],[f2063,f129])).

fof(f129,plain,(
    ! [X2,X3] : k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X2,X3),X2) ),
    inference(forward_demodulation,[],[f120,f68])).

fof(f68,plain,(
    ! [X0] : k2_xboole_0(k1_xboole_0,X0) = X0 ),
    inference(superposition,[],[f37,f35])).

fof(f120,plain,(
    ! [X2,X3] : k4_xboole_0(k2_xboole_0(X2,X3),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2)) ),
    inference(superposition,[],[f46,f54])).

fof(f2063,plain,(
    ! [X10,X8,X9] : k4_xboole_0(k2_xboole_0(X8,X10),k2_xboole_0(X8,X9)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X8,X9),X10),k2_xboole_0(X8,X9)) ),
    inference(superposition,[],[f462,f433])).

fof(f433,plain,(
    ! [X2,X3] : k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(forward_demodulation,[],[f418,f39])).

fof(f418,plain,(
    ! [X2,X3] : k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3)) ),
    inference(superposition,[],[f39,f129])).

fof(f462,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X5,X6),X7),X6) = k4_xboole_0(k2_xboole_0(X5,X7),X6) ),
    inference(forward_demodulation,[],[f447,f46])).

fof(f447,plain,(
    ! [X6,X7,X5] : k4_xboole_0(k2_xboole_0(k2_xboole_0(X5,X6),X7),X6) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X7,X6)) ),
    inference(superposition,[],[f46,f131])).

fof(f2354,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))),k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))))
    | ~ spl4_21
    | ~ spl4_23 ),
    inference(backward_demodulation,[],[f1267,f2327])).

fof(f2327,plain,
    ( ! [X0] : k4_xboole_0(k2_xboole_0(sK1,X0),sK0) = k2_xboole_0(sK1,k4_xboole_0(X0,sK0))
    | ~ spl4_23 ),
    inference(superposition,[],[f46,f1499])).

fof(f1499,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f1497])).

fof(f1497,plain,
    ( spl4_23
  <=> sK1 = k4_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f1267,plain,
    ( ~ r1_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)))
    | ~ spl4_21 ),
    inference(unit_resulting_resolution,[],[f1259,f91])).

fof(f91,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,X2)
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(forward_demodulation,[],[f89,f34])).

fof(f89,plain,(
    ! [X2,X3] :
      ( ~ r2_hidden(X3,k4_xboole_0(X2,k1_xboole_0))
      | ~ r1_xboole_0(X2,X2) ) ),
    inference(superposition,[],[f50,f54])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f42,f38])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,k3_xboole_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f24])).

fof(f24,plain,(
    ! [X1,X0] :
      ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
     => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f1259,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)))
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f1257])).

fof(f1257,plain,
    ( spl4_21
  <=> r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f1645,plain,
    ( spl4_25
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f896,f605,f1642])).

fof(f605,plain,
    ( spl4_18
  <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f896,plain,
    ( sK2 = k4_xboole_0(sK2,sK0)
    | ~ spl4_18 ),
    inference(backward_demodulation,[],[f725,f873])).

fof(f873,plain,(
    ! [X6,X7] : k2_xboole_0(X6,k4_xboole_0(X6,X7)) = X6 ),
    inference(superposition,[],[f475,f37])).

fof(f475,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2 ),
    inference(superposition,[],[f106,f39])).

fof(f106,plain,(
    ! [X2,X3] : k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2 ),
    inference(superposition,[],[f49,f37])).

fof(f49,plain,(
    ! [X0,X1] : k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0 ),
    inference(definition_unfolding,[],[f40,f38])).

fof(f40,plain,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

fof(f725,plain,
    ( k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f724,f35])).

fof(f724,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f711,f37])).

fof(f711,plain,
    ( k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2)
    | ~ spl4_18 ),
    inference(superposition,[],[f39,f607])).

fof(f607,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f605])).

fof(f1500,plain,
    ( spl4_23
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f895,f600,f1497])).

fof(f600,plain,
    ( spl4_17
  <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f895,plain,
    ( sK1 = k4_xboole_0(sK1,sK0)
    | ~ spl4_17 ),
    inference(backward_demodulation,[],[f694,f873])).

fof(f694,plain,
    ( k4_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f693,f35])).

fof(f693,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl4_17 ),
    inference(forward_demodulation,[],[f680,f37])).

fof(f680,plain,
    ( k2_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK1)
    | ~ spl4_17 ),
    inference(superposition,[],[f39,f602])).

fof(f602,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f600])).

fof(f1260,plain,
    ( spl4_21
    | spl4_4 ),
    inference(avatar_split_clause,[],[f225,f144,f1257])).

fof(f144,plain,
    ( spl4_4
  <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f225,plain,
    ( r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)))
    | spl4_4 ),
    inference(unit_resulting_resolution,[],[f145,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1)))
      | r1_xboole_0(X0,X1) ) ),
    inference(definition_unfolding,[],[f41,f38])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f145,plain,
    ( ~ r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f608,plain,
    ( spl4_18
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f218,f176,f605])).

fof(f218,plain,
    ( k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f177,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ) ),
    inference(definition_unfolding,[],[f44,f38])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f177,plain,
    ( r1_xboole_0(sK2,sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f176])).

fof(f603,plain,
    ( spl4_17
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f168,f78,f600])).

fof(f168,plain,
    ( k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f79,f53])).

fof(f79,plain,
    ( r1_xboole_0(sK1,sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f78])).

fof(f205,plain,
    ( spl4_5
    | spl4_2 ),
    inference(avatar_split_clause,[],[f200,f61,f159])).

fof(f61,plain,
    ( spl4_2
  <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f200,plain,
    ( r1_xboole_0(sK0,sK2)
    | spl4_2 ),
    inference(subsumption_resolution,[],[f32,f62])).

fof(f62,plain,
    ( ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f32,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
      & ( ~ r1_xboole_0(sK0,sK2)
        | ~ r1_xboole_0(sK0,sK1) ) )
    | ( r1_xboole_0(sK0,sK2)
      & r1_xboole_0(sK0,sK1)
      & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ( ~ r1_xboole_0(X0,X2)
            | ~ r1_xboole_0(X0,X1) ) )
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) )
   => ( ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
        & ( ~ r1_xboole_0(sK0,sK2)
          | ~ r1_xboole_0(sK0,sK1) ) )
      | ( r1_xboole_0(sK0,sK2)
        & r1_xboole_0(sK0,sK1)
        & ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0,X1,X2] :
      ( ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
        & ( ~ r1_xboole_0(X0,X2)
          | ~ r1_xboole_0(X0,X1) ) )
      | ( r1_xboole_0(X0,X2)
        & r1_xboole_0(X0,X1)
        & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
            & ~ ( r1_xboole_0(X0,X2)
                & r1_xboole_0(X0,X1) ) )
        & ~ ( r1_xboole_0(X0,X2)
            & r1_xboole_0(X0,X1)
            & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f204,plain,
    ( spl4_2
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | spl4_2
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f191,f62])).

fof(f191,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_4 ),
    inference(unit_resulting_resolution,[],[f146,f43])).

fof(f146,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f144])).

fof(f195,plain,
    ( ~ spl4_4
    | spl4_6 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | ~ spl4_4
    | spl4_6 ),
    inference(subsumption_resolution,[],[f188,f71])).

fof(f71,plain,(
    ! [X2,X1] : r1_tarski(X1,k2_xboole_0(X2,X1)) ),
    inference(superposition,[],[f36,f37])).

fof(f36,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f188,plain,
    ( ~ r1_tarski(sK2,k2_xboole_0(sK1,sK2))
    | ~ spl4_4
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f178,f146,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X1,X2)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f179,plain,
    ( ~ spl4_6
    | spl4_5 ),
    inference(avatar_split_clause,[],[f167,f159,f176])).

fof(f167,plain,
    ( ~ r1_xboole_0(sK2,sK0)
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f161,f43])).

fof(f161,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f159])).

fof(f162,plain,
    ( ~ spl4_1
    | ~ spl4_5
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f150,f61,f159,f57])).

fof(f150,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f27,f63])).

fof(f63,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f27,plain,
    ( ~ r1_xboole_0(sK0,sK2)
    | ~ r1_xboole_0(sK0,sK1)
    | ~ r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) ),
    inference(cnf_transformation,[],[f23])).

fof(f149,plain,
    ( spl4_3
    | ~ spl4_4 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f146,f101])).

fof(f101,plain,
    ( ! [X0] : ~ r1_xboole_0(k2_xboole_0(sK1,X0),sK0)
    | spl4_3 ),
    inference(unit_resulting_resolution,[],[f36,f80,f47])).

fof(f147,plain,
    ( spl4_4
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f66,f61,f144])).

fof(f66,plain,
    ( r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)
    | ~ spl4_2 ),
    inference(unit_resulting_resolution,[],[f63,f43])).

fof(f81,plain,
    ( ~ spl4_3
    | spl4_1 ),
    inference(avatar_split_clause,[],[f65,f57,f78])).

fof(f65,plain,
    ( ~ r1_xboole_0(sK1,sK0)
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f58,f43])).

fof(f58,plain,
    ( ~ r1_xboole_0(sK0,sK1)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f64,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f31,f61,f57])).

fof(f31,plain,
    ( r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))
    | r1_xboole_0(sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 15:00:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (12884)lrs+1_128_add=off:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bs=unit_only:gs=on:gsem=off:lwlo=on:nm=2:nwc=1:sas=z3:stl=90:sac=on:sp=occurrence:urr=on:updr=off:uhcvi=on_520 on theBenchmark
% 0.20/0.46  % (12880)dis+1002_2_add=off:afr=on:afp=10000:afq=2.0:amm=off:anc=none:cond=on:er=filter:fsr=off:nm=0:nwc=1.3:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (12889)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.20/0.46  % (12878)dis+11_50_add=large:afp=1000:afq=1.0:amm=sco:anc=none:fsr=off:nm=16:nwc=1.5:sac=on_13 on theBenchmark
% 0.20/0.46  % (12879)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.20/0.46  % (12876)lrs+11_24_add=large:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:bd=off:cond=fast:fde=unused:gs=on:irw=on:lma=on:nm=4:nwc=1.3:nicw=on:sas=z3:stl=30:sac=on:sp=reverse_arity:uhcvi=on_136 on theBenchmark
% 0.20/0.47  % (12892)ott-1_50_afr=on:afp=1000:afq=1.2:amm=sco:anc=none:bsr=on:cond=fast:fsr=off:fde=none:irw=on:nm=16:nwc=1.5:updr=off:uhcvi=on_1883 on theBenchmark
% 0.20/0.47  % (12890)lrs+11_128_add=large:afr=on:afp=10000:afq=1.2:amm=sco:anc=none:bs=unit_only:cond=on:nwc=1.3:stl=30:sac=on:uhcvi=on_236 on theBenchmark
% 0.20/0.48  % (12885)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_461 on theBenchmark
% 0.20/0.48  % (12882)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.20/0.48  % (12877)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.20/0.48  % (12888)dis+1_24_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1.5:sp=occurrence:updr=off_16 on theBenchmark
% 0.20/0.48  % (12887)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.20/0.48  % (12883)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.49  % (12881)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.20/0.49  % (12893)lrs+11_64_acc=model:afp=100000:afq=1.2:anc=all_dependent:bd=off:bs=unit_only:cond=fast:fsr=off:gs=on:gsaa=full_model:gsem=off:irw=on:lma=on:nwc=1:stl=150:sac=on:sp=reverse_arity:urr=on:updr=off_893 on theBenchmark
% 0.20/0.50  % (12887)Refutation not found, incomplete strategy% (12887)------------------------------
% 0.20/0.50  % (12887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (12887)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (12887)Memory used [KB]: 10618
% 0.20/0.50  % (12887)Time elapsed: 0.083 s
% 0.20/0.50  % (12887)------------------------------
% 0.20/0.50  % (12887)------------------------------
% 0.20/0.50  % (12891)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 1.34/0.52  % (12886)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_385 on theBenchmark
% 1.50/0.59  % (12891)Refutation found. Thanks to Tanya!
% 1.50/0.59  % SZS status Theorem for theBenchmark
% 1.50/0.59  % SZS output start Proof for theBenchmark
% 1.50/0.59  fof(f2398,plain,(
% 1.50/0.59    $false),
% 1.50/0.59    inference(avatar_sat_refutation,[],[f64,f81,f147,f149,f162,f179,f195,f204,f205,f603,f608,f1260,f1500,f1645,f2362,f2388,f2397])).
% 1.50/0.59  fof(f2397,plain,(
% 1.50/0.59    ~spl4_1 | spl4_3),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f2396])).
% 1.50/0.59  fof(f2396,plain,(
% 1.50/0.59    $false | (~spl4_1 | spl4_3)),
% 1.50/0.59    inference(subsumption_resolution,[],[f80,f156])).
% 1.50/0.59  fof(f156,plain,(
% 1.50/0.59    r1_xboole_0(sK1,sK0) | ~spl4_1),
% 1.50/0.59    inference(resolution,[],[f59,f43])).
% 1.50/0.59  fof(f43,plain,(
% 1.50/0.59    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f19])).
% 1.50/0.59  fof(f19,plain,(
% 1.50/0.59    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 1.50/0.59    inference(ennf_transformation,[],[f3])).
% 1.50/0.59  fof(f3,axiom,(
% 1.50/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 1.50/0.59  fof(f59,plain,(
% 1.50/0.59    r1_xboole_0(sK0,sK1) | ~spl4_1),
% 1.50/0.59    inference(avatar_component_clause,[],[f57])).
% 1.50/0.59  fof(f57,plain,(
% 1.50/0.59    spl4_1 <=> r1_xboole_0(sK0,sK1)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.50/0.59  fof(f80,plain,(
% 1.50/0.59    ~r1_xboole_0(sK1,sK0) | spl4_3),
% 1.50/0.59    inference(avatar_component_clause,[],[f78])).
% 1.50/0.59  fof(f78,plain,(
% 1.50/0.59    spl4_3 <=> r1_xboole_0(sK1,sK0)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.50/0.59  fof(f2388,plain,(
% 1.50/0.59    ~spl4_5 | spl4_6),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f2387])).
% 1.50/0.59  fof(f2387,plain,(
% 1.50/0.59    $false | (~spl4_5 | spl4_6)),
% 1.50/0.59    inference(subsumption_resolution,[],[f178,f211])).
% 1.50/0.59  fof(f211,plain,(
% 1.50/0.59    r1_xboole_0(sK2,sK0) | ~spl4_5),
% 1.50/0.59    inference(resolution,[],[f160,f43])).
% 1.50/0.59  fof(f160,plain,(
% 1.50/0.59    r1_xboole_0(sK0,sK2) | ~spl4_5),
% 1.50/0.59    inference(avatar_component_clause,[],[f159])).
% 1.50/0.59  fof(f159,plain,(
% 1.50/0.59    spl4_5 <=> r1_xboole_0(sK0,sK2)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.50/0.59  fof(f178,plain,(
% 1.50/0.59    ~r1_xboole_0(sK2,sK0) | spl4_6),
% 1.50/0.59    inference(avatar_component_clause,[],[f176])).
% 1.50/0.59  fof(f176,plain,(
% 1.50/0.59    spl4_6 <=> r1_xboole_0(sK2,sK0)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.50/0.59  fof(f2362,plain,(
% 1.50/0.59    ~spl4_21 | ~spl4_23 | ~spl4_25),
% 1.50/0.59    inference(avatar_contradiction_clause,[],[f2361])).
% 1.50/0.59  fof(f2361,plain,(
% 1.50/0.59    $false | (~spl4_21 | ~spl4_23 | ~spl4_25)),
% 1.50/0.59    inference(subsumption_resolution,[],[f2360,f136])).
% 1.50/0.59  fof(f136,plain,(
% 1.50/0.59    ( ! [X0] : (r1_xboole_0(k1_xboole_0,X0)) )),
% 1.50/0.59    inference(unit_resulting_resolution,[],[f95,f43])).
% 1.50/0.59  fof(f95,plain,(
% 1.50/0.59    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 1.50/0.59    inference(subsumption_resolution,[],[f93,f54])).
% 1.50/0.59  fof(f54,plain,(
% 1.50/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 1.50/0.59    inference(backward_demodulation,[],[f48,f34])).
% 1.50/0.59  fof(f34,plain,(
% 1.50/0.59    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.50/0.59    inference(cnf_transformation,[],[f8])).
% 1.50/0.59  fof(f8,axiom,(
% 1.50/0.59    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 1.50/0.59  fof(f48,plain,(
% 1.50/0.59    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 1.50/0.59    inference(definition_unfolding,[],[f33,f38])).
% 1.50/0.59  fof(f38,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f10])).
% 1.50/0.59  fof(f10,axiom,(
% 1.50/0.59    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 1.50/0.59  fof(f33,plain,(
% 1.50/0.59    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f6])).
% 1.50/0.59  fof(f6,axiom,(
% 1.50/0.59    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 1.50/0.59  fof(f93,plain,(
% 1.50/0.59    ( ! [X0] : (k1_xboole_0 != k4_xboole_0(X0,X0) | r1_xboole_0(X0,k1_xboole_0)) )),
% 1.50/0.59    inference(superposition,[],[f52,f34])).
% 1.50/0.59  fof(f52,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k1_xboole_0 != k4_xboole_0(X0,k4_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.50/0.59    inference(definition_unfolding,[],[f45,f38])).
% 1.50/0.59  fof(f45,plain,(
% 1.50/0.59    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 1.50/0.59    inference(cnf_transformation,[],[f26])).
% 1.50/0.59  fof(f26,plain,(
% 1.50/0.59    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 1.50/0.59    inference(nnf_transformation,[],[f2])).
% 1.50/0.59  fof(f2,axiom,(
% 1.50/0.59    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 1.50/0.59  fof(f2360,plain,(
% 1.50/0.59    ~r1_xboole_0(k1_xboole_0,k1_xboole_0) | (~spl4_21 | ~spl4_23 | ~spl4_25)),
% 1.50/0.59    inference(forward_demodulation,[],[f2359,f1428])).
% 1.50/0.59  fof(f1428,plain,(
% 1.50/0.59    ( ! [X19,X18] : (k1_xboole_0 = k4_xboole_0(X18,k2_xboole_0(X19,X18))) )),
% 1.50/0.59    inference(backward_demodulation,[],[f1117,f1343])).
% 1.50/0.59  fof(f1343,plain,(
% 1.50/0.59    ( ! [X14,X15] : (k1_xboole_0 = k4_xboole_0(k2_xboole_0(X15,X14),k2_xboole_0(X14,X15))) )),
% 1.50/0.59    inference(superposition,[],[f519,f54])).
% 1.50/0.59  fof(f519,plain,(
% 1.50/0.59    ( ! [X4,X5,X3] : (k4_xboole_0(k2_xboole_0(X3,X5),X4) = k4_xboole_0(k2_xboole_0(X5,X3),X4)) )),
% 1.50/0.59    inference(superposition,[],[f123,f46])).
% 1.50/0.59  fof(f46,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f9])).
% 1.50/0.59  fof(f9,axiom,(
% 1.50/0.59    ! [X0,X1,X2] : k4_xboole_0(k2_xboole_0(X0,X1),X2) = k2_xboole_0(k4_xboole_0(X0,X2),k4_xboole_0(X1,X2))),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_xboole_1)).
% 1.50/0.59  fof(f123,plain,(
% 1.50/0.59    ( ! [X4,X5,X3] : (k2_xboole_0(k4_xboole_0(X5,X4),k4_xboole_0(X3,X4)) = k4_xboole_0(k2_xboole_0(X3,X5),X4)) )),
% 1.50/0.59    inference(superposition,[],[f46,f37])).
% 1.50/0.59  fof(f37,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 1.50/0.59    inference(cnf_transformation,[],[f1])).
% 1.50/0.59  fof(f1,axiom,(
% 1.50/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 1.50/0.59  fof(f1117,plain,(
% 1.50/0.59    ( ! [X19,X18] : (k4_xboole_0(X18,k2_xboole_0(X19,X18)) = k4_xboole_0(k2_xboole_0(X18,X19),k2_xboole_0(X19,X18))) )),
% 1.50/0.59    inference(superposition,[],[f131,f461])).
% 1.50/0.59  fof(f461,plain,(
% 1.50/0.59    ( ! [X4,X3] : (k2_xboole_0(X4,X3) = k2_xboole_0(X4,k2_xboole_0(X3,X4))) )),
% 1.50/0.59    inference(forward_demodulation,[],[f446,f39])).
% 1.50/0.59  fof(f39,plain,(
% 1.50/0.59    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f7])).
% 1.50/0.59  fof(f7,axiom,(
% 1.50/0.59    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 1.50/0.59  fof(f446,plain,(
% 1.50/0.59    ( ! [X4,X3] : (k2_xboole_0(X4,k2_xboole_0(X3,X4)) = k2_xboole_0(X4,k4_xboole_0(X3,X4))) )),
% 1.50/0.59    inference(superposition,[],[f39,f131])).
% 1.50/0.59  fof(f131,plain,(
% 1.50/0.59    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X3,X2),X2)) )),
% 1.50/0.59    inference(forward_demodulation,[],[f122,f35])).
% 1.50/0.59  fof(f35,plain,(
% 1.50/0.59    ( ! [X0] : (k2_xboole_0(X0,k1_xboole_0) = X0) )),
% 1.50/0.59    inference(cnf_transformation,[],[f5])).
% 1.50/0.59  fof(f5,axiom,(
% 1.50/0.59    ! [X0] : k2_xboole_0(X0,k1_xboole_0) = X0),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).
% 1.50/0.59  fof(f122,plain,(
% 1.50/0.59    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X3,X2),X2) = k2_xboole_0(k4_xboole_0(X3,X2),k1_xboole_0)) )),
% 1.50/0.59    inference(superposition,[],[f46,f54])).
% 1.50/0.59  fof(f2359,plain,(
% 1.50/0.59    ~r1_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK1,sK2)),k4_xboole_0(sK2,k2_xboole_0(sK1,sK2))) | (~spl4_21 | ~spl4_23 | ~spl4_25)),
% 1.50/0.59    inference(forward_demodulation,[],[f2358,f1644])).
% 1.50/0.59  fof(f1644,plain,(
% 1.50/0.59    sK2 = k4_xboole_0(sK2,sK0) | ~spl4_25),
% 1.50/0.59    inference(avatar_component_clause,[],[f1642])).
% 1.50/0.59  fof(f1642,plain,(
% 1.50/0.59    spl4_25 <=> sK2 = k4_xboole_0(sK2,sK0)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 1.50/0.59  fof(f2358,plain,(
% 1.50/0.59    ~r1_xboole_0(k4_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))),k4_xboole_0(sK2,k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)))) | (~spl4_21 | ~spl4_23)),
% 1.50/0.59    inference(forward_demodulation,[],[f2354,f2121])).
% 1.50/0.59  fof(f2121,plain,(
% 1.50/0.59    ( ! [X10,X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X10),k2_xboole_0(X8,X9)) = k4_xboole_0(X10,k2_xboole_0(X8,X9))) )),
% 1.50/0.59    inference(forward_demodulation,[],[f2063,f129])).
% 1.50/0.59  fof(f129,plain,(
% 1.50/0.59    ( ! [X2,X3] : (k4_xboole_0(X3,X2) = k4_xboole_0(k2_xboole_0(X2,X3),X2)) )),
% 1.50/0.59    inference(forward_demodulation,[],[f120,f68])).
% 1.50/0.59  fof(f68,plain,(
% 1.50/0.59    ( ! [X0] : (k2_xboole_0(k1_xboole_0,X0) = X0) )),
% 1.50/0.59    inference(superposition,[],[f37,f35])).
% 1.50/0.59  fof(f120,plain,(
% 1.50/0.59    ( ! [X2,X3] : (k4_xboole_0(k2_xboole_0(X2,X3),X2) = k2_xboole_0(k1_xboole_0,k4_xboole_0(X3,X2))) )),
% 1.50/0.59    inference(superposition,[],[f46,f54])).
% 1.50/0.59  fof(f2063,plain,(
% 1.50/0.59    ( ! [X10,X8,X9] : (k4_xboole_0(k2_xboole_0(X8,X10),k2_xboole_0(X8,X9)) = k4_xboole_0(k2_xboole_0(k2_xboole_0(X8,X9),X10),k2_xboole_0(X8,X9))) )),
% 1.50/0.59    inference(superposition,[],[f462,f433])).
% 1.50/0.59  fof(f433,plain,(
% 1.50/0.59    ( ! [X2,X3] : (k2_xboole_0(X2,X3) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.50/0.59    inference(forward_demodulation,[],[f418,f39])).
% 1.50/0.59  fof(f418,plain,(
% 1.50/0.59    ( ! [X2,X3] : (k2_xboole_0(X2,k4_xboole_0(X3,X2)) = k2_xboole_0(X2,k2_xboole_0(X2,X3))) )),
% 1.50/0.59    inference(superposition,[],[f39,f129])).
% 1.50/0.59  fof(f462,plain,(
% 1.50/0.59    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X5,X6),X7),X6) = k4_xboole_0(k2_xboole_0(X5,X7),X6)) )),
% 1.50/0.59    inference(forward_demodulation,[],[f447,f46])).
% 1.50/0.59  fof(f447,plain,(
% 1.50/0.59    ( ! [X6,X7,X5] : (k4_xboole_0(k2_xboole_0(k2_xboole_0(X5,X6),X7),X6) = k2_xboole_0(k4_xboole_0(X5,X6),k4_xboole_0(X7,X6))) )),
% 1.50/0.59    inference(superposition,[],[f46,f131])).
% 1.50/0.59  fof(f2354,plain,(
% 1.50/0.59    ~r1_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,k4_xboole_0(sK2,sK0))),k4_xboole_0(k2_xboole_0(sK1,sK2),k2_xboole_0(sK1,k4_xboole_0(sK2,sK0)))) | (~spl4_21 | ~spl4_23)),
% 1.50/0.59    inference(backward_demodulation,[],[f1267,f2327])).
% 1.50/0.59  fof(f2327,plain,(
% 1.50/0.59    ( ! [X0] : (k4_xboole_0(k2_xboole_0(sK1,X0),sK0) = k2_xboole_0(sK1,k4_xboole_0(X0,sK0))) ) | ~spl4_23),
% 1.50/0.59    inference(superposition,[],[f46,f1499])).
% 1.50/0.59  fof(f1499,plain,(
% 1.50/0.59    sK1 = k4_xboole_0(sK1,sK0) | ~spl4_23),
% 1.50/0.59    inference(avatar_component_clause,[],[f1497])).
% 1.50/0.59  fof(f1497,plain,(
% 1.50/0.59    spl4_23 <=> sK1 = k4_xboole_0(sK1,sK0)),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 1.50/0.59  fof(f1267,plain,(
% 1.50/0.59    ~r1_xboole_0(k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0))) | ~spl4_21),
% 1.50/0.59    inference(unit_resulting_resolution,[],[f1259,f91])).
% 1.50/0.59  fof(f91,plain,(
% 1.50/0.59    ( ! [X2,X3] : (~r2_hidden(X3,X2) | ~r1_xboole_0(X2,X2)) )),
% 1.50/0.59    inference(forward_demodulation,[],[f89,f34])).
% 1.50/0.59  fof(f89,plain,(
% 1.50/0.59    ( ! [X2,X3] : (~r2_hidden(X3,k4_xboole_0(X2,k1_xboole_0)) | ~r1_xboole_0(X2,X2)) )),
% 1.50/0.59    inference(superposition,[],[f50,f54])).
% 1.50/0.59  fof(f50,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (~r2_hidden(X2,k4_xboole_0(X0,k4_xboole_0(X0,X1))) | ~r1_xboole_0(X0,X1)) )),
% 1.50/0.59    inference(definition_unfolding,[],[f42,f38])).
% 1.50/0.59  fof(f42,plain,(
% 1.50/0.59    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,k3_xboole_0(X0,X1))) )),
% 1.50/0.59    inference(cnf_transformation,[],[f25])).
% 1.50/0.59  fof(f25,plain,(
% 1.50/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.50/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f18,f24])).
% 1.50/0.59  fof(f24,plain,(
% 1.50/0.59    ! [X1,X0] : (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) => r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)))),
% 1.50/0.59    introduced(choice_axiom,[])).
% 1.50/0.59  fof(f18,plain,(
% 1.50/0.59    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 1.50/0.59    inference(ennf_transformation,[],[f16])).
% 1.50/0.59  fof(f16,plain,(
% 1.50/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.59    inference(rectify,[],[f4])).
% 1.50/0.59  fof(f4,axiom,(
% 1.50/0.59    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 1.50/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).
% 1.50/0.59  fof(f1259,plain,(
% 1.50/0.59    r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0))) | ~spl4_21),
% 1.50/0.59    inference(avatar_component_clause,[],[f1257])).
% 1.50/0.59  fof(f1257,plain,(
% 1.50/0.59    spl4_21 <=> r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0)))),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.50/0.59  fof(f1645,plain,(
% 1.50/0.59    spl4_25 | ~spl4_18),
% 1.50/0.59    inference(avatar_split_clause,[],[f896,f605,f1642])).
% 1.50/0.59  fof(f605,plain,(
% 1.50/0.59    spl4_18 <=> k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0))),
% 1.50/0.59    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.50/0.60  fof(f896,plain,(
% 1.50/0.60    sK2 = k4_xboole_0(sK2,sK0) | ~spl4_18),
% 1.50/0.60    inference(backward_demodulation,[],[f725,f873])).
% 1.50/0.60  fof(f873,plain,(
% 1.50/0.60    ( ! [X6,X7] : (k2_xboole_0(X6,k4_xboole_0(X6,X7)) = X6) )),
% 1.50/0.60    inference(superposition,[],[f475,f37])).
% 1.50/0.60  fof(f475,plain,(
% 1.50/0.60    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),X2) = X2) )),
% 1.50/0.60    inference(superposition,[],[f106,f39])).
% 1.50/0.60  fof(f106,plain,(
% 1.50/0.60    ( ! [X2,X3] : (k2_xboole_0(k4_xboole_0(X2,X3),k4_xboole_0(X2,k4_xboole_0(X2,X3))) = X2) )),
% 1.50/0.60    inference(superposition,[],[f49,f37])).
% 1.50/0.60  fof(f49,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k2_xboole_0(k4_xboole_0(X0,k4_xboole_0(X0,X1)),k4_xboole_0(X0,X1)) = X0) )),
% 1.50/0.60    inference(definition_unfolding,[],[f40,f38])).
% 1.50/0.60  fof(f40,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) )),
% 1.50/0.60    inference(cnf_transformation,[],[f11])).
% 1.50/0.60  fof(f11,axiom,(
% 1.50/0.60    ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).
% 1.50/0.60  fof(f725,plain,(
% 1.50/0.60    k4_xboole_0(sK2,sK0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_18),
% 1.50/0.60    inference(forward_demodulation,[],[f724,f35])).
% 1.50/0.60  fof(f724,plain,(
% 1.50/0.60    k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_18),
% 1.50/0.60    inference(forward_demodulation,[],[f711,f37])).
% 1.50/0.60  fof(f711,plain,(
% 1.50/0.60    k2_xboole_0(k4_xboole_0(sK2,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK2,sK0),sK2) | ~spl4_18),
% 1.50/0.60    inference(superposition,[],[f39,f607])).
% 1.50/0.60  fof(f607,plain,(
% 1.50/0.60    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_18),
% 1.50/0.60    inference(avatar_component_clause,[],[f605])).
% 1.50/0.60  fof(f1500,plain,(
% 1.50/0.60    spl4_23 | ~spl4_17),
% 1.50/0.60    inference(avatar_split_clause,[],[f895,f600,f1497])).
% 1.50/0.60  fof(f600,plain,(
% 1.50/0.60    spl4_17 <=> k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 1.50/0.60  fof(f895,plain,(
% 1.50/0.60    sK1 = k4_xboole_0(sK1,sK0) | ~spl4_17),
% 1.50/0.60    inference(backward_demodulation,[],[f694,f873])).
% 1.50/0.60  fof(f694,plain,(
% 1.50/0.60    k4_xboole_0(sK1,sK0) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl4_17),
% 1.50/0.60    inference(forward_demodulation,[],[f693,f35])).
% 1.50/0.60  fof(f693,plain,(
% 1.50/0.60    k2_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) = k2_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl4_17),
% 1.50/0.60    inference(forward_demodulation,[],[f680,f37])).
% 1.50/0.60  fof(f680,plain,(
% 1.50/0.60    k2_xboole_0(k4_xboole_0(sK1,sK0),k1_xboole_0) = k2_xboole_0(k4_xboole_0(sK1,sK0),sK1) | ~spl4_17),
% 1.50/0.60    inference(superposition,[],[f39,f602])).
% 1.50/0.60  fof(f602,plain,(
% 1.50/0.60    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl4_17),
% 1.50/0.60    inference(avatar_component_clause,[],[f600])).
% 1.50/0.60  fof(f1260,plain,(
% 1.50/0.60    spl4_21 | spl4_4),
% 1.50/0.60    inference(avatar_split_clause,[],[f225,f144,f1257])).
% 1.50/0.60  fof(f144,plain,(
% 1.50/0.60    spl4_4 <=> r1_xboole_0(k2_xboole_0(sK1,sK2),sK0)),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.50/0.60  fof(f225,plain,(
% 1.50/0.60    r2_hidden(sK3(k2_xboole_0(sK1,sK2),sK0),k4_xboole_0(k2_xboole_0(sK1,sK2),k4_xboole_0(k2_xboole_0(sK1,sK2),sK0))) | spl4_4),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f145,f51])).
% 1.50/0.60  fof(f51,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k4_xboole_0(X0,k4_xboole_0(X0,X1))) | r1_xboole_0(X0,X1)) )),
% 1.50/0.60    inference(definition_unfolding,[],[f41,f38])).
% 1.50/0.60  fof(f41,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f25])).
% 1.50/0.60  fof(f145,plain,(
% 1.50/0.60    ~r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | spl4_4),
% 1.50/0.60    inference(avatar_component_clause,[],[f144])).
% 1.50/0.60  fof(f608,plain,(
% 1.50/0.60    spl4_18 | ~spl4_6),
% 1.50/0.60    inference(avatar_split_clause,[],[f218,f176,f605])).
% 1.50/0.60  fof(f218,plain,(
% 1.50/0.60    k1_xboole_0 = k4_xboole_0(sK2,k4_xboole_0(sK2,sK0)) | ~spl4_6),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f177,f53])).
% 1.50/0.60  fof(f53,plain,(
% 1.50/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 1.50/0.60    inference(definition_unfolding,[],[f44,f38])).
% 1.50/0.60  fof(f44,plain,(
% 1.50/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f26])).
% 1.50/0.60  fof(f177,plain,(
% 1.50/0.60    r1_xboole_0(sK2,sK0) | ~spl4_6),
% 1.50/0.60    inference(avatar_component_clause,[],[f176])).
% 1.50/0.60  fof(f603,plain,(
% 1.50/0.60    spl4_17 | ~spl4_3),
% 1.50/0.60    inference(avatar_split_clause,[],[f168,f78,f600])).
% 1.50/0.60  fof(f168,plain,(
% 1.50/0.60    k1_xboole_0 = k4_xboole_0(sK1,k4_xboole_0(sK1,sK0)) | ~spl4_3),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f79,f53])).
% 1.50/0.60  fof(f79,plain,(
% 1.50/0.60    r1_xboole_0(sK1,sK0) | ~spl4_3),
% 1.50/0.60    inference(avatar_component_clause,[],[f78])).
% 1.50/0.60  fof(f205,plain,(
% 1.50/0.60    spl4_5 | spl4_2),
% 1.50/0.60    inference(avatar_split_clause,[],[f200,f61,f159])).
% 1.50/0.60  fof(f61,plain,(
% 1.50/0.60    spl4_2 <=> r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.50/0.60    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.50/0.60  fof(f200,plain,(
% 1.50/0.60    r1_xboole_0(sK0,sK2) | spl4_2),
% 1.50/0.60    inference(subsumption_resolution,[],[f32,f62])).
% 1.50/0.60  fof(f62,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | spl4_2),
% 1.50/0.60    inference(avatar_component_clause,[],[f61])).
% 1.50/0.60  fof(f32,plain,(
% 1.50/0.60    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK2)),
% 1.50/0.60    inference(cnf_transformation,[],[f23])).
% 1.50/0.60  fof(f23,plain,(
% 1.50/0.60    (r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)))),
% 1.50/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f22])).
% 1.50/0.60  fof(f22,plain,(
% 1.50/0.60    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2)))) => ((r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) & (~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1))) | (r1_xboole_0(sK0,sK2) & r1_xboole_0(sK0,sK1) & ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))))),
% 1.50/0.60    introduced(choice_axiom,[])).
% 1.50/0.60  fof(f17,plain,(
% 1.50/0.60    ? [X0,X1,X2] : ((r1_xboole_0(X0,k2_xboole_0(X1,X2)) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1))) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.50/0.60    inference(ennf_transformation,[],[f15])).
% 1.50/0.60  fof(f15,negated_conjecture,(
% 1.50/0.60    ~! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.50/0.60    inference(negated_conjecture,[],[f14])).
% 1.50/0.60  fof(f14,conjecture,(
% 1.50/0.60    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 1.50/0.60  fof(f204,plain,(
% 1.50/0.60    spl4_2 | ~spl4_4),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f203])).
% 1.50/0.60  fof(f203,plain,(
% 1.50/0.60    $false | (spl4_2 | ~spl4_4)),
% 1.50/0.60    inference(subsumption_resolution,[],[f191,f62])).
% 1.50/0.60  fof(f191,plain,(
% 1.50/0.60    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl4_4),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f146,f43])).
% 1.50/0.60  fof(f146,plain,(
% 1.50/0.60    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl4_4),
% 1.50/0.60    inference(avatar_component_clause,[],[f144])).
% 1.50/0.60  fof(f195,plain,(
% 1.50/0.60    ~spl4_4 | spl4_6),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f194])).
% 1.50/0.60  fof(f194,plain,(
% 1.50/0.60    $false | (~spl4_4 | spl4_6)),
% 1.50/0.60    inference(subsumption_resolution,[],[f188,f71])).
% 1.50/0.60  fof(f71,plain,(
% 1.50/0.60    ( ! [X2,X1] : (r1_tarski(X1,k2_xboole_0(X2,X1))) )),
% 1.50/0.60    inference(superposition,[],[f36,f37])).
% 1.50/0.60  fof(f36,plain,(
% 1.50/0.60    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 1.50/0.60    inference(cnf_transformation,[],[f13])).
% 1.50/0.60  fof(f13,axiom,(
% 1.50/0.60    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 1.50/0.60  fof(f188,plain,(
% 1.50/0.60    ~r1_tarski(sK2,k2_xboole_0(sK1,sK2)) | (~spl4_4 | spl4_6)),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f178,f146,f47])).
% 1.50/0.60  fof(f47,plain,(
% 1.50/0.60    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X1,X2) | r1_xboole_0(X0,X2)) )),
% 1.50/0.60    inference(cnf_transformation,[],[f21])).
% 1.50/0.60  fof(f21,plain,(
% 1.50/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 1.50/0.60    inference(flattening,[],[f20])).
% 1.50/0.60  fof(f20,plain,(
% 1.50/0.60    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 1.50/0.60    inference(ennf_transformation,[],[f12])).
% 1.50/0.60  fof(f12,axiom,(
% 1.50/0.60    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 1.50/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 1.50/0.60  fof(f179,plain,(
% 1.50/0.60    ~spl4_6 | spl4_5),
% 1.50/0.60    inference(avatar_split_clause,[],[f167,f159,f176])).
% 1.50/0.60  fof(f167,plain,(
% 1.50/0.60    ~r1_xboole_0(sK2,sK0) | spl4_5),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f161,f43])).
% 1.50/0.60  fof(f161,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,sK2) | spl4_5),
% 1.50/0.60    inference(avatar_component_clause,[],[f159])).
% 1.50/0.60  fof(f162,plain,(
% 1.50/0.60    ~spl4_1 | ~spl4_5 | ~spl4_2),
% 1.50/0.60    inference(avatar_split_clause,[],[f150,f61,f159,f57])).
% 1.50/0.60  fof(f150,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~spl4_2),
% 1.50/0.60    inference(subsumption_resolution,[],[f27,f63])).
% 1.50/0.60  fof(f63,plain,(
% 1.50/0.60    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | ~spl4_2),
% 1.50/0.60    inference(avatar_component_clause,[],[f61])).
% 1.50/0.60  fof(f27,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,sK2) | ~r1_xboole_0(sK0,sK1) | ~r1_xboole_0(sK0,k2_xboole_0(sK1,sK2))),
% 1.50/0.60    inference(cnf_transformation,[],[f23])).
% 1.50/0.60  fof(f149,plain,(
% 1.50/0.60    spl4_3 | ~spl4_4),
% 1.50/0.60    inference(avatar_contradiction_clause,[],[f148])).
% 1.50/0.60  fof(f148,plain,(
% 1.50/0.60    $false | (spl4_3 | ~spl4_4)),
% 1.50/0.60    inference(subsumption_resolution,[],[f146,f101])).
% 1.50/0.60  fof(f101,plain,(
% 1.50/0.60    ( ! [X0] : (~r1_xboole_0(k2_xboole_0(sK1,X0),sK0)) ) | spl4_3),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f36,f80,f47])).
% 1.50/0.60  fof(f147,plain,(
% 1.50/0.60    spl4_4 | ~spl4_2),
% 1.50/0.60    inference(avatar_split_clause,[],[f66,f61,f144])).
% 1.50/0.60  fof(f66,plain,(
% 1.50/0.60    r1_xboole_0(k2_xboole_0(sK1,sK2),sK0) | ~spl4_2),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f63,f43])).
% 1.50/0.60  fof(f81,plain,(
% 1.50/0.60    ~spl4_3 | spl4_1),
% 1.50/0.60    inference(avatar_split_clause,[],[f65,f57,f78])).
% 1.50/0.60  fof(f65,plain,(
% 1.50/0.60    ~r1_xboole_0(sK1,sK0) | spl4_1),
% 1.50/0.60    inference(unit_resulting_resolution,[],[f58,f43])).
% 1.50/0.60  fof(f58,plain,(
% 1.50/0.60    ~r1_xboole_0(sK0,sK1) | spl4_1),
% 1.50/0.60    inference(avatar_component_clause,[],[f57])).
% 1.50/0.60  fof(f64,plain,(
% 1.50/0.60    spl4_1 | spl4_2),
% 1.50/0.60    inference(avatar_split_clause,[],[f31,f61,f57])).
% 1.50/0.60  fof(f31,plain,(
% 1.50/0.60    r1_xboole_0(sK0,k2_xboole_0(sK1,sK2)) | r1_xboole_0(sK0,sK1)),
% 1.50/0.60    inference(cnf_transformation,[],[f23])).
% 1.50/0.60  % SZS output end Proof for theBenchmark
% 1.50/0.60  % (12891)------------------------------
% 1.50/0.60  % (12891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.50/0.60  % (12891)Termination reason: Refutation
% 1.50/0.60  
% 1.50/0.60  % (12891)Memory used [KB]: 12409
% 1.50/0.60  % (12891)Time elapsed: 0.175 s
% 1.50/0.60  % (12891)------------------------------
% 1.50/0.60  % (12891)------------------------------
% 1.50/0.60  % (12875)Success in time 0.245 s
%------------------------------------------------------------------------------
