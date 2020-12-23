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
% DateTime   : Thu Dec  3 12:30:08 EST 2020

% Result     : Theorem 2.54s
% Output     : Refutation 2.54s
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
fof(f3985,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f52,f56,f80,f88,f92,f96,f155,f181,f271,f328,f357,f1387,f2417,f3640,f3712,f3786])).

fof(f3786,plain,
    ( spl5_1
    | ~ spl5_124 ),
    inference(avatar_contradiction_clause,[],[f3713])).

fof(f3713,plain,
    ( $false
    | spl5_1
    | ~ spl5_124 ),
    inference(unit_resulting_resolution,[],[f43,f3711])).

fof(f3711,plain,
    ( ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_124 ),
    inference(avatar_component_clause,[],[f3710])).

fof(f3710,plain,
    ( spl5_124
  <=> ! [X5,X4] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).

fof(f43,plain,
    ( k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_1
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f3712,plain,
    ( spl5_124
    | ~ spl5_77
    | ~ spl5_97
    | ~ spl5_122 ),
    inference(avatar_split_clause,[],[f3674,f3638,f2415,f1385,f3710])).

fof(f1385,plain,
    ( spl5_77
  <=> ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f2415,plain,
    ( spl5_97
  <=> ! [X5,X4] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f3638,plain,
    ( spl5_122
  <=> ! [X18,X20,X19] :
        ( k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20)
        | ~ r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).

fof(f3674,plain,
    ( ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_77
    | ~ spl5_97
    | ~ spl5_122 ),
    inference(backward_demodulation,[],[f2416,f3671])).

fof(f3671,plain,
    ( ! [X4,X3] : k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))
    | ~ spl5_77
    | ~ spl5_122 ),
    inference(duplicate_literal_removal,[],[f3646])).

fof(f3646,plain,
    ( ! [X4,X3] :
        ( k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))
        | k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4)) )
    | ~ spl5_77
    | ~ spl5_122 ),
    inference(resolution,[],[f3639,f1386])).

fof(f1386,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK4(X1,X2,X1),X2)
        | k4_xboole_0(X1,X2) = X1 )
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f1385])).

fof(f3639,plain,
    ( ! [X19,X20,X18] :
        ( ~ r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19))
        | k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20) )
    | ~ spl5_122 ),
    inference(avatar_component_clause,[],[f3638])).

fof(f2416,plain,
    ( ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f2415])).

fof(f3640,plain,
    ( spl5_122
    | ~ spl5_31
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f348,f326,f269,f3638])).

fof(f269,plain,
    ( spl5_31
  <=> ! [X9,X7,X8] :
        ( ~ r2_hidden(X9,k4_xboole_0(X7,X8))
        | ~ r2_hidden(X9,k3_xboole_0(X7,X8)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f326,plain,
    ( spl5_38
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f348,plain,
    ( ! [X19,X20,X18] :
        ( k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20)
        | ~ r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)) )
    | ~ spl5_31
    | ~ spl5_38 ),
    inference(resolution,[],[f327,f270])).

fof(f270,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(X9,k3_xboole_0(X7,X8))
        | ~ r2_hidden(X9,k4_xboole_0(X7,X8)) )
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f269])).

fof(f327,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f326])).

fof(f2417,plain,
    ( spl5_97
    | ~ spl5_14
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f373,f355,f94,f2415])).

fof(f94,plain,
    ( spl5_14
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f355,plain,
    ( spl5_39
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f373,plain,
    ( ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_14
    | ~ spl5_39 ),
    inference(superposition,[],[f95,f356])).

fof(f356,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f355])).

fof(f95,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f1387,plain,
    ( spl5_77
    | ~ spl5_25
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f353,f326,f179,f1385])).

fof(f179,plain,
    ( spl5_25
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f353,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2) )
    | ~ spl5_25
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f351,f327])).

fof(f351,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2)
        | ~ r2_hidden(sK4(X1,X2,X1),X1) )
    | ~ spl5_25
    | ~ spl5_38 ),
    inference(duplicate_literal_removal,[],[f342])).

fof(f342,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2)
        | ~ r2_hidden(sK4(X1,X2,X1),X1)
        | k4_xboole_0(X1,X2) = X1 )
    | ~ spl5_25
    | ~ spl5_38 ),
    inference(resolution,[],[f327,f180])).

fof(f180,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f179])).

fof(f357,plain,
    ( spl5_39
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f125,f90,f86,f54,f50,f355])).

fof(f50,plain,
    ( spl5_3
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f54,plain,
    ( spl5_4
  <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f86,plain,
    ( spl5_12
  <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f90,plain,
    ( spl5_13
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f125,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f124,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f124,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f118,f51])).

fof(f51,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f118,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(superposition,[],[f87,f91])).

fof(f91,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f90])).

fof(f87,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f86])).

fof(f328,plain,
    ( spl5_38
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f171,f153,f326])).

fof(f153,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK4(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl5_21 ),
    inference(factoring,[],[f154])).

fof(f154,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f153])).

fof(f271,plain,
    ( spl5_31
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f121,f90,f78,f269])).

fof(f78,plain,
    ( spl5_10
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f121,plain,
    ( ! [X8,X7,X9] :
        ( ~ r2_hidden(X9,k4_xboole_0(X7,X8))
        | ~ r2_hidden(X9,k3_xboole_0(X7,X8)) )
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(superposition,[],[f79,f91])).

fof(f79,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f181,plain,(
    spl5_25 ),
    inference(avatar_split_clause,[],[f32,f179])).

fof(f32,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f155,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f33,f153])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X0)
      | r2_hidden(sK4(X0,X1,X2),X2)
      | k4_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f96,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f24,f94])).

fof(f24,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f92,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f23,f90])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f88,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f22,f86])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

fof(f80,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f36])).

fof(f36,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f56,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f21,f54])).

fof(f21,plain,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f52,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f44,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:19:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.52  % (20890)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.53  % (20898)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.53  % (20888)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.53  % (20899)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.54  % (20896)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (20899)Refutation not found, incomplete strategy% (20899)------------------------------
% 0.22/0.54  % (20899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20899)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20899)Memory used [KB]: 6140
% 0.22/0.54  % (20899)Time elapsed: 0.005 s
% 0.22/0.54  % (20899)------------------------------
% 0.22/0.54  % (20899)------------------------------
% 0.22/0.54  % (20891)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.54  % (20896)Refutation not found, incomplete strategy% (20896)------------------------------
% 0.22/0.54  % (20896)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (20896)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (20896)Memory used [KB]: 6012
% 0.22/0.54  % (20896)Time elapsed: 0.003 s
% 0.22/0.54  % (20896)------------------------------
% 0.22/0.54  % (20896)------------------------------
% 1.52/0.57  % (20889)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.71/0.57  % (20892)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 1.71/0.58  % (20893)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.71/0.58  % (20897)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 1.71/0.59  % (20887)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 1.71/0.59  % (20887)Refutation not found, incomplete strategy% (20887)------------------------------
% 1.71/0.59  % (20887)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (20887)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.59  
% 1.71/0.59  % (20887)Memory used [KB]: 10618
% 1.71/0.59  % (20887)Time elapsed: 0.127 s
% 1.71/0.59  % (20887)------------------------------
% 1.71/0.59  % (20887)------------------------------
% 1.71/0.59  % (20884)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 1.71/0.59  % (20884)Refutation not found, incomplete strategy% (20884)------------------------------
% 1.71/0.59  % (20884)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (20884)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.59  
% 1.71/0.59  % (20884)Memory used [KB]: 6140
% 1.71/0.59  % (20884)Time elapsed: 0.144 s
% 1.71/0.59  % (20884)------------------------------
% 1.71/0.59  % (20884)------------------------------
% 1.71/0.59  % (20885)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.71/0.59  % (20895)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 1.71/0.59  % (20904)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 1.71/0.59  % (20886)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 1.71/0.59  % (20885)Refutation not found, incomplete strategy% (20885)------------------------------
% 1.71/0.59  % (20885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.59  % (20885)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.59  
% 1.71/0.59  % (20885)Memory used [KB]: 10618
% 1.71/0.59  % (20885)Time elapsed: 0.143 s
% 1.71/0.59  % (20885)------------------------------
% 1.71/0.59  % (20885)------------------------------
% 1.71/0.60  % (20904)Refutation not found, incomplete strategy% (20904)------------------------------
% 1.71/0.60  % (20904)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.60  % (20895)Refutation not found, incomplete strategy% (20895)------------------------------
% 1.71/0.60  % (20895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.60  % (20904)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.60  
% 1.71/0.60  % (20895)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.60  
% 1.71/0.60  % (20904)Memory used [KB]: 10490
% 1.71/0.60  % (20895)Memory used [KB]: 10618
% 1.71/0.60  % (20904)Time elapsed: 0.150 s
% 1.71/0.60  % (20895)Time elapsed: 0.141 s
% 1.71/0.60  % (20904)------------------------------
% 1.71/0.60  % (20904)------------------------------
% 1.71/0.60  % (20895)------------------------------
% 1.71/0.60  % (20895)------------------------------
% 1.71/0.60  % (20897)Refutation not found, incomplete strategy% (20897)------------------------------
% 1.71/0.60  % (20897)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.60  % (20897)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.60  
% 1.71/0.60  % (20897)Memory used [KB]: 1535
% 1.71/0.60  % (20897)Time elapsed: 0.151 s
% 1.71/0.60  % (20897)------------------------------
% 1.71/0.60  % (20897)------------------------------
% 1.71/0.60  % (20903)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.71/0.61  % (20900)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 1.71/0.61  % (20894)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 1.71/0.61  % (20901)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.71/0.61  % (20894)Refutation not found, incomplete strategy% (20894)------------------------------
% 1.71/0.61  % (20894)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.71/0.61  % (20894)Termination reason: Refutation not found, incomplete strategy
% 1.71/0.61  
% 1.71/0.61  % (20894)Memory used [KB]: 6012
% 1.71/0.61  % (20894)Time elapsed: 0.168 s
% 1.71/0.61  % (20894)------------------------------
% 1.71/0.61  % (20894)------------------------------
% 1.71/0.63  % (20902)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 2.54/0.70  % (20893)Refutation found. Thanks to Tanya!
% 2.54/0.70  % SZS status Theorem for theBenchmark
% 2.54/0.70  % SZS output start Proof for theBenchmark
% 2.54/0.70  fof(f3985,plain,(
% 2.54/0.70    $false),
% 2.54/0.70    inference(avatar_sat_refutation,[],[f44,f52,f56,f80,f88,f92,f96,f155,f181,f271,f328,f357,f1387,f2417,f3640,f3712,f3786])).
% 2.54/0.70  fof(f3786,plain,(
% 2.54/0.70    spl5_1 | ~spl5_124),
% 2.54/0.70    inference(avatar_contradiction_clause,[],[f3713])).
% 2.54/0.70  fof(f3713,plain,(
% 2.54/0.70    $false | (spl5_1 | ~spl5_124)),
% 2.54/0.70    inference(unit_resulting_resolution,[],[f43,f3711])).
% 2.54/0.70  fof(f3711,plain,(
% 2.54/0.70    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl5_124),
% 2.54/0.70    inference(avatar_component_clause,[],[f3710])).
% 2.54/0.70  fof(f3710,plain,(
% 2.54/0.70    spl5_124 <=> ! [X5,X4] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_124])])).
% 2.54/0.70  fof(f43,plain,(
% 2.54/0.70    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl5_1),
% 2.54/0.70    inference(avatar_component_clause,[],[f42])).
% 2.54/0.70  fof(f42,plain,(
% 2.54/0.70    spl5_1 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 2.54/0.70  fof(f3712,plain,(
% 2.54/0.70    spl5_124 | ~spl5_77 | ~spl5_97 | ~spl5_122),
% 2.54/0.70    inference(avatar_split_clause,[],[f3674,f3638,f2415,f1385,f3710])).
% 2.54/0.70  fof(f1385,plain,(
% 2.54/0.70    spl5_77 <=> ! [X1,X2] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2))),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 2.54/0.70  fof(f2415,plain,(
% 2.54/0.70    spl5_97 <=> ! [X5,X4] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 2.54/0.70  fof(f3638,plain,(
% 2.54/0.70    spl5_122 <=> ! [X18,X20,X19] : (k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20) | ~r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)))),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_122])])).
% 2.54/0.70  fof(f3674,plain,(
% 2.54/0.70    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl5_77 | ~spl5_97 | ~spl5_122)),
% 2.54/0.70    inference(backward_demodulation,[],[f2416,f3671])).
% 2.54/0.70  fof(f3671,plain,(
% 2.54/0.70    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))) ) | (~spl5_77 | ~spl5_122)),
% 2.54/0.70    inference(duplicate_literal_removal,[],[f3646])).
% 2.54/0.70  fof(f3646,plain,(
% 2.54/0.70    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4)) | k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))) ) | (~spl5_77 | ~spl5_122)),
% 2.54/0.70    inference(resolution,[],[f3639,f1386])).
% 2.54/0.70  fof(f1386,plain,(
% 2.54/0.70    ( ! [X2,X1] : (r2_hidden(sK4(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) ) | ~spl5_77),
% 2.54/0.70    inference(avatar_component_clause,[],[f1385])).
% 2.54/0.70  fof(f3639,plain,(
% 2.54/0.70    ( ! [X19,X20,X18] : (~r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)) | k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20)) ) | ~spl5_122),
% 2.54/0.70    inference(avatar_component_clause,[],[f3638])).
% 2.54/0.70  fof(f2416,plain,(
% 2.54/0.70    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl5_97),
% 2.54/0.70    inference(avatar_component_clause,[],[f2415])).
% 2.54/0.70  fof(f3640,plain,(
% 2.54/0.70    spl5_122 | ~spl5_31 | ~spl5_38),
% 2.54/0.70    inference(avatar_split_clause,[],[f348,f326,f269,f3638])).
% 2.54/0.70  fof(f269,plain,(
% 2.54/0.70    spl5_31 <=> ! [X9,X7,X8] : (~r2_hidden(X9,k4_xboole_0(X7,X8)) | ~r2_hidden(X9,k3_xboole_0(X7,X8)))),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 2.54/0.70  fof(f326,plain,(
% 2.54/0.70    spl5_38 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0)),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 2.54/0.70  fof(f348,plain,(
% 2.54/0.70    ( ! [X19,X20,X18] : (k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20) | ~r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19))) ) | (~spl5_31 | ~spl5_38)),
% 2.54/0.70    inference(resolution,[],[f327,f270])).
% 2.54/0.70  fof(f270,plain,(
% 2.54/0.70    ( ! [X8,X7,X9] : (~r2_hidden(X9,k3_xboole_0(X7,X8)) | ~r2_hidden(X9,k4_xboole_0(X7,X8))) ) | ~spl5_31),
% 2.54/0.70    inference(avatar_component_clause,[],[f269])).
% 2.54/0.70  fof(f327,plain,(
% 2.54/0.70    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl5_38),
% 2.54/0.70    inference(avatar_component_clause,[],[f326])).
% 2.54/0.70  fof(f2417,plain,(
% 2.54/0.70    spl5_97 | ~spl5_14 | ~spl5_39),
% 2.54/0.70    inference(avatar_split_clause,[],[f373,f355,f94,f2415])).
% 2.54/0.70  fof(f94,plain,(
% 2.54/0.70    spl5_14 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 2.54/0.70  fof(f355,plain,(
% 2.54/0.70    spl5_39 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 2.54/0.70  fof(f373,plain,(
% 2.54/0.70    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl5_14 | ~spl5_39)),
% 2.54/0.70    inference(superposition,[],[f95,f356])).
% 2.54/0.70  fof(f356,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl5_39),
% 2.54/0.70    inference(avatar_component_clause,[],[f355])).
% 2.54/0.70  fof(f95,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl5_14),
% 2.54/0.70    inference(avatar_component_clause,[],[f94])).
% 2.54/0.70  fof(f1387,plain,(
% 2.54/0.70    spl5_77 | ~spl5_25 | ~spl5_38),
% 2.54/0.70    inference(avatar_split_clause,[],[f353,f326,f179,f1385])).
% 2.54/0.70  fof(f179,plain,(
% 2.54/0.70    spl5_25 <=> ! [X1,X0,X2] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 2.54/0.70  fof(f353,plain,(
% 2.54/0.70    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2)) ) | (~spl5_25 | ~spl5_38)),
% 2.54/0.70    inference(subsumption_resolution,[],[f351,f327])).
% 2.54/0.70  fof(f351,plain,(
% 2.54/0.70    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1)) ) | (~spl5_25 | ~spl5_38)),
% 2.54/0.70    inference(duplicate_literal_removal,[],[f342])).
% 2.54/0.70  fof(f342,plain,(
% 2.54/0.70    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1) | k4_xboole_0(X1,X2) = X1) ) | (~spl5_25 | ~spl5_38)),
% 2.54/0.70    inference(resolution,[],[f327,f180])).
% 2.54/0.70  fof(f180,plain,(
% 2.54/0.70    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl5_25),
% 2.54/0.70    inference(avatar_component_clause,[],[f179])).
% 2.54/0.70  fof(f357,plain,(
% 2.54/0.70    spl5_39 | ~spl5_3 | ~spl5_4 | ~spl5_12 | ~spl5_13),
% 2.54/0.70    inference(avatar_split_clause,[],[f125,f90,f86,f54,f50,f355])).
% 2.54/0.70  fof(f50,plain,(
% 2.54/0.70    spl5_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 2.54/0.70  fof(f54,plain,(
% 2.54/0.70    spl5_4 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 2.54/0.70  fof(f86,plain,(
% 2.54/0.70    spl5_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 2.54/0.70  fof(f90,plain,(
% 2.54/0.70    spl5_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 2.54/0.70  fof(f125,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | (~spl5_3 | ~spl5_4 | ~spl5_12 | ~spl5_13)),
% 2.54/0.70    inference(forward_demodulation,[],[f124,f55])).
% 2.54/0.70  fof(f55,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl5_4),
% 2.54/0.70    inference(avatar_component_clause,[],[f54])).
% 2.54/0.70  fof(f124,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl5_3 | ~spl5_12 | ~spl5_13)),
% 2.54/0.70    inference(forward_demodulation,[],[f118,f51])).
% 2.54/0.70  fof(f51,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_3),
% 2.54/0.70    inference(avatar_component_clause,[],[f50])).
% 2.54/0.70  fof(f118,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl5_12 | ~spl5_13)),
% 2.54/0.70    inference(superposition,[],[f87,f91])).
% 2.54/0.70  fof(f91,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl5_13),
% 2.54/0.70    inference(avatar_component_clause,[],[f90])).
% 2.54/0.70  fof(f87,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl5_12),
% 2.54/0.70    inference(avatar_component_clause,[],[f86])).
% 2.54/0.70  fof(f328,plain,(
% 2.54/0.70    spl5_38 | ~spl5_21),
% 2.54/0.70    inference(avatar_split_clause,[],[f171,f153,f326])).
% 2.54/0.70  fof(f153,plain,(
% 2.54/0.70    spl5_21 <=> ! [X1,X0,X2] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 2.54/0.70  fof(f171,plain,(
% 2.54/0.70    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl5_21),
% 2.54/0.70    inference(factoring,[],[f154])).
% 2.54/0.70  fof(f154,plain,(
% 2.54/0.70    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl5_21),
% 2.54/0.70    inference(avatar_component_clause,[],[f153])).
% 2.54/0.70  fof(f271,plain,(
% 2.54/0.70    spl5_31 | ~spl5_10 | ~spl5_13),
% 2.54/0.70    inference(avatar_split_clause,[],[f121,f90,f78,f269])).
% 2.54/0.70  fof(f78,plain,(
% 2.54/0.70    spl5_10 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 2.54/0.70    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 2.54/0.70  fof(f121,plain,(
% 2.54/0.70    ( ! [X8,X7,X9] : (~r2_hidden(X9,k4_xboole_0(X7,X8)) | ~r2_hidden(X9,k3_xboole_0(X7,X8))) ) | (~spl5_10 | ~spl5_13)),
% 2.54/0.70    inference(superposition,[],[f79,f91])).
% 2.54/0.70  fof(f79,plain,(
% 2.54/0.70    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) ) | ~spl5_10),
% 2.54/0.70    inference(avatar_component_clause,[],[f78])).
% 2.54/0.70  fof(f181,plain,(
% 2.54/0.70    spl5_25),
% 2.54/0.70    inference(avatar_split_clause,[],[f32,f179])).
% 2.54/0.70  fof(f32,plain,(
% 2.54/0.70    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.54/0.70    inference(cnf_transformation,[],[f2])).
% 2.54/0.70  fof(f2,axiom,(
% 2.54/0.70    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 2.54/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 2.54/0.70  fof(f155,plain,(
% 2.54/0.70    spl5_21),
% 2.54/0.70    inference(avatar_split_clause,[],[f33,f153])).
% 2.54/0.70  fof(f33,plain,(
% 2.54/0.70    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 2.54/0.70    inference(cnf_transformation,[],[f2])).
% 2.54/0.70  fof(f96,plain,(
% 2.54/0.70    spl5_14),
% 2.54/0.70    inference(avatar_split_clause,[],[f24,f94])).
% 2.54/0.70  fof(f24,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 2.54/0.70    inference(cnf_transformation,[],[f9])).
% 2.54/0.70  fof(f9,axiom,(
% 2.54/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 2.54/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).
% 2.54/0.70  fof(f92,plain,(
% 2.54/0.70    spl5_13),
% 2.54/0.70    inference(avatar_split_clause,[],[f23,f90])).
% 2.54/0.70  fof(f23,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 2.54/0.70    inference(cnf_transformation,[],[f10])).
% 2.54/0.70  fof(f10,axiom,(
% 2.54/0.70    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 2.54/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).
% 2.54/0.70  fof(f88,plain,(
% 2.54/0.70    spl5_12),
% 2.54/0.70    inference(avatar_split_clause,[],[f22,f86])).
% 2.54/0.70  fof(f22,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 2.54/0.70    inference(cnf_transformation,[],[f8])).
% 2.54/0.70  fof(f8,axiom,(
% 2.54/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 2.54/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).
% 2.54/0.70  fof(f80,plain,(
% 2.54/0.70    spl5_10),
% 2.54/0.70    inference(avatar_split_clause,[],[f39,f78])).
% 2.54/0.70  fof(f39,plain,(
% 2.54/0.70    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 2.54/0.70    inference(equality_resolution,[],[f36])).
% 2.54/0.70  fof(f36,plain,(
% 2.54/0.70    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 2.54/0.70    inference(cnf_transformation,[],[f2])).
% 2.54/0.70  fof(f56,plain,(
% 2.54/0.70    spl5_4),
% 2.54/0.70    inference(avatar_split_clause,[],[f21,f54])).
% 2.54/0.70  fof(f21,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 2.54/0.70    inference(cnf_transformation,[],[f6])).
% 2.54/0.70  fof(f6,axiom,(
% 2.54/0.70    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 2.54/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).
% 2.54/0.70  fof(f52,plain,(
% 2.54/0.70    spl5_3),
% 2.54/0.70    inference(avatar_split_clause,[],[f20,f50])).
% 2.54/0.70  fof(f20,plain,(
% 2.54/0.70    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 2.54/0.70    inference(cnf_transformation,[],[f1])).
% 2.54/0.70  fof(f1,axiom,(
% 2.54/0.70    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 2.54/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 2.54/0.70  fof(f44,plain,(
% 2.54/0.70    ~spl5_1),
% 2.54/0.70    inference(avatar_split_clause,[],[f18,f42])).
% 2.54/0.70  fof(f18,plain,(
% 2.54/0.70    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 2.54/0.70    inference(cnf_transformation,[],[f15])).
% 2.54/0.70  fof(f15,plain,(
% 2.54/0.70    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.54/0.70    inference(ennf_transformation,[],[f12])).
% 2.54/0.70  fof(f12,negated_conjecture,(
% 2.54/0.70    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.54/0.70    inference(negated_conjecture,[],[f11])).
% 2.54/0.70  fof(f11,conjecture,(
% 2.54/0.70    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 2.54/0.70    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 2.54/0.70  % SZS output end Proof for theBenchmark
% 2.54/0.70  % (20893)------------------------------
% 2.54/0.70  % (20893)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.54/0.70  % (20893)Termination reason: Refutation
% 2.54/0.70  
% 2.54/0.70  % (20893)Memory used [KB]: 13304
% 2.54/0.70  % (20893)Time elapsed: 0.253 s
% 2.54/0.70  % (20893)------------------------------
% 2.54/0.70  % (20893)------------------------------
% 2.54/0.70  % (20883)Success in time 0.338 s
%------------------------------------------------------------------------------
