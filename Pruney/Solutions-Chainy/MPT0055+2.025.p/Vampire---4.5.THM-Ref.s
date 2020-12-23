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
fof(f2904,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f52,f56,f80,f88,f92,f96,f150,f186,f244,f314,f336,f850,f1472,f2513,f2678,f2739])).

fof(f2739,plain,
    ( spl5_1
    | ~ spl5_104 ),
    inference(avatar_contradiction_clause,[],[f2679])).

fof(f2679,plain,
    ( $false
    | spl5_1
    | ~ spl5_104 ),
    inference(unit_resulting_resolution,[],[f43,f2677])).

fof(f2677,plain,
    ( ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_104 ),
    inference(avatar_component_clause,[],[f2676])).

fof(f2676,plain,
    ( spl5_104
  <=> ! [X5,X4] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).

fof(f43,plain,
    ( k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f42])).

fof(f42,plain,
    ( spl5_1
  <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f2678,plain,
    ( spl5_104
    | ~ spl5_60
    | ~ spl5_77
    | ~ spl5_102 ),
    inference(avatar_split_clause,[],[f2639,f2511,f1470,f848,f2676])).

fof(f848,plain,
    ( spl5_60
  <=> ! [X1,X2] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f1470,plain,
    ( spl5_77
  <=> ! [X5,X4] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).

fof(f2511,plain,
    ( spl5_102
  <=> ! [X18,X20,X19] :
        ( k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20)
        | ~ r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).

fof(f2639,plain,
    ( ! [X4,X5] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_60
    | ~ spl5_77
    | ~ spl5_102 ),
    inference(backward_demodulation,[],[f1471,f2636])).

fof(f2636,plain,
    ( ! [X4,X3] : k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))
    | ~ spl5_60
    | ~ spl5_102 ),
    inference(duplicate_literal_removal,[],[f2618])).

fof(f2618,plain,
    ( ! [X4,X3] :
        ( k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))
        | k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4)) )
    | ~ spl5_60
    | ~ spl5_102 ),
    inference(resolution,[],[f2512,f849])).

fof(f849,plain,
    ( ! [X2,X1] :
        ( r2_hidden(sK4(X1,X2,X1),X2)
        | k4_xboole_0(X1,X2) = X1 )
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f848])).

fof(f2512,plain,
    ( ! [X19,X20,X18] :
        ( ~ r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19))
        | k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20) )
    | ~ spl5_102 ),
    inference(avatar_component_clause,[],[f2511])).

fof(f1471,plain,
    ( ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_77 ),
    inference(avatar_component_clause,[],[f1470])).

fof(f2513,plain,
    ( spl5_102
    | ~ spl5_30
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f326,f312,f242,f2511])).

fof(f242,plain,
    ( spl5_30
  <=> ! [X5,X7,X6] :
        ( ~ r2_hidden(X7,k4_xboole_0(X5,X6))
        | ~ r2_hidden(X7,k3_xboole_0(X5,X6)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f312,plain,
    ( spl5_36
  <=> ! [X1,X0] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f326,plain,
    ( ! [X19,X20,X18] :
        ( k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20)
        | ~ r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)) )
    | ~ spl5_30
    | ~ spl5_36 ),
    inference(resolution,[],[f313,f243])).

fof(f243,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(X7,k3_xboole_0(X5,X6))
        | ~ r2_hidden(X7,k4_xboole_0(X5,X6)) )
    | ~ spl5_30 ),
    inference(avatar_component_clause,[],[f242])).

fof(f313,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f312])).

fof(f1472,plain,
    ( spl5_77
    | ~ spl5_14
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f347,f334,f94,f1470])).

fof(f94,plain,
    ( spl5_14
  <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f334,plain,
    ( spl5_38
  <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f347,plain,
    ( ! [X4,X5] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))
    | ~ spl5_14
    | ~ spl5_38 ),
    inference(superposition,[],[f95,f335])).

fof(f335,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f334])).

fof(f95,plain,
    ( ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f94])).

fof(f850,plain,
    ( spl5_60
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(avatar_split_clause,[],[f331,f312,f184,f848])).

fof(f184,plain,
    ( spl5_25
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f331,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2) )
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(subsumption_resolution,[],[f329,f313])).

fof(f329,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2)
        | ~ r2_hidden(sK4(X1,X2,X1),X1) )
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ! [X2,X1] :
        ( k4_xboole_0(X1,X2) = X1
        | r2_hidden(sK4(X1,X2,X1),X2)
        | ~ r2_hidden(sK4(X1,X2,X1),X1)
        | k4_xboole_0(X1,X2) = X1 )
    | ~ spl5_25
    | ~ spl5_36 ),
    inference(resolution,[],[f313,f185])).

fof(f185,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X1)
        | ~ r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f184])).

fof(f336,plain,
    ( spl5_38
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f122,f90,f86,f54,f50,f334])).

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

fof(f122,plain,
    ( ! [X0,X1] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f121,f55])).

fof(f55,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f121,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))
    | ~ spl5_3
    | ~ spl5_12
    | ~ spl5_13 ),
    inference(forward_demodulation,[],[f117,f51])).

fof(f51,plain,
    ( ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f50])).

fof(f117,plain,
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

fof(f314,plain,
    ( spl5_36
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f176,f148,f312])).

fof(f148,plain,
    ( spl5_21
  <=> ! [X1,X0,X2] :
        ( r2_hidden(sK4(X0,X1,X2),X0)
        | r2_hidden(sK4(X0,X1,X2),X2)
        | k4_xboole_0(X0,X1) = X2 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f176,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,X0),X0)
        | k4_xboole_0(X0,X1) = X0 )
    | ~ spl5_21 ),
    inference(factoring,[],[f149])).

fof(f149,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(sK4(X0,X1,X2),X2)
        | r2_hidden(sK4(X0,X1,X2),X0)
        | k4_xboole_0(X0,X1) = X2 )
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f148])).

fof(f244,plain,
    ( spl5_30
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f119,f90,f78,f242])).

fof(f78,plain,
    ( spl5_10
  <=> ! [X1,X3,X0] :
        ( ~ r2_hidden(X3,X1)
        | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f119,plain,
    ( ! [X6,X7,X5] :
        ( ~ r2_hidden(X7,k4_xboole_0(X5,X6))
        | ~ r2_hidden(X7,k3_xboole_0(X5,X6)) )
    | ~ spl5_10
    | ~ spl5_13 ),
    inference(superposition,[],[f79,f91])).

fof(f79,plain,
    ( ! [X0,X3,X1] :
        ( ~ r2_hidden(X3,k4_xboole_0(X0,X1))
        | ~ r2_hidden(X3,X1) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f78])).

fof(f186,plain,(
    spl5_25 ),
    inference(avatar_split_clause,[],[f32,f184])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f150,plain,(
    spl5_21 ),
    inference(avatar_split_clause,[],[f33,f148])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

fof(f92,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f23,f90])).

fof(f23,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

fof(f88,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f22,f86])).

fof(f22,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

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
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

fof(f52,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f20,f50])).

fof(f20,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:06:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.45  % (7735)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.47  % (7743)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.47  % (7737)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (7729)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (7743)Refutation not found, incomplete strategy% (7743)------------------------------
% 0.21/0.48  % (7743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (7743)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (7743)Memory used [KB]: 6140
% 0.21/0.48  % (7743)Time elapsed: 0.067 s
% 0.21/0.48  % (7743)------------------------------
% 0.21/0.48  % (7743)------------------------------
% 0.21/0.49  % (7728)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (7728)Refutation not found, incomplete strategy% (7728)------------------------------
% 0.21/0.50  % (7728)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7728)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7728)Memory used [KB]: 6140
% 0.21/0.50  % (7728)Time elapsed: 0.071 s
% 0.21/0.50  % (7728)------------------------------
% 0.21/0.50  % (7728)------------------------------
% 0.21/0.50  % (7732)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (7729)Refutation not found, incomplete strategy% (7729)------------------------------
% 0.21/0.50  % (7729)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (7729)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (7729)Memory used [KB]: 10618
% 0.21/0.50  % (7729)Time elapsed: 0.070 s
% 0.21/0.50  % (7729)------------------------------
% 0.21/0.50  % (7729)------------------------------
% 0.21/0.50  % (7742)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (7733)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.50  % (7745)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (7736)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.51  % (7730)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (7741)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.51  % (7741)Refutation not found, incomplete strategy% (7741)------------------------------
% 0.21/0.51  % (7741)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7741)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7741)Memory used [KB]: 1535
% 0.21/0.51  % (7741)Time elapsed: 0.093 s
% 0.21/0.51  % (7741)------------------------------
% 0.21/0.51  % (7741)------------------------------
% 0.21/0.51  % (7747)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (7748)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (7738)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (7734)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.51  % (7738)Refutation not found, incomplete strategy% (7738)------------------------------
% 0.21/0.51  % (7738)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7738)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7738)Memory used [KB]: 6012
% 0.21/0.51  % (7738)Time elapsed: 0.094 s
% 0.21/0.51  % (7738)------------------------------
% 0.21/0.51  % (7738)------------------------------
% 0.21/0.51  % (7748)Refutation not found, incomplete strategy% (7748)------------------------------
% 0.21/0.51  % (7748)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7748)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7748)Memory used [KB]: 10490
% 0.21/0.51  % (7748)Time elapsed: 0.097 s
% 0.21/0.51  % (7748)------------------------------
% 0.21/0.51  % (7748)------------------------------
% 0.21/0.51  % (7744)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (7731)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (7740)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (7746)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (7740)Refutation not found, incomplete strategy% (7740)------------------------------
% 0.21/0.52  % (7740)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7740)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7740)Memory used [KB]: 6012
% 0.21/0.52  % (7740)Time elapsed: 0.001 s
% 0.21/0.52  % (7740)------------------------------
% 0.21/0.52  % (7740)------------------------------
% 0.21/0.52  % (7731)Refutation not found, incomplete strategy% (7731)------------------------------
% 0.21/0.52  % (7731)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7731)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7731)Memory used [KB]: 10618
% 0.21/0.52  % (7731)Time elapsed: 0.091 s
% 0.21/0.52  % (7731)------------------------------
% 0.21/0.52  % (7731)------------------------------
% 0.21/0.52  % (7739)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (7739)Refutation not found, incomplete strategy% (7739)------------------------------
% 0.21/0.52  % (7739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7739)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (7739)Memory used [KB]: 10618
% 0.21/0.52  % (7739)Time elapsed: 0.105 s
% 0.21/0.52  % (7739)------------------------------
% 0.21/0.52  % (7739)------------------------------
% 0.21/0.54  % (7737)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.54  fof(f2904,plain,(
% 0.21/0.54    $false),
% 0.21/0.54    inference(avatar_sat_refutation,[],[f44,f52,f56,f80,f88,f92,f96,f150,f186,f244,f314,f336,f850,f1472,f2513,f2678,f2739])).
% 0.21/0.54  fof(f2739,plain,(
% 0.21/0.54    spl5_1 | ~spl5_104),
% 0.21/0.54    inference(avatar_contradiction_clause,[],[f2679])).
% 0.21/0.54  fof(f2679,plain,(
% 0.21/0.54    $false | (spl5_1 | ~spl5_104)),
% 0.21/0.54    inference(unit_resulting_resolution,[],[f43,f2677])).
% 0.21/0.54  fof(f2677,plain,(
% 0.21/0.54    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl5_104),
% 0.21/0.54    inference(avatar_component_clause,[],[f2676])).
% 0.21/0.54  fof(f2676,plain,(
% 0.21/0.54    spl5_104 <=> ! [X5,X4] : k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_104])])).
% 0.21/0.54  fof(f43,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1)) | spl5_1),
% 0.21/0.54    inference(avatar_component_clause,[],[f42])).
% 0.21/0.54  fof(f42,plain,(
% 0.21/0.54    spl5_1 <=> k3_xboole_0(sK0,sK1) = k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.54  fof(f2678,plain,(
% 0.21/0.54    spl5_104 | ~spl5_60 | ~spl5_77 | ~spl5_102),
% 0.21/0.54    inference(avatar_split_clause,[],[f2639,f2511,f1470,f848,f2676])).
% 0.21/0.54  fof(f848,plain,(
% 0.21/0.54    spl5_60 <=> ! [X1,X2] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.21/0.54  fof(f1470,plain,(
% 0.21/0.54    spl5_77 <=> ! [X5,X4] : k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_77])])).
% 0.21/0.54  fof(f2511,plain,(
% 0.21/0.54    spl5_102 <=> ! [X18,X20,X19] : (k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20) | ~r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_102])])).
% 0.21/0.54  fof(f2639,plain,(
% 0.21/0.54    ( ! [X4,X5] : (k3_xboole_0(X4,X5) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl5_60 | ~spl5_77 | ~spl5_102)),
% 0.21/0.54    inference(backward_demodulation,[],[f1471,f2636])).
% 0.21/0.54  fof(f2636,plain,(
% 0.21/0.54    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))) ) | (~spl5_60 | ~spl5_102)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f2618])).
% 0.21/0.54  fof(f2618,plain,(
% 0.21/0.54    ( ! [X4,X3] : (k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4)) | k3_xboole_0(X3,X4) = k4_xboole_0(k3_xboole_0(X3,X4),k4_xboole_0(X3,X4))) ) | (~spl5_60 | ~spl5_102)),
% 0.21/0.54    inference(resolution,[],[f2512,f849])).
% 0.21/0.54  fof(f849,plain,(
% 0.21/0.54    ( ! [X2,X1] : (r2_hidden(sK4(X1,X2,X1),X2) | k4_xboole_0(X1,X2) = X1) ) | ~spl5_60),
% 0.21/0.54    inference(avatar_component_clause,[],[f848])).
% 0.21/0.54  fof(f2512,plain,(
% 0.21/0.54    ( ! [X19,X20,X18] : (~r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19)) | k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20)) ) | ~spl5_102),
% 0.21/0.54    inference(avatar_component_clause,[],[f2511])).
% 0.21/0.54  fof(f1471,plain,(
% 0.21/0.54    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | ~spl5_77),
% 0.21/0.54    inference(avatar_component_clause,[],[f1470])).
% 0.21/0.54  fof(f2513,plain,(
% 0.21/0.54    spl5_102 | ~spl5_30 | ~spl5_36),
% 0.21/0.54    inference(avatar_split_clause,[],[f326,f312,f242,f2511])).
% 0.21/0.54  fof(f242,plain,(
% 0.21/0.54    spl5_30 <=> ! [X5,X7,X6] : (~r2_hidden(X7,k4_xboole_0(X5,X6)) | ~r2_hidden(X7,k3_xboole_0(X5,X6)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.54  fof(f312,plain,(
% 0.21/0.54    spl5_36 <=> ! [X1,X0] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.54  fof(f326,plain,(
% 0.21/0.54    ( ! [X19,X20,X18] : (k3_xboole_0(X18,X19) = k4_xboole_0(k3_xboole_0(X18,X19),X20) | ~r2_hidden(sK4(k3_xboole_0(X18,X19),X20,k3_xboole_0(X18,X19)),k4_xboole_0(X18,X19))) ) | (~spl5_30 | ~spl5_36)),
% 0.21/0.54    inference(resolution,[],[f313,f243])).
% 0.21/0.54  fof(f243,plain,(
% 0.21/0.54    ( ! [X6,X7,X5] : (~r2_hidden(X7,k3_xboole_0(X5,X6)) | ~r2_hidden(X7,k4_xboole_0(X5,X6))) ) | ~spl5_30),
% 0.21/0.54    inference(avatar_component_clause,[],[f242])).
% 0.21/0.54  fof(f313,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl5_36),
% 0.21/0.54    inference(avatar_component_clause,[],[f312])).
% 0.21/0.54  fof(f1472,plain,(
% 0.21/0.54    spl5_77 | ~spl5_14 | ~spl5_38),
% 0.21/0.54    inference(avatar_split_clause,[],[f347,f334,f94,f1470])).
% 0.21/0.54  fof(f94,plain,(
% 0.21/0.54    spl5_14 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.54  fof(f334,plain,(
% 0.21/0.54    spl5_38 <=> ! [X1,X0] : k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.21/0.54  fof(f347,plain,(
% 0.21/0.54    ( ! [X4,X5] : (k4_xboole_0(k3_xboole_0(X4,X5),k4_xboole_0(X4,X5)) = k4_xboole_0(X4,k4_xboole_0(X4,X5))) ) | (~spl5_14 | ~spl5_38)),
% 0.21/0.54    inference(superposition,[],[f95,f335])).
% 0.21/0.54  fof(f335,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | ~spl5_38),
% 0.21/0.54    inference(avatar_component_clause,[],[f334])).
% 0.21/0.54  fof(f95,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) ) | ~spl5_14),
% 0.21/0.54    inference(avatar_component_clause,[],[f94])).
% 0.21/0.54  fof(f850,plain,(
% 0.21/0.54    spl5_60 | ~spl5_25 | ~spl5_36),
% 0.21/0.54    inference(avatar_split_clause,[],[f331,f312,f184,f848])).
% 0.21/0.54  fof(f184,plain,(
% 0.21/0.54    spl5_25 <=> ! [X1,X0,X2] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.54  fof(f331,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2)) ) | (~spl5_25 | ~spl5_36)),
% 0.21/0.54    inference(subsumption_resolution,[],[f329,f313])).
% 0.21/0.54  fof(f329,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1)) ) | (~spl5_25 | ~spl5_36)),
% 0.21/0.54    inference(duplicate_literal_removal,[],[f320])).
% 0.21/0.54  fof(f320,plain,(
% 0.21/0.54    ( ! [X2,X1] : (k4_xboole_0(X1,X2) = X1 | r2_hidden(sK4(X1,X2,X1),X2) | ~r2_hidden(sK4(X1,X2,X1),X1) | k4_xboole_0(X1,X2) = X1) ) | (~spl5_25 | ~spl5_36)),
% 0.21/0.54    inference(resolution,[],[f313,f185])).
% 0.21/0.54  fof(f185,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl5_25),
% 0.21/0.54    inference(avatar_component_clause,[],[f184])).
% 0.21/0.54  fof(f336,plain,(
% 0.21/0.54    spl5_38 | ~spl5_3 | ~spl5_4 | ~spl5_12 | ~spl5_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f122,f90,f86,f54,f50,f334])).
% 0.21/0.54  fof(f50,plain,(
% 0.21/0.54    spl5_3 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.54  fof(f54,plain,(
% 0.21/0.54    spl5_4 <=> ! [X1,X0] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.54  fof(f86,plain,(
% 0.21/0.54    spl5_12 <=> ! [X1,X0] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.54  fof(f90,plain,(
% 0.21/0.54    spl5_13 <=> ! [X1,X0] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.54  fof(f122,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1)) = X0) ) | (~spl5_3 | ~spl5_4 | ~spl5_12 | ~spl5_13)),
% 0.21/0.54    inference(forward_demodulation,[],[f121,f55])).
% 0.21/0.54  fof(f55,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) ) | ~spl5_4),
% 0.21/0.54    inference(avatar_component_clause,[],[f54])).
% 0.21/0.54  fof(f121,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl5_3 | ~spl5_12 | ~spl5_13)),
% 0.21/0.54    inference(forward_demodulation,[],[f117,f51])).
% 0.21/0.54  fof(f51,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) ) | ~spl5_3),
% 0.21/0.54    inference(avatar_component_clause,[],[f50])).
% 0.21/0.54  fof(f117,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(k3_xboole_0(X0,X1),X0) = k2_xboole_0(k3_xboole_0(X0,X1),k4_xboole_0(X0,X1))) ) | (~spl5_12 | ~spl5_13)),
% 0.21/0.54    inference(superposition,[],[f87,f91])).
% 0.21/0.54  fof(f91,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) ) | ~spl5_13),
% 0.21/0.54    inference(avatar_component_clause,[],[f90])).
% 0.21/0.54  fof(f87,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) ) | ~spl5_12),
% 0.21/0.54    inference(avatar_component_clause,[],[f86])).
% 0.21/0.54  fof(f314,plain,(
% 0.21/0.54    spl5_36 | ~spl5_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f176,f148,f312])).
% 0.21/0.54  fof(f148,plain,(
% 0.21/0.54    spl5_21 <=> ! [X1,X0,X2] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2)),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.54  fof(f176,plain,(
% 0.21/0.54    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1,X0),X0) | k4_xboole_0(X0,X1) = X0) ) | ~spl5_21),
% 0.21/0.54    inference(factoring,[],[f149])).
% 0.21/0.54  fof(f149,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X2) | r2_hidden(sK4(X0,X1,X2),X0) | k4_xboole_0(X0,X1) = X2) ) | ~spl5_21),
% 0.21/0.54    inference(avatar_component_clause,[],[f148])).
% 0.21/0.54  fof(f244,plain,(
% 0.21/0.54    spl5_30 | ~spl5_10 | ~spl5_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f119,f90,f78,f242])).
% 0.21/0.54  fof(f78,plain,(
% 0.21/0.54    spl5_10 <=> ! [X1,X3,X0] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1)))),
% 0.21/0.54    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.54  fof(f119,plain,(
% 0.21/0.54    ( ! [X6,X7,X5] : (~r2_hidden(X7,k4_xboole_0(X5,X6)) | ~r2_hidden(X7,k3_xboole_0(X5,X6))) ) | (~spl5_10 | ~spl5_13)),
% 0.21/0.54    inference(superposition,[],[f79,f91])).
% 0.21/0.54  fof(f79,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,k4_xboole_0(X0,X1)) | ~r2_hidden(X3,X1)) ) | ~spl5_10),
% 0.21/0.54    inference(avatar_component_clause,[],[f78])).
% 0.21/0.54  fof(f186,plain,(
% 0.21/0.54    spl5_25),
% 0.21/0.54    inference(avatar_split_clause,[],[f32,f184])).
% 0.21/0.54  fof(f32,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X1) | ~r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f2,axiom,(
% 0.21/0.54    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.54  fof(f150,plain,(
% 0.21/0.54    spl5_21),
% 0.21/0.54    inference(avatar_split_clause,[],[f33,f148])).
% 0.21/0.54  fof(f33,plain,(
% 0.21/0.54    ( ! [X2,X0,X1] : (r2_hidden(sK4(X0,X1,X2),X0) | r2_hidden(sK4(X0,X1,X2),X2) | k4_xboole_0(X0,X1) = X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f96,plain,(
% 0.21/0.54    spl5_14),
% 0.21/0.54    inference(avatar_split_clause,[],[f24,f94])).
% 0.21/0.54  fof(f24,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f9])).
% 0.21/0.54  fof(f9,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(k2_xboole_0(X0,X1),X1)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).
% 0.21/0.54  fof(f92,plain,(
% 0.21/0.54    spl5_13),
% 0.21/0.54    inference(avatar_split_clause,[],[f23,f90])).
% 0.21/0.54  fof(f23,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f10])).
% 0.21/0.54  fof(f10,axiom,(
% 0.21/0.54    ! [X0,X1] : k4_xboole_0(X0,X1) = k4_xboole_0(X0,k3_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).
% 0.21/0.54  fof(f88,plain,(
% 0.21/0.54    spl5_12),
% 0.21/0.54    inference(avatar_split_clause,[],[f22,f86])).
% 0.21/0.54  fof(f22,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))) )),
% 0.21/0.54    inference(cnf_transformation,[],[f8])).
% 0.21/0.54  fof(f8,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X0,k4_xboole_0(X1,X0))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).
% 0.21/0.54  fof(f80,plain,(
% 0.21/0.54    spl5_10),
% 0.21/0.54    inference(avatar_split_clause,[],[f39,f78])).
% 0.21/0.54  fof(f39,plain,(
% 0.21/0.54    ( ! [X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.54    inference(equality_resolution,[],[f36])).
% 0.21/0.54  fof(f36,plain,(
% 0.21/0.54    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,X1) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.54    inference(cnf_transformation,[],[f2])).
% 0.21/0.54  fof(f56,plain,(
% 0.21/0.54    spl5_4),
% 0.21/0.54    inference(avatar_split_clause,[],[f21,f54])).
% 0.21/0.54  fof(f21,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0) )),
% 0.21/0.54    inference(cnf_transformation,[],[f7])).
% 0.21/0.54  fof(f7,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,k3_xboole_0(X0,X1)) = X0),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).
% 0.21/0.54  fof(f52,plain,(
% 0.21/0.54    spl5_3),
% 0.21/0.54    inference(avatar_split_clause,[],[f20,f50])).
% 0.21/0.54  fof(f20,plain,(
% 0.21/0.54    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)) )),
% 0.21/0.54    inference(cnf_transformation,[],[f1])).
% 0.21/0.54  fof(f1,axiom,(
% 0.21/0.54    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0)),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).
% 0.21/0.54  fof(f44,plain,(
% 0.21/0.54    ~spl5_1),
% 0.21/0.54    inference(avatar_split_clause,[],[f18,f42])).
% 0.21/0.54  fof(f18,plain,(
% 0.21/0.54    k3_xboole_0(sK0,sK1) != k4_xboole_0(sK0,k4_xboole_0(sK0,sK1))),
% 0.21/0.54    inference(cnf_transformation,[],[f15])).
% 0.21/0.54  fof(f15,plain,(
% 0.21/0.54    ? [X0,X1] : k3_xboole_0(X0,X1) != k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    inference(ennf_transformation,[],[f12])).
% 0.21/0.54  fof(f12,negated_conjecture,(
% 0.21/0.54    ~! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    inference(negated_conjecture,[],[f11])).
% 0.21/0.54  fof(f11,conjecture,(
% 0.21/0.54    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.21/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.21/0.54  % SZS output end Proof for theBenchmark
% 0.21/0.54  % (7737)------------------------------
% 0.21/0.54  % (7737)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7737)Termination reason: Refutation
% 0.21/0.54  
% 0.21/0.54  % (7737)Memory used [KB]: 12537
% 0.21/0.54  % (7737)Time elapsed: 0.113 s
% 0.21/0.54  % (7737)------------------------------
% 0.21/0.54  % (7737)------------------------------
% 0.21/0.54  % (7727)Success in time 0.175 s
%------------------------------------------------------------------------------
