%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:02 EST 2020

% Result     : Theorem 1.64s
% Output     : Refutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 281 expanded)
%              Number of leaves         :   26 (  84 expanded)
%              Depth                    :   19
%              Number of atoms          :  520 (1310 expanded)
%              Number of equality atoms :   92 ( 266 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f130,f134,f138,f252,f254,f267])).

fof(f267,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | spl5_9
    | spl5_11 ),
    inference(avatar_contradiction_clause,[],[f264])).

fof(f264,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_2
    | spl5_3
    | spl5_9
    | spl5_11 ),
    inference(unit_resulting_resolution,[],[f104,f99,f182,f109,f192,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f192,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f190])).

fof(f190,plain,
    ( spl5_11
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f109,plain,
    ( sK0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl5_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f182,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_9
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f99,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl5_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f104,plain,
    ( v3_ordinal1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f254,plain,
    ( ~ spl5_1
    | ~ spl5_2
    | ~ spl5_11
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f251,f127,f190,f102,f97])).

fof(f127,plain,
    ( spl5_7
  <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f251,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f228,f129])).

fof(f129,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f127])).

fof(f228,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(subsumption_resolution,[],[f169,f223])).

fof(f223,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X2,X1)
      | r1_tarski(X2,X1)
      | ~ v3_ordinal1(X1) ) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,(
    ! [X2,X1] :
      ( ~ v3_ordinal1(X1)
      | r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f219,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f79])).

fof(f79,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f219,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(global_subsumption,[],[f83,f211])).

fof(f211,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1)))
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) ) ),
    inference(resolution,[],[f208,f84])).

fof(f84,plain,(
    ! [X1] : r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1))) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | X0 != X1 ) ),
    inference(definition_unfolding,[],[f55,f79])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f208,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r2_hidden(X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X1,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X0,X2) ) ),
    inference(resolution,[],[f155,f200])).

fof(f200,plain,(
    ! [X4,X0,X5] :
      ( ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | r1_tarski(X4,X5)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0) ) ),
    inference(global_subsumption,[],[f75,f94])).

fof(f94,plain,(
    ! [X4,X0,X5] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0))
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X4,X0,X5,X1] :
      ( r1_tarski(X4,X5)
      | ~ r2_hidden(k4_tarski(X4,X5),X1)
      | ~ r2_hidden(X5,X0)
      | ~ r2_hidden(X4,X0)
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
              | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
            & r2_hidden(sK4(X0,X1),X0)
            & r2_hidden(sK3(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f47])).

fof(f47,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | ~ r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & ( r1_tarski(sK3(X0,X1),sK4(X0,X1))
          | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1) )
        & r2_hidden(sK4(X0,X1),X0)
        & r2_hidden(sK3(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f75,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(global_subsumption,[],[f75,f153])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(superposition,[],[f86,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f86,plain,(
    ! [X4,X0,X1] :
      ( ~ r2_hidden(X4,k1_wellord1(X0,X1))
      | r2_hidden(k4_tarski(X4,X1),X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(k4_tarski(X4,X1),X0)
      | ~ r2_hidden(X4,X2)
      | k1_wellord1(X0,X1) != X2
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                | sK2(X0,X1,X2) = X1
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
                  & sK2(X0,X1,X2) != X1 )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
            | X1 = X3
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(k4_tarski(X3,X1),X0)
              & X1 != X3 )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
          | sK2(X0,X1,X2) = X1
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ( r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0)
            & sK2(X0,X1,X2) != X1 )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X4] :
                ( ( r2_hidden(X4,X2)
                  | ~ r2_hidden(k4_tarski(X4,X1),X0)
                  | X1 = X4 )
                & ( ( r2_hidden(k4_tarski(X4,X1),X0)
                    & X1 != X4 )
                  | ~ r2_hidden(X4,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k1_wellord1(X0,X1) = X2
            | ? [X3] :
                ( ( ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3
                  | ~ r2_hidden(X3,X2) )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ~ r2_hidden(k4_tarski(X3,X1),X0)
                  | X1 = X3 )
                & ( ( r2_hidden(k4_tarski(X3,X1),X0)
                    & X1 != X3 )
                  | ~ r2_hidden(X3,X2) ) )
            | k1_wellord1(X0,X1) != X2 ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1,X2] :
          ( k1_wellord1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ( r2_hidden(k4_tarski(X3,X1),X0)
                & X1 != X3 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

fof(f83,plain,(
    ! [X0] :
      ( v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0)))
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f76,f79])).

fof(f76,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).

fof(f169,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f166,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f166,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(global_subsumption,[],[f75,f74,f165])).

fof(f165,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f162,f116])).

fof(f116,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f75,f95])).

fof(f95,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f162,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(superposition,[],[f65,f57])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f74,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f252,plain,
    ( ~ spl5_2
    | ~ spl5_1
    | ~ spl5_9
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f250,f112,f180,f97,f102])).

fof(f112,plain,
    ( spl5_4
  <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f250,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ spl5_4 ),
    inference(resolution,[],[f228,f114])).

fof(f114,plain,
    ( r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f112])).

fof(f138,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f75,f125])).

fof(f125,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_6
  <=> v1_relat_1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f134,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f131])).

fof(f131,plain,
    ( $false
    | spl5_5 ),
    inference(unit_resulting_resolution,[],[f75,f121])).

fof(f121,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl5_5
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f130,plain,
    ( ~ spl5_5
    | ~ spl5_6
    | spl5_7
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f117,f112,f127,f123,f119])).

fof(f117,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_4 ),
    inference(resolution,[],[f64,f114])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f115,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f51,f112])).

fof(f51,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f110,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f52,f107])).

fof(f52,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f36])).

fof(f105,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f50,f102])).

fof(f50,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f100,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f49,f97])).

fof(f49,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.49  % (12410)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.50  % (12408)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (12425)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (12417)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (12405)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (12399)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (12403)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (12406)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (12409)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (12423)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (12415)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (12425)Refutation not found, incomplete strategy% (12425)------------------------------
% 0.21/0.52  % (12425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12413)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (12416)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.52  % (12417)Refutation not found, incomplete strategy% (12417)------------------------------
% 0.21/0.52  % (12417)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (12425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12425)Memory used [KB]: 10618
% 0.21/0.52  % (12425)Time elapsed: 0.114 s
% 0.21/0.52  % (12425)------------------------------
% 0.21/0.52  % (12425)------------------------------
% 0.21/0.52  % (12417)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (12417)Memory used [KB]: 10618
% 0.21/0.52  % (12417)Time elapsed: 0.114 s
% 0.21/0.52  % (12417)------------------------------
% 0.21/0.52  % (12417)------------------------------
% 0.21/0.52  % (12422)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.53  % (12404)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (12430)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (12430)Refutation not found, incomplete strategy% (12430)------------------------------
% 0.21/0.53  % (12430)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12430)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12430)Memory used [KB]: 1663
% 0.21/0.53  % (12430)Time elapsed: 0.001 s
% 0.21/0.53  % (12430)------------------------------
% 0.21/0.53  % (12430)------------------------------
% 0.21/0.53  % (12407)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (12426)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (12428)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (12401)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (12428)Refutation not found, incomplete strategy% (12428)------------------------------
% 0.21/0.53  % (12428)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12428)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12428)Memory used [KB]: 6140
% 0.21/0.53  % (12428)Time elapsed: 0.129 s
% 0.21/0.53  % (12428)------------------------------
% 0.21/0.53  % (12428)------------------------------
% 0.21/0.53  % (12401)Refutation not found, incomplete strategy% (12401)------------------------------
% 0.21/0.53  % (12401)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12401)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12401)Memory used [KB]: 1663
% 0.21/0.53  % (12401)Time elapsed: 0.126 s
% 0.21/0.53  % (12401)------------------------------
% 0.21/0.53  % (12401)------------------------------
% 0.21/0.53  % (12413)Refutation not found, incomplete strategy% (12413)------------------------------
% 0.21/0.53  % (12413)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (12413)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (12413)Memory used [KB]: 10618
% 0.21/0.53  % (12413)Time elapsed: 0.144 s
% 0.21/0.53  % (12413)------------------------------
% 0.21/0.53  % (12413)------------------------------
% 0.21/0.54  % (12419)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (12420)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (12427)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (12429)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (12429)Refutation not found, incomplete strategy% (12429)------------------------------
% 0.21/0.54  % (12429)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (12429)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (12429)Memory used [KB]: 10746
% 0.21/0.54  % (12429)Time elapsed: 0.139 s
% 0.21/0.54  % (12429)------------------------------
% 0.21/0.54  % (12429)------------------------------
% 0.21/0.54  % (12418)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (12412)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (12421)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.54/0.54  % (12414)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.54/0.55  % (12424)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.54/0.55  % (12411)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.64/0.57  % (12424)Refutation found. Thanks to Tanya!
% 1.64/0.57  % SZS status Theorem for theBenchmark
% 1.64/0.57  % SZS output start Proof for theBenchmark
% 1.64/0.57  fof(f268,plain,(
% 1.64/0.57    $false),
% 1.64/0.57    inference(avatar_sat_refutation,[],[f100,f105,f110,f115,f130,f134,f138,f252,f254,f267])).
% 1.64/0.57  fof(f267,plain,(
% 1.64/0.57    ~spl5_1 | ~spl5_2 | spl5_3 | spl5_9 | spl5_11),
% 1.64/0.57    inference(avatar_contradiction_clause,[],[f264])).
% 1.64/0.57  fof(f264,plain,(
% 1.64/0.57    $false | (~spl5_1 | ~spl5_2 | spl5_3 | spl5_9 | spl5_11)),
% 1.64/0.57    inference(unit_resulting_resolution,[],[f104,f99,f182,f109,f192,f56])).
% 1.64/0.57  fof(f56,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f19])).
% 1.64/0.57  fof(f19,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.64/0.57    inference(flattening,[],[f18])).
% 1.64/0.57  fof(f18,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f4])).
% 1.64/0.57  fof(f4,axiom,(
% 1.64/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.64/0.57  fof(f192,plain,(
% 1.64/0.57    ~r2_hidden(sK0,sK1) | spl5_11),
% 1.64/0.57    inference(avatar_component_clause,[],[f190])).
% 1.64/0.57  fof(f190,plain,(
% 1.64/0.57    spl5_11 <=> r2_hidden(sK0,sK1)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.64/0.57  fof(f109,plain,(
% 1.64/0.57    sK0 != sK1 | spl5_3),
% 1.64/0.57    inference(avatar_component_clause,[],[f107])).
% 1.64/0.57  fof(f107,plain,(
% 1.64/0.57    spl5_3 <=> sK0 = sK1),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.64/0.57  fof(f182,plain,(
% 1.64/0.57    ~r2_hidden(sK1,sK0) | spl5_9),
% 1.64/0.57    inference(avatar_component_clause,[],[f180])).
% 1.64/0.57  fof(f180,plain,(
% 1.64/0.57    spl5_9 <=> r2_hidden(sK1,sK0)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.64/0.57  fof(f99,plain,(
% 1.64/0.57    v3_ordinal1(sK0) | ~spl5_1),
% 1.64/0.57    inference(avatar_component_clause,[],[f97])).
% 1.64/0.57  fof(f97,plain,(
% 1.64/0.57    spl5_1 <=> v3_ordinal1(sK0)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.64/0.57  fof(f104,plain,(
% 1.64/0.57    v3_ordinal1(sK1) | ~spl5_2),
% 1.64/0.57    inference(avatar_component_clause,[],[f102])).
% 1.64/0.57  fof(f102,plain,(
% 1.64/0.57    spl5_2 <=> v3_ordinal1(sK1)),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.64/0.57  fof(f254,plain,(
% 1.64/0.57    ~spl5_1 | ~spl5_2 | ~spl5_11 | ~spl5_7),
% 1.64/0.57    inference(avatar_split_clause,[],[f251,f127,f190,f102,f97])).
% 1.64/0.57  fof(f127,plain,(
% 1.64/0.57    spl5_7 <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.64/0.57  fof(f251,plain,(
% 1.64/0.57    ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~spl5_7),
% 1.64/0.57    inference(resolution,[],[f228,f129])).
% 1.64/0.57  fof(f129,plain,(
% 1.64/0.57    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~spl5_7),
% 1.64/0.57    inference(avatar_component_clause,[],[f127])).
% 1.64/0.57  fof(f228,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.64/0.57    inference(subsumption_resolution,[],[f169,f223])).
% 1.64/0.57  fof(f223,plain,(
% 1.64/0.57    ( ! [X2,X1] : (~r2_hidden(X2,X1) | r1_tarski(X2,X1) | ~v3_ordinal1(X1)) )),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f221])).
% 1.64/0.57  fof(f221,plain,(
% 1.64/0.57    ( ! [X2,X1] : (~v3_ordinal1(X1) | r1_tarski(X2,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X1)) )),
% 1.64/0.57    inference(resolution,[],[f219,f81])).
% 1.64/0.57  fof(f81,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f54,f79])).
% 1.64/0.57  fof(f79,plain,(
% 1.64/0.57    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f2])).
% 1.64/0.57  fof(f2,axiom,(
% 1.64/0.57    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.64/0.57  fof(f54,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f38])).
% 1.64/0.57  fof(f38,plain,(
% 1.64/0.57    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.64/0.57    inference(flattening,[],[f37])).
% 1.64/0.57  fof(f37,plain,(
% 1.64/0.57    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.64/0.57    inference(nnf_transformation,[],[f3])).
% 1.64/0.57  fof(f3,axiom,(
% 1.64/0.57    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.64/0.57  fof(f219,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.64/0.57    inference(global_subsumption,[],[f83,f211])).
% 1.64/0.57  fof(f211,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~v3_ordinal1(k2_xboole_0(X1,k1_tarski(X1))) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.64/0.57    inference(resolution,[],[f208,f84])).
% 1.64/0.57  fof(f84,plain,(
% 1.64/0.57    ( ! [X1] : (r2_hidden(X1,k2_xboole_0(X1,k1_tarski(X1)))) )),
% 1.64/0.57    inference(equality_resolution,[],[f80])).
% 1.64/0.57  fof(f80,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | X0 != X1) )),
% 1.64/0.57    inference(definition_unfolding,[],[f55,f79])).
% 1.64/0.57  fof(f55,plain,(
% 1.64/0.57    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | X0 != X1) )),
% 1.64/0.57    inference(cnf_transformation,[],[f38])).
% 1.64/0.57  fof(f208,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,X2) | ~r2_hidden(X0,X1) | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r2_hidden(X0,X2)) )),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f204])).
% 1.64/0.57  fof(f204,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~r2_hidden(X1,X2) | ~v3_ordinal1(X2) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) )),
% 1.64/0.57    inference(resolution,[],[f155,f200])).
% 1.64/0.57  fof(f200,plain,(
% 1.64/0.57    ( ! [X4,X0,X5] : (~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | r1_tarski(X4,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) )),
% 1.64/0.57    inference(global_subsumption,[],[f75,f94])).
% 1.64/0.57  fof(f94,plain,(
% 1.64/0.57    ( ! [X4,X0,X5] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),k1_wellord2(X0)) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.64/0.57    inference(equality_resolution,[],[f68])).
% 1.64/0.57  fof(f68,plain,(
% 1.64/0.57    ( ! [X4,X0,X5,X1] : (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0) | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f48])).
% 1.64/0.57  fof(f48,plain,(
% 1.64/0.57    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f46,f47])).
% 1.64/0.57  fof(f47,plain,(
% 1.64/0.57    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK3(X0,X1),sK4(X0,X1)) | ~r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & (r1_tarski(sK3(X0,X1),sK4(X0,X1)) | r2_hidden(k4_tarski(sK3(X0,X1),sK4(X0,X1)),X1)) & r2_hidden(sK4(X0,X1),X0) & r2_hidden(sK3(X0,X1),X0)))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f46,plain,(
% 1.64/0.57    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(rectify,[],[f45])).
% 1.64/0.57  fof(f45,plain,(
% 1.64/0.57    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(flattening,[],[f44])).
% 1.64/0.57  fof(f44,plain,(
% 1.64/0.57    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(nnf_transformation,[],[f29])).
% 1.64/0.57  fof(f29,plain,(
% 1.64/0.57    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(flattening,[],[f28])).
% 1.64/0.57  fof(f28,plain,(
% 1.64/0.57    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f9])).
% 1.64/0.57  fof(f9,axiom,(
% 1.64/0.57    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 1.64/0.57  fof(f75,plain,(
% 1.64/0.57    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 1.64/0.57    inference(cnf_transformation,[],[f10])).
% 1.64/0.57  fof(f10,axiom,(
% 1.64/0.57    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 1.64/0.57  fof(f155,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0)) | ~r2_hidden(X2,X1) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.64/0.57    inference(global_subsumption,[],[f75,f153])).
% 1.64/0.57  fof(f153,plain,(
% 1.64/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | r2_hidden(k4_tarski(X2,X1),k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.64/0.57    inference(superposition,[],[f86,f57])).
% 1.64/0.57  fof(f57,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f21])).
% 1.64/0.57  fof(f21,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.64/0.57    inference(flattening,[],[f20])).
% 1.64/0.57  fof(f20,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f11])).
% 1.64/0.57  fof(f11,axiom,(
% 1.64/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 1.64/0.57  fof(f86,plain,(
% 1.64/0.57    ( ! [X4,X0,X1] : (~r2_hidden(X4,k1_wellord1(X0,X1)) | r2_hidden(k4_tarski(X4,X1),X0) | ~v1_relat_1(X0)) )),
% 1.64/0.57    inference(equality_resolution,[],[f59])).
% 1.64/0.57  fof(f59,plain,(
% 1.64/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(k4_tarski(X4,X1),X0) | ~r2_hidden(X4,X2) | k1_wellord1(X0,X1) != X2 | ~v1_relat_1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f43])).
% 1.64/0.57  fof(f43,plain,(
% 1.64/0.57    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f41,f42])).
% 1.64/0.57  fof(f42,plain,(
% 1.64/0.57    ! [X2,X1,X0] : (? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2))) => ((~r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) | sK2(X0,X1,X2) = X1 | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((r2_hidden(k4_tarski(sK2(X0,X1,X2),X1),X0) & sK2(X0,X1,X2) != X1) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f41,plain,(
% 1.64/0.57    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | ~r2_hidden(k4_tarski(X4,X1),X0) | X1 = X4) & ((r2_hidden(k4_tarski(X4,X1),X0) & X1 != X4) | ~r2_hidden(X4,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(rectify,[],[f40])).
% 1.64/0.57  fof(f40,plain,(
% 1.64/0.57    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : ((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3 | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(flattening,[],[f39])).
% 1.64/0.57  fof(f39,plain,(
% 1.64/0.57    ! [X0] : (! [X1,X2] : ((k1_wellord1(X0,X1) = X2 | ? [X3] : (((~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3) | ~r2_hidden(X3,X2)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (~r2_hidden(k4_tarski(X3,X1),X0) | X1 = X3)) & ((r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3) | ~r2_hidden(X3,X2))) | k1_wellord1(X0,X1) != X2)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(nnf_transformation,[],[f22])).
% 1.64/0.57  fof(f22,plain,(
% 1.64/0.57    ! [X0] : (! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f6])).
% 1.64/0.57  fof(f6,axiom,(
% 1.64/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1,X2] : (k1_wellord1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(k4_tarski(X3,X1),X0) & X1 != X3))))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).
% 1.64/0.57  fof(f83,plain,(
% 1.64/0.57    ( ! [X0] : (v3_ordinal1(k2_xboole_0(X0,k1_tarski(X0))) | ~v3_ordinal1(X0)) )),
% 1.64/0.57    inference(definition_unfolding,[],[f76,f79])).
% 1.64/0.57  fof(f76,plain,(
% 1.64/0.57    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f31])).
% 1.64/0.57  fof(f31,plain,(
% 1.64/0.57    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f5])).
% 1.64/0.57  fof(f5,axiom,(
% 1.64/0.57    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_ordinal1)).
% 1.64/0.57  fof(f169,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r1_tarski(X1,X0)) )),
% 1.64/0.57    inference(superposition,[],[f166,f66])).
% 1.64/0.57  fof(f66,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f27])).
% 1.64/0.57  fof(f27,plain,(
% 1.64/0.57    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 1.64/0.57    inference(ennf_transformation,[],[f13])).
% 1.64/0.57  fof(f13,axiom,(
% 1.64/0.57    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 1.64/0.57  fof(f166,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.64/0.57    inference(global_subsumption,[],[f75,f74,f165])).
% 1.64/0.57  fof(f165,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~v2_wellord1(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.64/0.57    inference(duplicate_literal_removal,[],[f164])).
% 1.64/0.57  fof(f164,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~v2_wellord1(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.64/0.57    inference(forward_demodulation,[],[f162,f116])).
% 1.64/0.57  fof(f116,plain,(
% 1.64/0.57    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 1.64/0.57    inference(global_subsumption,[],[f75,f95])).
% 1.64/0.57  fof(f95,plain,(
% 1.64/0.57    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.64/0.57    inference(equality_resolution,[],[f67])).
% 1.64/0.57  fof(f67,plain,(
% 1.64/0.57    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f48])).
% 1.64/0.57  fof(f162,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~v2_wellord1(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.64/0.57    inference(superposition,[],[f65,f57])).
% 1.64/0.57  fof(f65,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f26])).
% 1.64/0.57  fof(f26,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(flattening,[],[f25])).
% 1.64/0.57  fof(f25,plain,(
% 1.64/0.57    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f8])).
% 1.64/0.57  fof(f8,axiom,(
% 1.64/0.57    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 1.64/0.57  fof(f74,plain,(
% 1.64/0.57    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f30])).
% 1.64/0.57  fof(f30,plain,(
% 1.64/0.57    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f12])).
% 1.64/0.57  fof(f12,axiom,(
% 1.64/0.57    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 1.64/0.57  fof(f252,plain,(
% 1.64/0.57    ~spl5_2 | ~spl5_1 | ~spl5_9 | ~spl5_4),
% 1.64/0.57    inference(avatar_split_clause,[],[f250,f112,f180,f97,f102])).
% 1.64/0.57  fof(f112,plain,(
% 1.64/0.57    spl5_4 <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.64/0.57  fof(f250,plain,(
% 1.64/0.57    ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~spl5_4),
% 1.64/0.57    inference(resolution,[],[f228,f114])).
% 1.64/0.57  fof(f114,plain,(
% 1.64/0.57    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~spl5_4),
% 1.64/0.57    inference(avatar_component_clause,[],[f112])).
% 1.64/0.57  fof(f138,plain,(
% 1.64/0.57    spl5_6),
% 1.64/0.57    inference(avatar_contradiction_clause,[],[f135])).
% 1.64/0.57  fof(f135,plain,(
% 1.64/0.57    $false | spl5_6),
% 1.64/0.57    inference(unit_resulting_resolution,[],[f75,f125])).
% 1.64/0.57  fof(f125,plain,(
% 1.64/0.57    ~v1_relat_1(k1_wellord2(sK1)) | spl5_6),
% 1.64/0.57    inference(avatar_component_clause,[],[f123])).
% 1.64/0.57  fof(f123,plain,(
% 1.64/0.57    spl5_6 <=> v1_relat_1(k1_wellord2(sK1))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.64/0.57  fof(f134,plain,(
% 1.64/0.57    spl5_5),
% 1.64/0.57    inference(avatar_contradiction_clause,[],[f131])).
% 1.64/0.57  fof(f131,plain,(
% 1.64/0.57    $false | spl5_5),
% 1.64/0.57    inference(unit_resulting_resolution,[],[f75,f121])).
% 1.64/0.57  fof(f121,plain,(
% 1.64/0.57    ~v1_relat_1(k1_wellord2(sK0)) | spl5_5),
% 1.64/0.57    inference(avatar_component_clause,[],[f119])).
% 1.64/0.57  fof(f119,plain,(
% 1.64/0.57    spl5_5 <=> v1_relat_1(k1_wellord2(sK0))),
% 1.64/0.57    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.64/0.57  fof(f130,plain,(
% 1.64/0.57    ~spl5_5 | ~spl5_6 | spl5_7 | ~spl5_4),
% 1.64/0.57    inference(avatar_split_clause,[],[f117,f112,f127,f123,f119])).
% 1.64/0.57  fof(f117,plain,(
% 1.64/0.57    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl5_4),
% 1.64/0.57    inference(resolution,[],[f64,f114])).
% 1.64/0.57  fof(f64,plain,(
% 1.64/0.57    ( ! [X0,X1] : (~r4_wellord1(X0,X1) | r4_wellord1(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.64/0.57    inference(cnf_transformation,[],[f24])).
% 1.64/0.57  fof(f24,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(flattening,[],[f23])).
% 1.64/0.57  fof(f23,plain,(
% 1.64/0.57    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f7])).
% 1.64/0.57  fof(f7,axiom,(
% 1.64/0.57    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 1.64/0.57  fof(f115,plain,(
% 1.64/0.57    spl5_4),
% 1.64/0.57    inference(avatar_split_clause,[],[f51,f112])).
% 1.64/0.57  fof(f51,plain,(
% 1.64/0.57    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 1.64/0.57    inference(cnf_transformation,[],[f36])).
% 1.64/0.57  fof(f36,plain,(
% 1.64/0.57    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 1.64/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f17,f35,f34])).
% 1.64/0.57  fof(f34,plain,(
% 1.64/0.57    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f35,plain,(
% 1.64/0.57    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 1.64/0.57    introduced(choice_axiom,[])).
% 1.64/0.57  fof(f17,plain,(
% 1.64/0.57    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.64/0.57    inference(flattening,[],[f16])).
% 1.64/0.57  fof(f16,plain,(
% 1.64/0.57    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.64/0.57    inference(ennf_transformation,[],[f15])).
% 1.64/0.57  fof(f15,negated_conjecture,(
% 1.64/0.57    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 1.64/0.57    inference(negated_conjecture,[],[f14])).
% 1.64/0.57  fof(f14,conjecture,(
% 1.64/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 1.64/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 1.64/0.57  fof(f110,plain,(
% 1.64/0.57    ~spl5_3),
% 1.64/0.57    inference(avatar_split_clause,[],[f52,f107])).
% 1.64/0.57  fof(f52,plain,(
% 1.64/0.57    sK0 != sK1),
% 1.64/0.57    inference(cnf_transformation,[],[f36])).
% 1.64/0.57  fof(f105,plain,(
% 1.64/0.57    spl5_2),
% 1.64/0.57    inference(avatar_split_clause,[],[f50,f102])).
% 1.64/0.57  fof(f50,plain,(
% 1.64/0.57    v3_ordinal1(sK1)),
% 1.64/0.57    inference(cnf_transformation,[],[f36])).
% 1.64/0.57  fof(f100,plain,(
% 1.64/0.57    spl5_1),
% 1.64/0.57    inference(avatar_split_clause,[],[f49,f97])).
% 1.64/0.57  fof(f49,plain,(
% 1.64/0.57    v3_ordinal1(sK0)),
% 1.64/0.57    inference(cnf_transformation,[],[f36])).
% 1.64/0.57  % SZS output end Proof for theBenchmark
% 1.64/0.57  % (12424)------------------------------
% 1.64/0.57  % (12424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.64/0.57  % (12424)Termination reason: Refutation
% 1.64/0.57  
% 1.64/0.57  % (12424)Memory used [KB]: 11001
% 1.64/0.57  % (12424)Time elapsed: 0.181 s
% 1.64/0.57  % (12424)------------------------------
% 1.64/0.57  % (12424)------------------------------
% 1.64/0.58  % (12398)Success in time 0.223 s
%------------------------------------------------------------------------------
