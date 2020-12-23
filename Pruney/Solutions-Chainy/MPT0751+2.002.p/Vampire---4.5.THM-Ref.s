%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:55:42 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 203 expanded)
%              Number of leaves         :   25 (  86 expanded)
%              Depth                    :   11
%              Number of atoms          :  334 ( 800 expanded)
%              Number of equality atoms :   41 (  97 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f763,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f69,f75,f80,f153,f158,f231,f259,f333,f342,f509,f637,f707,f708,f761])).

fof(f761,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f760])).

fof(f760,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f759,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

fof(f759,plain,
    ( r2_hidden(sK0,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(forward_demodulation,[],[f750,f67])).

fof(f67,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_3
  <=> sK0 = k1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f750,plain,
    ( r2_hidden(k1_ordinal1(sK1),sK0)
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f79,f62,f134,f73,f43])).

fof(f43,plain,(
    ! [X2,X0] :
      ( r2_hidden(k1_ordinal1(X2),X0)
      | ~ r2_hidden(X2,X0)
      | ~ v3_ordinal1(X2)
      | ~ v4_ordinal1(X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
            & r2_hidden(sK2(X0),X0)
            & v3_ordinal1(sK2(X0)) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).

fof(f28,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ r2_hidden(k1_ordinal1(X1),X0)
          & r2_hidden(X1,X0)
          & v3_ordinal1(X1) )
     => ( ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
        & r2_hidden(sK2(X0),X0)
        & v3_ordinal1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X2] :
              ( r2_hidden(k1_ordinal1(X2),X0)
              | ~ r2_hidden(X2,X0)
              | ~ v3_ordinal1(X2) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( ( v4_ordinal1(X0)
          | ? [X1] :
              ( ~ r2_hidden(k1_ordinal1(X1),X0)
              & r2_hidden(X1,X0)
              & v3_ordinal1(X1) ) )
        & ( ! [X1] :
              ( r2_hidden(k1_ordinal1(X1),X0)
              | ~ r2_hidden(X1,X0)
              | ~ v3_ordinal1(X1) )
          | ~ v4_ordinal1(X0) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( r2_hidden(k1_ordinal1(X1),X0)
            | ~ r2_hidden(X1,X0)
            | ~ v3_ordinal1(X1) ) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v4_ordinal1(X0)
      <=> ! [X1] :
            ( v3_ordinal1(X1)
           => ( r2_hidden(X1,X0)
             => r2_hidden(k1_ordinal1(X1),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).

fof(f73,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f71])).

fof(f71,plain,
    ( spl4_4
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f134,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f132])).

fof(f132,plain,
    ( spl4_9
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f62,plain,
    ( v4_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_2
  <=> v4_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f79,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl4_5
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f708,plain,
    ( sK0 != sK2(sK0)
    | r2_hidden(sK0,sK2(sK0))
    | ~ r2_hidden(sK2(sK0),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f707,plain,
    ( spl4_63
    | spl4_19
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f706,f293,f243,f702])).

fof(f702,plain,
    ( spl4_63
  <=> sK0 = sK2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).

fof(f243,plain,
    ( spl4_19
  <=> r2_hidden(sK0,sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f293,plain,
    ( spl4_24
  <=> r2_hidden(sK0,k1_ordinal1(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f706,plain,
    ( sK0 = sK2(sK0)
    | spl4_19
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f685,f245])).

fof(f245,plain,
    ( ~ r2_hidden(sK0,sK2(sK0))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f243])).

fof(f685,plain,
    ( sK0 = sK2(sK0)
    | r2_hidden(sK0,sK2(sK0))
    | ~ spl4_24 ),
    inference(resolution,[],[f295,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f295,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK2(sK0)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f293])).

fof(f637,plain,
    ( spl4_24
    | ~ spl4_5
    | spl4_10
    | spl4_17
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f628,f228,f223,f145,f77,f293])).

fof(f145,plain,
    ( spl4_10
  <=> r2_hidden(k1_ordinal1(sK2(sK0)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f223,plain,
    ( spl4_17
  <=> sK0 = k1_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f228,plain,
    ( spl4_18
  <=> v3_ordinal1(k1_ordinal1(sK2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f628,plain,
    ( r2_hidden(sK0,k1_ordinal1(sK2(sK0)))
    | ~ spl4_5
    | spl4_10
    | spl4_17
    | ~ spl4_18 ),
    inference(unit_resulting_resolution,[],[f79,f230,f147,f225,f47])).

fof(f47,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f225,plain,
    ( sK0 != k1_ordinal1(sK2(sK0))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f223])).

fof(f147,plain,
    ( ~ r2_hidden(k1_ordinal1(sK2(sK0)),sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f230,plain,
    ( v3_ordinal1(k1_ordinal1(sK2(sK0)))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f228])).

fof(f509,plain,
    ( ~ spl4_17
    | ~ spl4_1
    | spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f508,f77,f60,f57,f223])).

fof(f57,plain,
    ( spl4_1
  <=> ! [X2] :
        ( k1_ordinal1(X2) != sK0
        | ~ v3_ordinal1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f508,plain,
    ( sK0 != k1_ordinal1(sK2(sK0))
    | ~ spl4_1
    | spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f486,f61])).

fof(f61,plain,
    ( ~ v4_ordinal1(sK0)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f60])).

fof(f486,plain,
    ( v4_ordinal1(sK0)
    | sK0 != k1_ordinal1(sK2(sK0))
    | ~ spl4_1
    | ~ spl4_5 ),
    inference(resolution,[],[f192,f79])).

fof(f192,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | v4_ordinal1(X1)
        | sK0 != k1_ordinal1(sK2(X1)) )
    | ~ spl4_1 ),
    inference(resolution,[],[f58,f44])).

fof(f44,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | v3_ordinal1(sK2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,
    ( ! [X2] :
        ( ~ v3_ordinal1(X2)
        | k1_ordinal1(X2) != sK0 )
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f57])).

fof(f342,plain,
    ( spl4_9
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f340,f65,f132])).

fof(f340,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_3 ),
    inference(superposition,[],[f41,f67])).

fof(f41,plain,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : r2_hidden(X0,k1_ordinal1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

fof(f333,plain,
    ( ~ spl4_10
    | spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f329,f77,f60,f145])).

fof(f329,plain,
    ( ~ r2_hidden(k1_ordinal1(sK2(sK0)),sK0)
    | spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f79,f61,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | ~ r2_hidden(k1_ordinal1(sK2(X0)),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f259,plain,
    ( ~ spl4_19
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f240,f150,f243])).

fof(f150,plain,
    ( spl4_11
  <=> r2_hidden(sK2(sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f240,plain,
    ( ~ r2_hidden(sK0,sK2(sK0))
    | ~ spl4_11 ),
    inference(resolution,[],[f152,f48])).

fof(f152,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f231,plain,
    ( spl4_18
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f211,f155,f228])).

fof(f155,plain,
    ( spl4_12
  <=> v3_ordinal1(sK2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f211,plain,
    ( v3_ordinal1(k1_ordinal1(sK2(sK0)))
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f157,f42])).

fof(f42,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v3_ordinal1(k1_ordinal1(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v3_ordinal1(k1_ordinal1(X0)) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v3_ordinal1(k1_ordinal1(X0))
        & ~ v1_xboole_0(k1_ordinal1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).

fof(f157,plain,
    ( v3_ordinal1(sK2(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f155])).

fof(f158,plain,
    ( spl4_12
    | spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f138,f77,f60,f155])).

fof(f138,plain,
    ( v3_ordinal1(sK2(sK0))
    | spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f79,f61,f44])).

fof(f153,plain,
    ( spl4_11
    | spl4_2
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f139,f77,f60,f150])).

fof(f139,plain,
    ( r2_hidden(sK2(sK0),sK0)
    | spl4_2
    | ~ spl4_5 ),
    inference(unit_resulting_resolution,[],[f79,f61,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v4_ordinal1(X0)
      | r2_hidden(sK2(X0),X0)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f34,f77])).

fof(f34,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ( ( v4_ordinal1(sK0)
        & sK0 = k1_ordinal1(sK1)
        & v3_ordinal1(sK1) )
      | ( ! [X2] :
            ( k1_ordinal1(X2) != sK0
            | ~ v3_ordinal1(X2) )
        & ~ v4_ordinal1(sK0) ) )
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).

fof(f23,plain,
    ( ? [X0] :
        ( ( ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
          | ( ! [X2] :
                ( k1_ordinal1(X2) != X0
                | ~ v3_ordinal1(X2) )
            & ~ v4_ordinal1(X0) ) )
        & v3_ordinal1(X0) )
   => ( ( ( v4_ordinal1(sK0)
          & ? [X1] :
              ( k1_ordinal1(X1) = sK0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != sK0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(sK0) ) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X1] :
        ( k1_ordinal1(X1) = sK0
        & v3_ordinal1(X1) )
   => ( sK0 = k1_ordinal1(sK1)
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ( ( v4_ordinal1(X0)
          & ? [X1] :
              ( k1_ordinal1(X1) = X0
              & v3_ordinal1(X1) ) )
        | ( ! [X2] :
              ( k1_ordinal1(X2) != X0
              | ~ v3_ordinal1(X2) )
          & ~ v4_ordinal1(X0) ) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,plain,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X2] :
                  ( v3_ordinal1(X2)
                 => k1_ordinal1(X2) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(rectify,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ( ~ ( v4_ordinal1(X0)
              & ? [X1] :
                  ( k1_ordinal1(X1) = X0
                  & v3_ordinal1(X1) ) )
          & ~ ( ! [X1] :
                  ( v3_ordinal1(X1)
                 => k1_ordinal1(X1) != X0 )
              & ~ v4_ordinal1(X0) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( ~ ( v4_ordinal1(X0)
            & ? [X1] :
                ( k1_ordinal1(X1) = X0
                & v3_ordinal1(X1) ) )
        & ~ ( ! [X1] :
                ( v3_ordinal1(X1)
               => k1_ordinal1(X1) != X0 )
            & ~ v4_ordinal1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).

fof(f75,plain,
    ( ~ spl4_2
    | spl4_4 ),
    inference(avatar_split_clause,[],[f35,f71,f60])).

fof(f35,plain,
    ( v3_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f69,plain,
    ( ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f37,f65,f60])).

fof(f37,plain,
    ( sK0 = k1_ordinal1(sK1)
    | ~ v4_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f40,f60,f57])).

fof(f40,plain,(
    ! [X2] :
      ( v4_ordinal1(sK0)
      | k1_ordinal1(X2) != sK0
      | ~ v3_ordinal1(X2) ) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:13:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (21432)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.51  % (21424)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (21429)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (21440)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.52  % (21427)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.53  % (21426)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (21425)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (21446)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.54  % (21428)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (21425)Refutation not found, incomplete strategy% (21425)------------------------------
% 0.21/0.54  % (21425)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (21425)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (21425)Memory used [KB]: 10746
% 0.21/0.54  % (21425)Time elapsed: 0.125 s
% 0.21/0.54  % (21425)------------------------------
% 0.21/0.54  % (21425)------------------------------
% 0.21/0.54  % (21438)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.54  % (21447)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.54  % (21442)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.54  % (21431)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (21451)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (21423)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.55  % (21452)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % (21450)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (21445)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.55  % (21448)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.55  % (21434)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (21437)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (21444)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (21445)Refutation not found, incomplete strategy% (21445)------------------------------
% 0.21/0.55  % (21445)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (21443)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.56  % (21435)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (21430)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.56  % (21436)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.57  % (21445)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (21445)Memory used [KB]: 10746
% 0.21/0.57  % (21445)Time elapsed: 0.142 s
% 0.21/0.57  % (21445)------------------------------
% 0.21/0.57  % (21445)------------------------------
% 0.21/0.57  % (21439)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.57  % (21448)Refutation found. Thanks to Tanya!
% 0.21/0.57  % SZS status Theorem for theBenchmark
% 0.21/0.57  % SZS output start Proof for theBenchmark
% 0.21/0.57  fof(f763,plain,(
% 0.21/0.57    $false),
% 0.21/0.57    inference(avatar_sat_refutation,[],[f63,f69,f75,f80,f153,f158,f231,f259,f333,f342,f509,f637,f707,f708,f761])).
% 0.21/0.57  fof(f761,plain,(
% 0.21/0.57    ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9),
% 0.21/0.57    inference(avatar_contradiction_clause,[],[f760])).
% 0.21/0.57  fof(f760,plain,(
% 0.21/0.57    $false | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9)),
% 0.21/0.57    inference(subsumption_resolution,[],[f759,f48])).
% 0.21/0.57  fof(f48,plain,(
% 0.21/0.57    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f20])).
% 0.21/0.57  fof(f20,plain,(
% 0.21/0.57    ! [X0,X1] : (~r2_hidden(X1,X0) | ~r2_hidden(X0,X1))),
% 0.21/0.57    inference(ennf_transformation,[],[f1])).
% 0.21/0.57  fof(f1,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,X1) => ~r2_hidden(X1,X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).
% 0.21/0.57  fof(f759,plain,(
% 0.21/0.57    r2_hidden(sK0,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_9)),
% 0.21/0.57    inference(forward_demodulation,[],[f750,f67])).
% 0.21/0.57  fof(f67,plain,(
% 0.21/0.57    sK0 = k1_ordinal1(sK1) | ~spl4_3),
% 0.21/0.57    inference(avatar_component_clause,[],[f65])).
% 0.21/0.57  fof(f65,plain,(
% 0.21/0.57    spl4_3 <=> sK0 = k1_ordinal1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.57  fof(f750,plain,(
% 0.21/0.57    r2_hidden(k1_ordinal1(sK1),sK0) | (~spl4_2 | ~spl4_4 | ~spl4_5 | ~spl4_9)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f79,f62,f134,f73,f43])).
% 0.21/0.57  fof(f43,plain,(
% 0.21/0.57    ( ! [X2,X0] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2) | ~v4_ordinal1(X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f29,plain,(
% 0.21/0.57    ! [X0] : (((v4_ordinal1(X0) | (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0)))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f27,f28])).
% 0.21/0.57  fof(f28,plain,(
% 0.21/0.57    ! [X0] : (? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1)) => (~r2_hidden(k1_ordinal1(sK2(X0)),X0) & r2_hidden(sK2(X0),X0) & v3_ordinal1(sK2(X0))))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f27,plain,(
% 0.21/0.57    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X2] : (r2_hidden(k1_ordinal1(X2),X0) | ~r2_hidden(X2,X0) | ~v3_ordinal1(X2)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(rectify,[],[f26])).
% 0.21/0.57  fof(f26,plain,(
% 0.21/0.57    ! [X0] : (((v4_ordinal1(X0) | ? [X1] : (~r2_hidden(k1_ordinal1(X1),X0) & r2_hidden(X1,X0) & v3_ordinal1(X1))) & (! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1)) | ~v4_ordinal1(X0))) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(nnf_transformation,[],[f17])).
% 0.21/0.57  fof(f17,plain,(
% 0.21/0.57    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : (r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(flattening,[],[f16])).
% 0.21/0.57  fof(f16,plain,(
% 0.21/0.57    ! [X0] : ((v4_ordinal1(X0) <=> ! [X1] : ((r2_hidden(k1_ordinal1(X1),X0) | ~r2_hidden(X1,X0)) | ~v3_ordinal1(X1))) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f7])).
% 0.21/0.57  fof(f7,axiom,(
% 0.21/0.57    ! [X0] : (v3_ordinal1(X0) => (v4_ordinal1(X0) <=> ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X1,X0) => r2_hidden(k1_ordinal1(X1),X0)))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_ordinal1)).
% 0.21/0.57  fof(f73,plain,(
% 0.21/0.57    v3_ordinal1(sK1) | ~spl4_4),
% 0.21/0.57    inference(avatar_component_clause,[],[f71])).
% 0.21/0.57  fof(f71,plain,(
% 0.21/0.57    spl4_4 <=> v3_ordinal1(sK1)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.57  fof(f134,plain,(
% 0.21/0.57    r2_hidden(sK1,sK0) | ~spl4_9),
% 0.21/0.57    inference(avatar_component_clause,[],[f132])).
% 0.21/0.57  fof(f132,plain,(
% 0.21/0.57    spl4_9 <=> r2_hidden(sK1,sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.57  fof(f62,plain,(
% 0.21/0.57    v4_ordinal1(sK0) | ~spl4_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f60])).
% 0.21/0.57  fof(f60,plain,(
% 0.21/0.57    spl4_2 <=> v4_ordinal1(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.57  fof(f79,plain,(
% 0.21/0.57    v3_ordinal1(sK0) | ~spl4_5),
% 0.21/0.57    inference(avatar_component_clause,[],[f77])).
% 0.21/0.57  fof(f77,plain,(
% 0.21/0.57    spl4_5 <=> v3_ordinal1(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.57  fof(f708,plain,(
% 0.21/0.57    sK0 != sK2(sK0) | r2_hidden(sK0,sK2(sK0)) | ~r2_hidden(sK2(sK0),sK0)),
% 0.21/0.57    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.57  fof(f707,plain,(
% 0.21/0.57    spl4_63 | spl4_19 | ~spl4_24),
% 0.21/0.57    inference(avatar_split_clause,[],[f706,f293,f243,f702])).
% 0.21/0.57  fof(f702,plain,(
% 0.21/0.57    spl4_63 <=> sK0 = sK2(sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_63])])).
% 0.21/0.57  fof(f243,plain,(
% 0.21/0.57    spl4_19 <=> r2_hidden(sK0,sK2(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.57  fof(f293,plain,(
% 0.21/0.57    spl4_24 <=> r2_hidden(sK0,k1_ordinal1(sK2(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.21/0.57  fof(f706,plain,(
% 0.21/0.57    sK0 = sK2(sK0) | (spl4_19 | ~spl4_24)),
% 0.21/0.57    inference(subsumption_resolution,[],[f685,f245])).
% 0.21/0.57  fof(f245,plain,(
% 0.21/0.57    ~r2_hidden(sK0,sK2(sK0)) | spl4_19),
% 0.21/0.57    inference(avatar_component_clause,[],[f243])).
% 0.21/0.57  fof(f685,plain,(
% 0.21/0.57    sK0 = sK2(sK0) | r2_hidden(sK0,sK2(sK0)) | ~spl4_24),
% 0.21/0.57    inference(resolution,[],[f295,f51])).
% 0.21/0.57  fof(f51,plain,(
% 0.21/0.57    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f33])).
% 0.21/0.57  fof(f33,plain,(
% 0.21/0.57    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.57    inference(flattening,[],[f32])).
% 0.21/0.57  fof(f32,plain,(
% 0.21/0.57    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 0.21/0.57    inference(nnf_transformation,[],[f5])).
% 0.21/0.57  fof(f5,axiom,(
% 0.21/0.57    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_ordinal1)).
% 0.21/0.57  fof(f295,plain,(
% 0.21/0.57    r2_hidden(sK0,k1_ordinal1(sK2(sK0))) | ~spl4_24),
% 0.21/0.57    inference(avatar_component_clause,[],[f293])).
% 0.21/0.57  fof(f637,plain,(
% 0.21/0.57    spl4_24 | ~spl4_5 | spl4_10 | spl4_17 | ~spl4_18),
% 0.21/0.57    inference(avatar_split_clause,[],[f628,f228,f223,f145,f77,f293])).
% 0.21/0.57  fof(f145,plain,(
% 0.21/0.57    spl4_10 <=> r2_hidden(k1_ordinal1(sK2(sK0)),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.57  fof(f223,plain,(
% 0.21/0.57    spl4_17 <=> sK0 = k1_ordinal1(sK2(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.57  fof(f228,plain,(
% 0.21/0.57    spl4_18 <=> v3_ordinal1(k1_ordinal1(sK2(sK0)))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.57  fof(f628,plain,(
% 0.21/0.57    r2_hidden(sK0,k1_ordinal1(sK2(sK0))) | (~spl4_5 | spl4_10 | spl4_17 | ~spl4_18)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f79,f230,f147,f225,f47])).
% 0.21/0.57  fof(f47,plain,(
% 0.21/0.57    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f19])).
% 0.21/0.57  fof(f19,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(flattening,[],[f18])).
% 0.21/0.57  fof(f18,plain,(
% 0.21/0.57    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f6])).
% 0.21/0.57  fof(f6,axiom,(
% 0.21/0.57    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.21/0.57  fof(f225,plain,(
% 0.21/0.57    sK0 != k1_ordinal1(sK2(sK0)) | spl4_17),
% 0.21/0.57    inference(avatar_component_clause,[],[f223])).
% 0.21/0.57  fof(f147,plain,(
% 0.21/0.57    ~r2_hidden(k1_ordinal1(sK2(sK0)),sK0) | spl4_10),
% 0.21/0.57    inference(avatar_component_clause,[],[f145])).
% 0.21/0.57  fof(f230,plain,(
% 0.21/0.57    v3_ordinal1(k1_ordinal1(sK2(sK0))) | ~spl4_18),
% 0.21/0.57    inference(avatar_component_clause,[],[f228])).
% 0.21/0.57  fof(f509,plain,(
% 0.21/0.57    ~spl4_17 | ~spl4_1 | spl4_2 | ~spl4_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f508,f77,f60,f57,f223])).
% 0.21/0.57  fof(f57,plain,(
% 0.21/0.57    spl4_1 <=> ! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.57  fof(f508,plain,(
% 0.21/0.57    sK0 != k1_ordinal1(sK2(sK0)) | (~spl4_1 | spl4_2 | ~spl4_5)),
% 0.21/0.57    inference(subsumption_resolution,[],[f486,f61])).
% 0.21/0.57  fof(f61,plain,(
% 0.21/0.57    ~v4_ordinal1(sK0) | spl4_2),
% 0.21/0.57    inference(avatar_component_clause,[],[f60])).
% 0.21/0.57  fof(f486,plain,(
% 0.21/0.57    v4_ordinal1(sK0) | sK0 != k1_ordinal1(sK2(sK0)) | (~spl4_1 | ~spl4_5)),
% 0.21/0.57    inference(resolution,[],[f192,f79])).
% 0.21/0.57  fof(f192,plain,(
% 0.21/0.57    ( ! [X1] : (~v3_ordinal1(X1) | v4_ordinal1(X1) | sK0 != k1_ordinal1(sK2(X1))) ) | ~spl4_1),
% 0.21/0.57    inference(resolution,[],[f58,f44])).
% 0.21/0.57  fof(f44,plain,(
% 0.21/0.57    ( ! [X0] : (v4_ordinal1(X0) | v3_ordinal1(sK2(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f58,plain,(
% 0.21/0.57    ( ! [X2] : (~v3_ordinal1(X2) | k1_ordinal1(X2) != sK0) ) | ~spl4_1),
% 0.21/0.57    inference(avatar_component_clause,[],[f57])).
% 0.21/0.57  fof(f342,plain,(
% 0.21/0.57    spl4_9 | ~spl4_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f340,f65,f132])).
% 0.21/0.57  fof(f340,plain,(
% 0.21/0.57    r2_hidden(sK1,sK0) | ~spl4_3),
% 0.21/0.57    inference(superposition,[],[f41,f67])).
% 0.21/0.57  fof(f41,plain,(
% 0.21/0.57    ( ! [X0] : (r2_hidden(X0,k1_ordinal1(X0))) )),
% 0.21/0.57    inference(cnf_transformation,[],[f4])).
% 0.21/0.57  fof(f4,axiom,(
% 0.21/0.57    ! [X0] : r2_hidden(X0,k1_ordinal1(X0))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).
% 0.21/0.57  fof(f333,plain,(
% 0.21/0.57    ~spl4_10 | spl4_2 | ~spl4_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f329,f77,f60,f145])).
% 0.21/0.57  fof(f329,plain,(
% 0.21/0.57    ~r2_hidden(k1_ordinal1(sK2(sK0)),sK0) | (spl4_2 | ~spl4_5)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f79,f61,f46])).
% 0.21/0.57  fof(f46,plain,(
% 0.21/0.57    ( ! [X0] : (v4_ordinal1(X0) | ~r2_hidden(k1_ordinal1(sK2(X0)),X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f259,plain,(
% 0.21/0.57    ~spl4_19 | ~spl4_11),
% 0.21/0.57    inference(avatar_split_clause,[],[f240,f150,f243])).
% 0.21/0.57  fof(f150,plain,(
% 0.21/0.57    spl4_11 <=> r2_hidden(sK2(sK0),sK0)),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.57  fof(f240,plain,(
% 0.21/0.57    ~r2_hidden(sK0,sK2(sK0)) | ~spl4_11),
% 0.21/0.57    inference(resolution,[],[f152,f48])).
% 0.21/0.57  fof(f152,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0),sK0) | ~spl4_11),
% 0.21/0.57    inference(avatar_component_clause,[],[f150])).
% 0.21/0.57  fof(f231,plain,(
% 0.21/0.57    spl4_18 | ~spl4_12),
% 0.21/0.57    inference(avatar_split_clause,[],[f211,f155,f228])).
% 0.21/0.57  fof(f155,plain,(
% 0.21/0.57    spl4_12 <=> v3_ordinal1(sK2(sK0))),
% 0.21/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.57  fof(f211,plain,(
% 0.21/0.57    v3_ordinal1(k1_ordinal1(sK2(sK0))) | ~spl4_12),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f157,f42])).
% 0.21/0.57  fof(f42,plain,(
% 0.21/0.57    ( ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f15])).
% 0.21/0.57  fof(f15,plain,(
% 0.21/0.57    ! [X0] : (v3_ordinal1(k1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f13])).
% 0.21/0.57  fof(f13,plain,(
% 0.21/0.57    ! [X0] : (v3_ordinal1(X0) => v3_ordinal1(k1_ordinal1(X0)))),
% 0.21/0.57    inference(pure_predicate_removal,[],[f3])).
% 0.21/0.57  fof(f3,axiom,(
% 0.21/0.57    ! [X0] : (v3_ordinal1(X0) => (v3_ordinal1(k1_ordinal1(X0)) & ~v1_xboole_0(k1_ordinal1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_ordinal1)).
% 0.21/0.57  fof(f157,plain,(
% 0.21/0.57    v3_ordinal1(sK2(sK0)) | ~spl4_12),
% 0.21/0.57    inference(avatar_component_clause,[],[f155])).
% 0.21/0.57  fof(f158,plain,(
% 0.21/0.57    spl4_12 | spl4_2 | ~spl4_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f138,f77,f60,f155])).
% 0.21/0.57  fof(f138,plain,(
% 0.21/0.57    v3_ordinal1(sK2(sK0)) | (spl4_2 | ~spl4_5)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f79,f61,f44])).
% 0.21/0.57  fof(f153,plain,(
% 0.21/0.57    spl4_11 | spl4_2 | ~spl4_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f139,f77,f60,f150])).
% 0.21/0.57  fof(f139,plain,(
% 0.21/0.57    r2_hidden(sK2(sK0),sK0) | (spl4_2 | ~spl4_5)),
% 0.21/0.57    inference(unit_resulting_resolution,[],[f79,f61,f45])).
% 0.21/0.57  fof(f45,plain,(
% 0.21/0.57    ( ! [X0] : (v4_ordinal1(X0) | r2_hidden(sK2(X0),X0) | ~v3_ordinal1(X0)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f29])).
% 0.21/0.57  fof(f80,plain,(
% 0.21/0.57    spl4_5),
% 0.21/0.57    inference(avatar_split_clause,[],[f34,f77])).
% 0.21/0.57  fof(f34,plain,(
% 0.21/0.57    v3_ordinal1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f25,plain,(
% 0.21/0.57    ((v4_ordinal1(sK0) & (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0)),
% 0.21/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f24,f23])).
% 0.21/0.57  fof(f23,plain,(
% 0.21/0.57    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0)) => (((v4_ordinal1(sK0) & ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(sK0))) & v3_ordinal1(sK0))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f24,plain,(
% 0.21/0.57    ? [X1] : (k1_ordinal1(X1) = sK0 & v3_ordinal1(X1)) => (sK0 = k1_ordinal1(sK1) & v3_ordinal1(sK1))),
% 0.21/0.57    introduced(choice_axiom,[])).
% 0.21/0.57  fof(f14,plain,(
% 0.21/0.57    ? [X0] : (((v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) | (! [X2] : (k1_ordinal1(X2) != X0 | ~v3_ordinal1(X2)) & ~v4_ordinal1(X0))) & v3_ordinal1(X0))),
% 0.21/0.57    inference(ennf_transformation,[],[f11])).
% 0.21/0.57  fof(f11,plain,(
% 0.21/0.57    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X2] : (v3_ordinal1(X2) => k1_ordinal1(X2) != X0) & ~v4_ordinal1(X0))))),
% 0.21/0.57    inference(rectify,[],[f10])).
% 0.21/0.57  fof(f10,negated_conjecture,(
% 0.21/0.57    ~! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 0.21/0.57    inference(negated_conjecture,[],[f9])).
% 0.21/0.57  fof(f9,conjecture,(
% 0.21/0.57    ! [X0] : (v3_ordinal1(X0) => (~(v4_ordinal1(X0) & ? [X1] : (k1_ordinal1(X1) = X0 & v3_ordinal1(X1))) & ~(! [X1] : (v3_ordinal1(X1) => k1_ordinal1(X1) != X0) & ~v4_ordinal1(X0))))),
% 0.21/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_ordinal1)).
% 0.21/0.57  fof(f75,plain,(
% 0.21/0.57    ~spl4_2 | spl4_4),
% 0.21/0.57    inference(avatar_split_clause,[],[f35,f71,f60])).
% 0.21/0.57  fof(f35,plain,(
% 0.21/0.57    v3_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f69,plain,(
% 0.21/0.57    ~spl4_2 | spl4_3),
% 0.21/0.57    inference(avatar_split_clause,[],[f37,f65,f60])).
% 0.21/0.57  fof(f37,plain,(
% 0.21/0.57    sK0 = k1_ordinal1(sK1) | ~v4_ordinal1(sK0)),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  fof(f63,plain,(
% 0.21/0.57    spl4_1 | spl4_2),
% 0.21/0.57    inference(avatar_split_clause,[],[f40,f60,f57])).
% 0.21/0.57  fof(f40,plain,(
% 0.21/0.57    ( ! [X2] : (v4_ordinal1(sK0) | k1_ordinal1(X2) != sK0 | ~v3_ordinal1(X2)) )),
% 0.21/0.57    inference(cnf_transformation,[],[f25])).
% 0.21/0.57  % SZS output end Proof for theBenchmark
% 0.21/0.57  % (21448)------------------------------
% 0.21/0.57  % (21448)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (21448)Termination reason: Refutation
% 0.21/0.57  
% 0.21/0.57  % (21448)Memory used [KB]: 6652
% 0.21/0.57  % (21448)Time elapsed: 0.125 s
% 0.21/0.57  % (21448)------------------------------
% 0.21/0.57  % (21448)------------------------------
% 0.21/0.57  % (21433)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (21422)Success in time 0.202 s
%------------------------------------------------------------------------------
