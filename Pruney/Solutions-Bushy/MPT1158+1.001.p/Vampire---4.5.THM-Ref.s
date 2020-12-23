%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1158+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:24 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 420 expanded)
%              Number of leaves         :   25 ( 141 expanded)
%              Depth                    :   14
%              Number of atoms          :  681 (2990 expanded)
%              Number of equality atoms :   49 ( 109 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f529,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f96,f117,f125,f373,f384,f467,f490,f514,f528])).

fof(f528,plain,
    ( ~ spl10_1
    | spl10_8 ),
    inference(avatar_contradiction_clause,[],[f527])).

fof(f527,plain,
    ( $false
    | ~ spl10_1
    | spl10_8 ),
    inference(subsumption_resolution,[],[f520,f89])).

fof(f89,plain,
    ( r2_orders_2(sK4,sK5,sK6)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl10_1
  <=> r2_orders_2(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f520,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | spl10_8 ),
    inference(resolution,[],[f517,f141])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,k1_tarski(X2))
      | ~ r2_orders_2(X1,X0,X2) ) ),
    inference(duplicate_literal_removal,[],[f136])).

fof(f136,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X1,X0,X2)
      | sP1(X0,X1,k1_tarski(X2))
      | sP1(X0,X1,k1_tarski(X2)) ) ),
    inference(superposition,[],[f81,f106])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( sK9(X0,X1,k1_tarski(X2)) = X2
      | sP1(X0,X1,k1_tarski(X2)) ) ),
    inference(resolution,[],[f80,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f66,f85])).

fof(f85,plain,(
    ! [X0] : sP0(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f2,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f66,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ( ( sK7(X0,X1) != X0
            | ~ r2_hidden(sK7(X0,X1),X1) )
          & ( sK7(X0,X1) = X0
            | r2_hidden(sK7(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f39,f40])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK7(X0,X1) != X0
          | ~ r2_hidden(sK7(X0,X1),X1) )
        & ( sK7(X0,X1) = X0
          | r2_hidden(sK7(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( sP0(X0,X1)
        | ? [X2] :
            ( ( X0 != X2
              | ~ r2_hidden(X2,X1) )
            & ( X0 = X2
              | r2_hidden(X2,X1) ) ) )
      & ( ! [X2] :
            ( ( r2_hidden(X2,X1)
              | X0 != X2 )
            & ( X0 = X2
              | ~ r2_hidden(X2,X1) ) )
        | ~ sP0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r2_orders_2(X1,X0,sK9(X0,X1,X2))
          & r2_hidden(sK9(X0,X1,X2),X2)
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f49,f50])).

fof(f50,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_orders_2(X1,X0,X3)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X0,sK9(X0,X1,X2))
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r2_orders_2(X1,X0,X3)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X0,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X3,X1,X2] :
      ( ( sP1(X3,X1,X2)
        | ? [X4] :
            ( ~ r2_orders_2(X1,X3,X4)
            & r2_hidden(X4,X2)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X3,X4)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X3,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X3,X1,X2] :
      ( sP1(X3,X1,X2)
    <=> ! [X4] :
          ( r2_orders_2(X1,X3,X4)
          | ~ r2_hidden(X4,X2)
          | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X1,X0,sK9(X0,X1,X2))
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f517,plain,
    ( ~ sP1(sK5,sK4,k1_tarski(sK6))
    | spl10_8 ),
    inference(subsumption_resolution,[],[f515,f57])).

fof(f57,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
      | ~ r2_orders_2(sK4,sK5,sK6) )
    & ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
      | r2_orders_2(sK4,sK5,sK6) )
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f33,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                  | r2_orders_2(X0,X1,X2) )
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2)))
                | ~ r2_orders_2(sK4,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2)))
                | r2_orders_2(sK4,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2)))
              | ~ r2_orders_2(sK4,X1,X2) )
            & ( r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2)))
              | r2_orders_2(sK4,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK4)) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2)))
            | ~ r2_orders_2(sK4,sK5,X2) )
          & ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2)))
            | r2_orders_2(sK4,sK5,X2) )
          & m1_subset_1(X2,u1_struct_0(sK4)) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2)))
          | ~ r2_orders_2(sK4,sK5,X2) )
        & ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2)))
          | r2_orders_2(sK4,sK5,X2) )
        & m1_subset_1(X2,u1_struct_0(sK4)) )
   => ( ( ~ r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
        | ~ r2_orders_2(sK4,sK5,sK6) )
      & ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
        | r2_orders_2(sK4,sK5,sK6) )
      & m1_subset_1(sK6,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_orders_2(X0,X1,X2)
                <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_orders_2(X0,X1,X2)
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).

fof(f515,plain,
    ( ~ sP1(sK5,sK4,k1_tarski(sK6))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl10_8 ),
    inference(resolution,[],[f371,f86])).

fof(f86,plain,(
    ! [X0,X3,X1] :
      ( sP2(X0,X1,X3)
      | ~ sP1(X3,X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP1(X3,X1,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ sP1(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ( sP1(sK8(X0,X1,X2),X1,X0)
          & sK8(X0,X1,X2) = X2
          & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f45,f46])).

fof(f46,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( sP1(X4,X1,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP1(sK8(X0,X1,X2),X1,X0)
        & sK8(X0,X1,X2) = X2
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ! [X3] :
            ( ~ sP1(X3,X1,X0)
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X4] :
            ( sP1(X4,X1,X0)
            & X2 = X4
            & m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ( sP2(X2,X1,X0)
        | ! [X3] :
            ( ~ sP1(X3,X1,X2)
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( sP1(X3,X1,X2)
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP2(X2,X1,X0) ) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( sP2(X2,X1,X0)
    <=> ? [X3] :
          ( sP1(X3,X1,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f371,plain,
    ( ~ sP2(k1_tarski(sK6),sK4,sK5)
    | spl10_8 ),
    inference(avatar_component_clause,[],[f370])).

fof(f370,plain,
    ( spl10_8
  <=> sP2(k1_tarski(sK6),sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f514,plain,
    ( ~ spl10_8
    | spl10_4
    | ~ spl10_7 ),
    inference(avatar_split_clause,[],[f513,f366,f114,f370])).

fof(f114,plain,
    ( spl10_4
  <=> r2_hidden(sK5,k2_orders_2(sK4,k1_tarski(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f366,plain,
    ( spl10_7
  <=> m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_7])])).

fof(f513,plain,
    ( ~ sP2(k1_tarski(sK6),sK4,sK5)
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f512,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f512,plain,
    ( ~ sP2(k1_tarski(sK6),sK4,sK5)
    | v2_struct_0(sK4)
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f511,f53])).

fof(f53,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f511,plain,
    ( ~ sP2(k1_tarski(sK6),sK4,sK5)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f510,f54])).

fof(f54,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f510,plain,
    ( ~ sP2(k1_tarski(sK6),sK4,sK5)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f509,f55])).

fof(f55,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f509,plain,
    ( ~ sP2(k1_tarski(sK6),sK4,sK5)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f508,f56])).

fof(f56,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f37])).

fof(f508,plain,
    ( ~ sP2(k1_tarski(sK6),sK4,sK5)
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_4
    | ~ spl10_7 ),
    inference(subsumption_resolution,[],[f498,f367])).

fof(f367,plain,
    ( m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl10_7 ),
    inference(avatar_component_clause,[],[f366])).

fof(f498,plain,
    ( ~ sP2(k1_tarski(sK6),sK4,sK5)
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_4 ),
    inference(resolution,[],[f115,f219])).

fof(f219,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_orders_2(X0,X1))
      | ~ sP2(X1,X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f217,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP3(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f23,f30,f29,f28])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP2(X2,X1,X0) )
      | ~ sP3(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
        & l1_orders_2(X1)
        & v5_orders_2(X1)
        & v4_orders_2(X1)
        & v3_orders_2(X1)
        & ~ v2_struct_0(X1) )
     => ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X3,X4) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f217,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,k2_orders_2(X0,X1))
      | ~ sP2(X1,X0,X2)
      | ~ sP3(X2,X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f73,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f115,plain,
    ( ~ r2_hidden(sK5,k2_orders_2(sK4,k1_tarski(sK6)))
    | spl10_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f490,plain,
    ( ~ spl10_4
    | spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f489,f110,f92,f114])).

fof(f92,plain,
    ( spl10_2
  <=> r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f110,plain,
    ( spl10_3
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f489,plain,
    ( ~ r2_hidden(sK5,k2_orders_2(sK4,k1_tarski(sK6)))
    | spl10_2
    | spl10_3 ),
    inference(subsumption_resolution,[],[f488,f111])).

fof(f111,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f488,plain,
    ( ~ r2_hidden(sK5,k2_orders_2(sK4,k1_tarski(sK6)))
    | v1_xboole_0(u1_struct_0(sK4))
    | spl10_2 ),
    inference(subsumption_resolution,[],[f475,f58])).

fof(f58,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f37])).

fof(f475,plain,
    ( ~ r2_hidden(sK5,k2_orders_2(sK4,k1_tarski(sK6)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | spl10_2 ),
    inference(superposition,[],[f94,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f94,plain,
    ( ~ r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f467,plain,
    ( spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(avatar_contradiction_clause,[],[f466])).

fof(f466,plain,
    ( $false
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f460,f98])).

fof(f98,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f84,f85])).

fof(f84,plain,(
    ! [X3,X1] :
      ( ~ sP0(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f67])).

fof(f67,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f460,plain,
    ( ~ r2_hidden(sK6,k1_tarski(sK6))
    | spl10_1
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(resolution,[],[f459,f90])).

fof(f90,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f459,plain,
    ( ! [X0] :
        ( r2_orders_2(sK4,sK5,X0)
        | ~ r2_hidden(X0,k1_tarski(sK6)) )
    | ~ spl10_7
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f386,f393])).

fof(f393,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tarski(sK6))
        | m1_subset_1(X1,u1_struct_0(sK4)) )
    | ~ spl10_7 ),
    inference(resolution,[],[f367,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f386,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ r2_hidden(X0,k1_tarski(sK6))
        | r2_orders_2(sK4,sK5,X0) )
    | ~ spl10_8 ),
    inference(resolution,[],[f372,f269])).

fof(f269,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X0)
      | r2_orders_2(X1,X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f268])).

fof(f268,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X1,X2,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X0)
      | ~ sP2(X0,X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(superposition,[],[f171,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sK8(X0,X1,X2) = X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f171,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X2,sK8(X1,X2,X3),X0)
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ sP2(X1,X2,X3) ) ),
    inference(resolution,[],[f78,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( sP1(sK8(X0,X1,X2),X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f78,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r2_orders_2(X1,X0,X4) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f372,plain,
    ( sP2(k1_tarski(sK6),sK4,sK5)
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f370])).

fof(f384,plain,
    ( spl10_3
    | spl10_7 ),
    inference(avatar_contradiction_clause,[],[f383])).

fof(f383,plain,
    ( $false
    | spl10_3
    | spl10_7 ),
    inference(subsumption_resolution,[],[f382,f111])).

fof(f382,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | spl10_7 ),
    inference(subsumption_resolution,[],[f379,f58])).

fof(f379,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | spl10_7 ),
    inference(resolution,[],[f368,f120])).

fof(f120,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f65,f64])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f368,plain,
    ( ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | spl10_7 ),
    inference(avatar_component_clause,[],[f366])).

fof(f373,plain,
    ( ~ spl10_7
    | spl10_8
    | ~ spl10_4 ),
    inference(avatar_split_clause,[],[f364,f114,f370,f366])).

fof(f364,plain,
    ( sP2(k1_tarski(sK6),sK4,sK5)
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f363,f52])).

fof(f363,plain,
    ( sP2(k1_tarski(sK6),sK4,sK5)
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f362,f53])).

fof(f362,plain,
    ( sP2(k1_tarski(sK6),sK4,sK5)
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f361,f54])).

fof(f361,plain,
    ( sP2(k1_tarski(sK6),sK4,sK5)
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f360,f55])).

fof(f360,plain,
    ( sP2(k1_tarski(sK6),sK4,sK5)
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f341,f56])).

fof(f341,plain,
    ( sP2(k1_tarski(sK6),sK4,sK5)
    | ~ m1_subset_1(k1_tarski(sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_4 ),
    inference(resolution,[],[f220,f116])).

fof(f116,plain,
    ( r2_hidden(sK5,k2_orders_2(sK4,k1_tarski(sK6)))
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f220,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_orders_2(X3,X4))
      | sP2(X4,X3,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f218,f82])).

fof(f218,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k2_orders_2(X3,X4))
      | sP2(X4,X3,X5)
      | ~ sP3(X5,X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f72,f63])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f125,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f124])).

fof(f124,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f123,f56])).

fof(f123,plain,
    ( ~ l1_orders_2(sK4)
    | ~ spl10_3 ),
    inference(resolution,[],[f122,f61])).

fof(f61,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f122,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f121,f52])).

fof(f121,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_3 ),
    inference(resolution,[],[f112,f62])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f112,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f117,plain,
    ( spl10_3
    | spl10_4
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f108,f92,f114,f110])).

fof(f108,plain,
    ( r2_hidden(sK5,k2_orders_2(sK4,k1_tarski(sK6)))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f107,f58])).

fof(f107,plain,
    ( r2_hidden(sK5,k2_orders_2(sK4,k1_tarski(sK6)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl10_2 ),
    inference(superposition,[],[f93,f64])).

fof(f93,plain,
    ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f96,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f59,f92,f88])).

fof(f59,plain,
    ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    | r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f37])).

fof(f95,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f60,f92,f88])).

fof(f60,plain,
    ( ~ r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    | ~ r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f37])).

%------------------------------------------------------------------------------
