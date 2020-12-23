%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1157+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.72s
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
fof(f753,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f103,f142,f150,f500,f517,f679,f709,f736,f752])).

fof(f752,plain,
    ( ~ spl10_1
    | spl10_9 ),
    inference(avatar_contradiction_clause,[],[f751])).

fof(f751,plain,
    ( $false
    | ~ spl10_1
    | spl10_9 ),
    inference(subsumption_resolution,[],[f743,f96])).

fof(f96,plain,
    ( r2_orders_2(sK4,sK5,sK6)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl10_1
  <=> r2_orders_2(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f743,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | spl10_9 ),
    inference(resolution,[],[f740,f173])).

fof(f173,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X1,k1_tarski(X2))
      | ~ r2_orders_2(X1,X2,X0) ) ),
    inference(duplicate_literal_removal,[],[f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X1,X2,X0)
      | sP1(X0,X1,k1_tarski(X2))
      | sP1(X0,X1,k1_tarski(X2)) ) ),
    inference(superposition,[],[f88,f120])).

fof(f120,plain,(
    ! [X4,X5,X3] :
      ( sK9(X3,X4,k1_tarski(X5)) = X5
      | sP1(X3,X4,k1_tarski(X5)) ) ),
    inference(resolution,[],[f87,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k1_tarski(X1))
      | X0 = X1 ) ),
    inference(resolution,[],[f73,f92])).

fof(f92,plain,(
    ! [X0] : sP0(X0,k1_tarski(X0)) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ~ sP0(X0,X1) )
      & ( sP0(X0,X1)
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> sP0(X0,X1) ) ),
    inference(definition_folding,[],[f2,f31])).

fof(f31,plain,(
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

fof(f73,plain,(
    ! [X0,X3,X1] :
      ( ~ sP0(X0,X1)
      | ~ r2_hidden(X3,X1)
      | X0 = X3 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f44,f45])).

fof(f45,plain,(
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

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK9(X0,X1,X2),X2)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ( ~ r2_orders_2(X1,sK9(X0,X1,X2),X0)
          & r2_hidden(sK9(X0,X1,X2),X2)
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK9])],[f54,f55])).

fof(f55,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ r2_orders_2(X1,X3,X0)
          & r2_hidden(X3,X2)
          & m1_subset_1(X3,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK9(X0,X1,X2),X0)
        & r2_hidden(sK9(X0,X1,X2),X2)
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ? [X3] :
            ( ~ r2_orders_2(X1,X3,X0)
            & r2_hidden(X3,X2)
            & m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X4,X0)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f53])).

fof(f53,plain,(
    ! [X3,X1,X2] :
      ( ( sP1(X3,X1,X2)
        | ? [X4] :
            ( ~ r2_orders_2(X1,X4,X3)
            & r2_hidden(X4,X2)
            & m1_subset_1(X4,u1_struct_0(X1)) ) )
      & ( ! [X4] :
            ( r2_orders_2(X1,X4,X3)
            | ~ r2_hidden(X4,X2)
            | ~ m1_subset_1(X4,u1_struct_0(X1)) )
        | ~ sP1(X3,X1,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X3,X1,X2] :
      ( sP1(X3,X1,X2)
    <=> ! [X4] :
          ( r2_orders_2(X1,X4,X3)
          | ~ r2_hidden(X4,X2)
          | ~ m1_subset_1(X4,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X1,sK9(X0,X1,X2),X0)
      | sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f740,plain,
    ( ~ sP1(sK6,sK4,k1_tarski(sK5))
    | spl10_9 ),
    inference(subsumption_resolution,[],[f737,f63])).

fof(f63,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
    ( ( ~ r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
      | ~ r2_orders_2(sK4,sK5,sK6) )
    & ( r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
      | r2_orders_2(sK4,sK5,sK6) )
    & m1_subset_1(sK6,u1_struct_0(sK4))
    & m1_subset_1(sK5,u1_struct_0(sK4))
    & l1_orders_2(sK4)
    & v5_orders_2(sK4)
    & v4_orders_2(sK4)
    & v3_orders_2(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f38,f41,f40,f39])).

fof(f39,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                  | ~ r2_orders_2(X0,X1,X2) )
                & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
              ( ( ~ r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1)))
                | ~ r2_orders_2(sK4,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1)))
                | r2_orders_2(sK4,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK4)) )
          & m1_subset_1(X1,u1_struct_0(sK4)) )
      & l1_orders_2(sK4)
      & v5_orders_2(sK4)
      & v4_orders_2(sK4)
      & v3_orders_2(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1)))
              | ~ r2_orders_2(sK4,X1,X2) )
            & ( r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1)))
              | r2_orders_2(sK4,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK4)) )
        & m1_subset_1(X1,u1_struct_0(sK4)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
            | ~ r2_orders_2(sK4,sK5,X2) )
          & ( r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
            | r2_orders_2(sK4,sK5,X2) )
          & m1_subset_1(X2,u1_struct_0(sK4)) )
      & m1_subset_1(sK5,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
          | ~ r2_orders_2(sK4,sK5,X2) )
        & ( r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
          | r2_orders_2(sK4,sK5,X2) )
        & m1_subset_1(X2,u1_struct_0(sK4)) )
   => ( ( ~ r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
        | ~ r2_orders_2(sK4,sK5,sK6) )
      & ( r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
        | r2_orders_2(sK4,sK5,sK6) )
      & m1_subset_1(sK6,u1_struct_0(sK4)) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_orders_2(X0,X1,X2)
              <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
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
                <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).

fof(f737,plain,
    ( ~ sP1(sK6,sK4,k1_tarski(sK5))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | spl10_9 ),
    inference(resolution,[],[f498,f93])).

fof(f93,plain,(
    ! [X0,X3,X1] :
      ( sP2(X0,X1,X3)
      | ~ sP1(X3,X1,X0)
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( sP2(X0,X1,X2)
      | ~ sP1(X3,X1,X0)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f50,f51])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( sP1(X4,X1,X0)
          & X2 = X4
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( sP1(sK8(X0,X1,X2),X1,X0)
        & sK8(X0,X1,X2) = X2
        & m1_subset_1(sK8(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X2,X1,X0] :
      ( sP2(X2,X1,X0)
    <=> ? [X3] :
          ( sP1(X3,X1,X2)
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f498,plain,
    ( ~ sP2(k1_tarski(sK5),sK4,sK6)
    | spl10_9 ),
    inference(avatar_component_clause,[],[f497])).

fof(f497,plain,
    ( spl10_9
  <=> sP2(k1_tarski(sK5),sK4,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_9])])).

fof(f736,plain,
    ( ~ spl10_9
    | spl10_5
    | ~ spl10_8 ),
    inference(avatar_split_clause,[],[f735,f493,f139,f497])).

fof(f139,plain,
    ( spl10_5
  <=> r2_hidden(sK6,k1_orders_2(sK4,k1_tarski(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f493,plain,
    ( spl10_8
  <=> m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_8])])).

fof(f735,plain,
    ( ~ sP2(k1_tarski(sK5),sK4,sK6)
    | spl10_5
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f734,f57])).

fof(f57,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f734,plain,
    ( ~ sP2(k1_tarski(sK5),sK4,sK6)
    | v2_struct_0(sK4)
    | spl10_5
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f733,f58])).

fof(f58,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f733,plain,
    ( ~ sP2(k1_tarski(sK5),sK4,sK6)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_5
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f732,f59])).

fof(f59,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f732,plain,
    ( ~ sP2(k1_tarski(sK5),sK4,sK6)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_5
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f731,f60])).

fof(f60,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f731,plain,
    ( ~ sP2(k1_tarski(sK5),sK4,sK6)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_5
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f730,f61])).

fof(f61,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f42])).

fof(f730,plain,
    ( ~ sP2(k1_tarski(sK5),sK4,sK6)
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_5
    | ~ spl10_8 ),
    inference(subsumption_resolution,[],[f717,f494])).

fof(f494,plain,
    ( m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl10_8 ),
    inference(avatar_component_clause,[],[f493])).

fof(f717,plain,
    ( ~ sP2(k1_tarski(sK5),sK4,sK6)
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl10_5 ),
    inference(resolution,[],[f140,f267])).

fof(f267,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X5,k1_orders_2(X3,X4))
      | ~ sP2(X4,X3,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(subsumption_resolution,[],[f264,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP3(X0,X1,X2)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f28,f35,f34,f33])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> sP2(X2,X1,X0) )
      | ~ sP3(X0,X1,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
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
     => ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> ? [X3] :
            ( ! [X4] :
                ( m1_subset_1(X4,u1_struct_0(X1))
               => ( r2_hidden(X4,X2)
                 => r2_orders_2(X1,X4,X3) ) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f264,plain,(
    ! [X4,X5,X3] :
      ( r2_hidden(X5,k1_orders_2(X3,X4))
      | ~ sP2(X4,X3,X5)
      | ~ sP3(X5,X3,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X3)))
      | ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(superposition,[],[f80,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
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
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ~ sP2(X2,X1,X0) )
        & ( sP2(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f140,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k1_tarski(sK5)))
    | spl10_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f709,plain,
    ( ~ spl10_5
    | spl10_2
    | spl10_3 ),
    inference(avatar_split_clause,[],[f708,f129,f99,f139])).

fof(f99,plain,
    ( spl10_2
  <=> r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f129,plain,
    ( spl10_3
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f708,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k1_tarski(sK5)))
    | spl10_2
    | spl10_3 ),
    inference(subsumption_resolution,[],[f707,f130])).

fof(f130,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl10_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f707,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k1_tarski(sK5)))
    | v1_xboole_0(u1_struct_0(sK4))
    | spl10_2 ),
    inference(subsumption_resolution,[],[f685,f62])).

fof(f62,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f42])).

fof(f685,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k1_tarski(sK5)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | spl10_2 ),
    inference(superposition,[],[f101,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f101,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | spl10_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f679,plain,
    ( spl10_1
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(avatar_contradiction_clause,[],[f678])).

fof(f678,plain,
    ( $false
    | spl10_1
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f672,f106])).

fof(f106,plain,(
    ! [X0] : r2_hidden(X0,k1_tarski(X0)) ),
    inference(resolution,[],[f91,f92])).

fof(f91,plain,(
    ! [X3,X1] :
      ( ~ sP0(X3,X1)
      | r2_hidden(X3,X1) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f672,plain,
    ( ~ r2_hidden(sK5,k1_tarski(sK5))
    | spl10_1
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(resolution,[],[f671,f97])).

fof(f97,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | spl10_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f671,plain,
    ( ! [X0] :
        ( r2_orders_2(sK4,X0,sK6)
        | ~ r2_hidden(X0,k1_tarski(sK5)) )
    | ~ spl10_8
    | ~ spl10_9 ),
    inference(subsumption_resolution,[],[f519,f528])).

fof(f528,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tarski(sK5))
        | m1_subset_1(X1,u1_struct_0(sK4)) )
    | ~ spl10_8 ),
    inference(resolution,[],[f494,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f519,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK4))
        | ~ r2_hidden(X0,k1_tarski(sK5))
        | r2_orders_2(sK4,X0,sK6) )
    | ~ spl10_9 ),
    inference(resolution,[],[f499,f324])).

fof(f324,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X0)
      | r2_orders_2(X1,X3,X2) ) ),
    inference(duplicate_literal_removal,[],[f323])).

fof(f323,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X1,X3,X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ r2_hidden(X3,X0)
      | ~ sP2(X0,X1,X2)
      | ~ sP2(X0,X1,X2) ) ),
    inference(superposition,[],[f212,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sK8(X0,X1,X2) = X2
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f212,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_orders_2(X2,X0,sK8(X1,X2,X3))
      | ~ m1_subset_1(X0,u1_struct_0(X2))
      | ~ r2_hidden(X0,X1)
      | ~ sP2(X1,X2,X3) ) ),
    inference(resolution,[],[f85,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( sP1(sK8(X0,X1,X2),X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | ~ r2_hidden(X4,X2)
      | ~ m1_subset_1(X4,u1_struct_0(X1))
      | r2_orders_2(X1,X4,X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f499,plain,
    ( sP2(k1_tarski(sK5),sK4,sK6)
    | ~ spl10_9 ),
    inference(avatar_component_clause,[],[f497])).

fof(f517,plain,
    ( spl10_3
    | spl10_8 ),
    inference(avatar_contradiction_clause,[],[f516])).

fof(f516,plain,
    ( $false
    | spl10_3
    | spl10_8 ),
    inference(subsumption_resolution,[],[f515,f130])).

fof(f515,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | spl10_8 ),
    inference(subsumption_resolution,[],[f511,f62])).

fof(f511,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | spl10_8 ),
    inference(resolution,[],[f495,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f72,f71])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f495,plain,
    ( ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | spl10_8 ),
    inference(avatar_component_clause,[],[f493])).

fof(f500,plain,
    ( ~ spl10_8
    | spl10_9
    | ~ spl10_5 ),
    inference(avatar_split_clause,[],[f491,f139,f497,f493])).

fof(f491,plain,
    ( sP2(k1_tarski(sK5),sK4,sK6)
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f490,f57])).

fof(f490,plain,
    ( sP2(k1_tarski(sK5),sK4,sK6)
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f489,f58])).

fof(f489,plain,
    ( sP2(k1_tarski(sK5),sK4,sK6)
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f488,f59])).

fof(f488,plain,
    ( sP2(k1_tarski(sK5),sK4,sK6)
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f487,f60])).

fof(f487,plain,
    ( sP2(k1_tarski(sK5),sK4,sK6)
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f467,f61])).

fof(f467,plain,
    ( sP2(k1_tarski(sK5),sK4,sK6)
    | ~ m1_subset_1(k1_tarski(sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_5 ),
    inference(resolution,[],[f268,f141])).

fof(f141,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k1_tarski(sK5)))
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f139])).

fof(f268,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k1_orders_2(X6,X7))
      | sP2(X7,X6,X8)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v3_orders_2(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f265,f89])).

fof(f265,plain,(
    ! [X6,X8,X7] :
      ( ~ r2_hidden(X8,k1_orders_2(X6,X7))
      | sP2(X7,X6,X8)
      | ~ sP3(X8,X6,X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_orders_2(X6)
      | ~ v5_orders_2(X6)
      | ~ v4_orders_2(X6)
      | ~ v3_orders_2(X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f79,f68])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | sP2(X2,X1,X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f150,plain,(
    ~ spl10_3 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f148,f61])).

fof(f148,plain,
    ( ~ l1_orders_2(sK4)
    | ~ spl10_3 ),
    inference(resolution,[],[f147,f66])).

fof(f66,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f147,plain,
    ( ~ l1_struct_0(sK4)
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f146,f57])).

fof(f146,plain,
    ( ~ l1_struct_0(sK4)
    | v2_struct_0(sK4)
    | ~ spl10_3 ),
    inference(resolution,[],[f131,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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

fof(f131,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f129])).

fof(f142,plain,
    ( spl10_3
    | spl10_5
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f137,f99,f139,f129])).

fof(f137,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k1_tarski(sK5)))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f126,f62])).

fof(f126,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k1_tarski(sK5)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl10_2 ),
    inference(superposition,[],[f100,f71])).

fof(f100,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f103,plain,
    ( spl10_1
    | spl10_2 ),
    inference(avatar_split_clause,[],[f64,f99,f95])).

fof(f64,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f42])).

fof(f102,plain,
    ( ~ spl10_1
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f65,f99,f95])).

fof(f65,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | ~ r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f42])).

%------------------------------------------------------------------------------
