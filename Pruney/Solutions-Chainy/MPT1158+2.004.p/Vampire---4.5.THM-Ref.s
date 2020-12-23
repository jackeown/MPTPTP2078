%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:03 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :  181 (1297 expanded)
%              Number of leaves         :   23 ( 414 expanded)
%              Depth                    :   38
%              Number of atoms          :  905 (11350 expanded)
%              Number of equality atoms :  105 ( 282 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f547,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f101,f123,f257,f496,f546])).

fof(f546,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f545])).

fof(f545,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f540,f95])).

fof(f95,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl9_1
  <=> r2_orders_2(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f540,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f538,f105])).

fof(f105,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f90,f91])).

fof(f91,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f90,plain,(
    ! [X4,X2,X0] :
      ( ~ sP2(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ( ( ( sK8(X0,X1,X2) != X0
              & sK8(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK8(X0,X1,X2),X2) )
          & ( sK8(X0,X1,X2) = X0
            | sK8(X0,X1,X2) = X1
            | r2_hidden(sK8(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f47,f48])).

fof(f48,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK8(X0,X1,X2) != X0
            & sK8(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK8(X0,X1,X2),X2) )
        & ( sK8(X0,X1,X2) = X0
          | sK8(X0,X1,X2) = X1
          | r2_hidden(sK8(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( sP2(X0,X1,X2)
        | ? [X3] :
            ( ( ( X0 != X3
                & X1 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X0 = X3
              | X1 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP2(X0,X1,X2) ) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X1,X0,X2] :
      ( ( sP2(X1,X0,X2)
        | ? [X3] :
            ( ( ( X1 != X3
                & X0 != X3 )
              | ~ r2_hidden(X3,X2) )
            & ( X1 = X3
              | X0 = X3
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ( X1 != X3
                & X0 != X3 ) )
            & ( X1 = X3
              | X0 = X3
              | ~ r2_hidden(X3,X2) ) )
        | ~ sP2(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f538,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | r2_orders_2(sK3,sK4,X1) )
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f537,f322])).

fof(f322,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK5,sK5))
        | m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f321,f57])).

fof(f57,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
      | ~ r2_orders_2(sK3,sK4,sK5) )
    & ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
      | r2_orders_2(sK3,sK4,sK5) )
    & m1_subset_1(sK5,u1_struct_0(sK3))
    & m1_subset_1(sK4,u1_struct_0(sK3))
    & l1_orders_2(sK3)
    & v5_orders_2(sK3)
    & v4_orders_2(sK3)
    & v3_orders_2(sK3)
    & ~ v2_struct_0(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f36,f35,f34])).

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
              ( ( ~ r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
                | ~ r2_orders_2(sK3,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
                | r2_orders_2(sK3,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK3)) )
          & m1_subset_1(X1,u1_struct_0(sK3)) )
      & l1_orders_2(sK3)
      & v5_orders_2(sK3)
      & v4_orders_2(sK3)
      & v3_orders_2(sK3)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
              | ~ r2_orders_2(sK3,X1,X2) )
            & ( r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
              | r2_orders_2(sK3,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK3)) )
        & m1_subset_1(X1,u1_struct_0(sK3)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
            | ~ r2_orders_2(sK3,sK4,X2) )
          & ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
            | r2_orders_2(sK3,sK4,X2) )
          & m1_subset_1(X2,u1_struct_0(sK3)) )
      & m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
          | ~ r2_orders_2(sK3,sK4,X2) )
        & ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2)))
          | r2_orders_2(sK3,sK4,X2) )
        & m1_subset_1(X2,u1_struct_0(sK3)) )
   => ( ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
        | ~ r2_orders_2(sK3,sK4,sK5) )
      & ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
        | r2_orders_2(sK3,sK4,sK5) )
      & m1_subset_1(sK5,u1_struct_0(sK3)) ) ),
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f321,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK5,sK5))
        | m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f320,f51])).

fof(f51,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f320,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK5,sK5))
        | v2_struct_0(sK3)
        | m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f319,f52])).

fof(f52,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f319,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK5,sK5))
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f305,f55])).

fof(f55,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f305,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK5,sK5))
        | ~ l1_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | m1_subset_1(X0,u1_struct_0(sK3))
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(superposition,[],[f132,f122])).

fof(f122,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl9_5
  <=> k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f63,f75])).

fof(f75,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f537,plain,
    ( ! [X1] :
        ( r2_orders_2(sK3,sK4,X1)
        | ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f534,f505])).

fof(f505,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f426,f497])).

fof(f497,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f98,f122])).

fof(f98,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f97,plain,
    ( spl9_2
  <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f426,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | sP0(sK3,k2_tarski(sK5,sK5),X3) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f423,f328])).

fof(f328,plain,
    ( ! [X2] : sP1(X2,k2_tarski(sK5,sK5),sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f327,f57])).

fof(f327,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f326,f51])).

fof(f326,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f325,f52])).

fof(f325,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f324,f53])).

fof(f53,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f324,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f323,f54])).

fof(f54,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f37])).

fof(f323,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f307,f55])).

fof(f307,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(superposition,[],[f139,f122])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,k6_domain_1(u1_struct_0(X1),X2),X1)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f138])).

fof(f138,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,k6_domain_1(u1_struct_0(X1),X2),X1)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f74,f63])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP1(X0,X2,X1)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f23,f28,f27])).

fof(f27,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X3,X4)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f423,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | sP0(sK3,k2_tarski(sK5,sK5),X3)
        | ~ sP1(X3,k2_tarski(sK5,sK5),sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f66,f301])).

fof(f301,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f213,f122])).

fof(f213,plain,(
    k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f212,f51])).

fof(f212,plain,
    ( v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f211,f52])).

fof(f211,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f210,f53])).

fof(f210,plain,
    ( ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f209,f54])).

fof(f209,plain,
    ( ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f201,f55])).

fof(f201,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(resolution,[],[f147,f57])).

fof(f147,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = a_2_1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = a_2_1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f61,f63])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f534,plain,
    ( ! [X1] :
        ( r2_orders_2(sK3,sK4,X1)
        | ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),sK4) )
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(superposition,[],[f70,f530])).

fof(f530,plain,
    ( sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f505,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK7(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
              & r2_hidden(sK6(X0,X1,X3),X1)
              & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,sK7(X0,X1,X2),X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK7(X0,X1,X2) = X2
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f43,f42])).

fof(f42,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
        & r2_hidden(sK6(X0,X1,X3),X1)
        & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X5,X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,sK7(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK7(X0,X1,X2) = X2
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X3,X4)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X5,X6)
                | ~ r2_hidden(X6,X1)
                | ~ m1_subset_1(X6,u1_struct_0(X0)) )
            & X2 = X5
            & m1_subset_1(X5,u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X1,X3,X4)
                & r2_hidden(X4,X2)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X3,X4)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f70,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X0,sK7(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f496,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f495])).

fof(f495,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f494,f56])).

fof(f56,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f37])).

fof(f494,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f493,f485])).

fof(f485,plain,
    ( ~ sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f425,f302])).

fof(f302,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | spl9_2
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f99,f122])).

fof(f99,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f425,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),X2) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f422,f328])).

fof(f422,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),X2)
        | ~ sP1(X2,k2_tarski(sK5,sK5),sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f67,f301])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f493,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f491,f94])).

fof(f94,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f491,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_2
    | ~ spl9_5 ),
    inference(superposition,[],[f86,f489])).

fof(f489,plain,
    ( sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f488,f56])).

fof(f488,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f487])).

fof(f487,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f485,f130])).

fof(f130,plain,(
    ! [X6,X4,X7,X5] :
      ( sP0(X4,k2_tarski(X5,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | sK6(X4,k2_tarski(X5,X6),X7) = X5
      | sK6(X4,k2_tarski(X5,X6),X7) = X6 ) ),
    inference(resolution,[],[f87,f126])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f76,f91])).

fof(f76,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f87,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | sP0(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f72])).

% (24009)Refutation not found, incomplete strategy% (24009)------------------------------
% (24009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24009)Termination reason: Refutation not found, incomplete strategy
fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

% (24009)Memory used [KB]: 10746
fof(f86,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
      | sP0(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f73])).

% (24009)Time elapsed: 0.160 s
% (24009)------------------------------
% (24009)------------------------------
fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f257,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f252])).

fof(f252,plain,
    ( $false
    | ~ spl9_3 ),
    inference(resolution,[],[f251,f56])).

fof(f251,plain,
    ( ! [X0] : ~ m1_subset_1(X0,u1_struct_0(sK3))
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f250,f55])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ l1_orders_2(sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f249,f56])).

fof(f249,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f248,f113])).

fof(f113,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl9_3
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f248,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f247,f51])).

fof(f247,plain,
    ( ! [X0] :
        ( v2_struct_0(sK3)
        | ~ v1_xboole_0(u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f245,f52])).

fof(f245,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ v1_xboole_0(u1_struct_0(sK3))
        | ~ m1_subset_1(sK4,u1_struct_0(sK3))
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(X0,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f244,f140])).

fof(f140,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,k6_domain_1(u1_struct_0(X0),X1),X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f133,f87])).

fof(f133,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X5,k6_domain_1(u1_struct_0(X4),X3))
      | ~ l1_orders_2(X4)
      | ~ v3_orders_2(X4)
      | v2_struct_0(X4)
      | ~ v1_xboole_0(u1_struct_0(X4))
      | ~ m1_subset_1(X3,u1_struct_0(X4)) ) ),
    inference(resolution,[],[f63,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f244,plain,
    ( ! [X0] : ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f243,f56])).

fof(f243,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f242,f51])).

fof(f242,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f241,f52])).

fof(f241,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f240,f53])).

fof(f240,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f239,f54])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f238,f55])).

fof(f238,plain,
    ( ! [X0] :
        ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(resolution,[],[f233,f139])).

fof(f233,plain,
    ( ! [X1] :
        ( ~ sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
        | ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f232,f56])).

fof(f232,plain,
    ( ! [X1] :
        ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1)
        | ~ sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f231,f55])).

fof(f231,plain,
    ( ! [X1] :
        ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1)
        | ~ sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
        | ~ l1_orders_2(sK3)
        | ~ m1_subset_1(sK4,u1_struct_0(sK3)) )
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f230,f113])).

fof(f230,plain,(
    ! [X1] :
      ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1)
      | ~ sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
      | ~ v1_xboole_0(u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f229,f51])).

fof(f229,plain,(
    ! [X1] :
      ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1)
      | ~ sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
      | v2_struct_0(sK3)
      | ~ v1_xboole_0(u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f228,f52])).

fof(f228,plain,(
    ! [X1] :
      ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1)
      | ~ sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ v1_xboole_0(u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f227,f53])).

fof(f227,plain,(
    ! [X1] :
      ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1)
      | ~ sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ v1_xboole_0(u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    inference(subsumption_resolution,[],[f219,f54])).

fof(f219,plain,(
    ! [X1] :
      ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1)
      | ~ sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
      | ~ v5_orders_2(sK3)
      | ~ v4_orders_2(sK3)
      | ~ v3_orders_2(sK3)
      | v2_struct_0(sK3)
      | ~ v1_xboole_0(u1_struct_0(sK3))
      | ~ l1_orders_2(sK3)
      | ~ m1_subset_1(sK4,u1_struct_0(sK3)) ) ),
    inference(resolution,[],[f214,f165])).

fof(f165,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(resolution,[],[f153,f63])).

fof(f153,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9)))
      | ~ l1_orders_2(X9)
      | ~ v5_orders_2(X9)
      | ~ v4_orders_2(X9)
      | ~ v3_orders_2(X9)
      | v2_struct_0(X9)
      | ~ v1_xboole_0(u1_struct_0(X9))
      | ~ r2_hidden(X10,k2_orders_2(X9,X8)) ) ),
    inference(resolution,[],[f65,f84])).

fof(f65,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f214,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
      | ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)
      | ~ sP1(X0,k6_domain_1(u1_struct_0(sK3),sK4),sK3) ) ),
    inference(superposition,[],[f67,f208])).

fof(f208,plain,(
    k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f207,f51])).

fof(f207,plain,
    ( v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f206,f52])).

fof(f206,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f205,f53])).

fof(f205,plain,
    ( ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f204,f54])).

fof(f204,plain,
    ( ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f200,f55])).

fof(f200,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(resolution,[],[f147,f56])).

fof(f123,plain,
    ( spl9_3
    | spl9_5 ),
    inference(avatar_split_clause,[],[f108,f120,f111])).

fof(f108,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f85,f57])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f64,f60])).

fof(f60,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f101,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f58,f97,f93])).

fof(f58,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f59,f97,f93])).

fof(f59,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.50  % (23981)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.50  % (23990)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (24005)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (23997)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.52  % (23988)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.52  % (23986)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (23991)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.52  % (23991)Refutation not found, incomplete strategy% (23991)------------------------------
% 0.21/0.52  % (23991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23991)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23991)Memory used [KB]: 10746
% 0.21/0.52  % (23991)Time elapsed: 0.118 s
% 0.21/0.52  % (23991)------------------------------
% 0.21/0.52  % (23991)------------------------------
% 0.21/0.52  % (24000)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.53  % (23997)Refutation not found, incomplete strategy% (23997)------------------------------
% 0.21/0.53  % (23997)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (23985)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (24003)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (23997)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (23997)Memory used [KB]: 10618
% 0.21/0.53  % (23997)Time elapsed: 0.114 s
% 0.21/0.53  % (23997)------------------------------
% 0.21/0.53  % (23997)------------------------------
% 0.21/0.53  % (24001)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (23982)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (23995)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.53  % (23989)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (23992)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.54  % (24007)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (23987)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.54  % (24002)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (24007)Refutation not found, incomplete strategy% (24007)------------------------------
% 0.21/0.54  % (24007)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24007)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24007)Memory used [KB]: 6268
% 0.21/0.54  % (24007)Time elapsed: 0.132 s
% 0.21/0.54  % (24007)------------------------------
% 0.21/0.54  % (24007)------------------------------
% 0.21/0.54  % (23983)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (24010)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (24010)Refutation not found, incomplete strategy% (24010)------------------------------
% 0.21/0.54  % (24010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (24010)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (24010)Memory used [KB]: 1663
% 0.21/0.54  % (24010)Time elapsed: 0.128 s
% 0.21/0.54  % (24010)------------------------------
% 0.21/0.54  % (24010)------------------------------
% 0.21/0.54  % (23999)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (23996)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (23984)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (23993)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.51/0.55  % (23994)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.51/0.55  % (24006)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.51/0.55  % (24006)Refutation not found, incomplete strategy% (24006)------------------------------
% 1.51/0.55  % (24006)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.55  % (24006)Termination reason: Refutation not found, incomplete strategy
% 1.51/0.55  
% 1.51/0.55  % (24006)Memory used [KB]: 6268
% 1.51/0.55  % (24006)Time elapsed: 0.140 s
% 1.51/0.55  % (24006)------------------------------
% 1.51/0.55  % (24006)------------------------------
% 1.51/0.55  % (23998)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.51/0.55  % (24004)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.51/0.56  % (24008)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.51/0.56  % (24009)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.51/0.57  % (23987)Refutation found. Thanks to Tanya!
% 1.51/0.57  % SZS status Theorem for theBenchmark
% 1.51/0.57  % SZS output start Proof for theBenchmark
% 1.51/0.57  fof(f547,plain,(
% 1.51/0.57    $false),
% 1.51/0.57    inference(avatar_sat_refutation,[],[f100,f101,f123,f257,f496,f546])).
% 1.51/0.57  fof(f546,plain,(
% 1.51/0.57    spl9_1 | ~spl9_2 | ~spl9_5),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f545])).
% 1.51/0.57  fof(f545,plain,(
% 1.51/0.57    $false | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(subsumption_resolution,[],[f540,f95])).
% 1.51/0.57  fof(f95,plain,(
% 1.51/0.57    ~r2_orders_2(sK3,sK4,sK5) | spl9_1),
% 1.51/0.57    inference(avatar_component_clause,[],[f93])).
% 1.51/0.57  fof(f93,plain,(
% 1.51/0.57    spl9_1 <=> r2_orders_2(sK3,sK4,sK5)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 1.51/0.57  fof(f540,plain,(
% 1.51/0.57    r2_orders_2(sK3,sK4,sK5) | (~spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(resolution,[],[f538,f105])).
% 1.51/0.57  fof(f105,plain,(
% 1.51/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.51/0.57    inference(resolution,[],[f90,f91])).
% 1.51/0.57  fof(f91,plain,(
% 1.51/0.57    ( ! [X0,X1] : (sP2(X1,X0,k2_tarski(X0,X1))) )),
% 1.51/0.57    inference(equality_resolution,[],[f82])).
% 1.51/0.57  fof(f82,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.51/0.57    inference(cnf_transformation,[],[f50])).
% 1.51/0.57  fof(f50,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.51/0.57    inference(nnf_transformation,[],[f31])).
% 1.51/0.57  fof(f31,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 1.51/0.57    inference(definition_folding,[],[f1,f30])).
% 1.51/0.57  fof(f30,plain,(
% 1.51/0.57    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.51/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.51/0.57  fof(f1,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 1.51/0.57  fof(f90,plain,(
% 1.51/0.57    ( ! [X4,X2,X0] : (~sP2(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.51/0.57    inference(equality_resolution,[],[f77])).
% 1.51/0.57  fof(f77,plain,(
% 1.51/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP2(X0,X1,X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f49])).
% 1.51/0.57  fof(f49,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f47,f48])).
% 1.51/0.57  fof(f48,plain,(
% 1.51/0.57    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f47,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 1.51/0.57    inference(rectify,[],[f46])).
% 1.51/0.57  fof(f46,plain,(
% 1.51/0.57    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.51/0.57    inference(flattening,[],[f45])).
% 1.51/0.57  fof(f45,plain,(
% 1.51/0.57    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 1.51/0.57    inference(nnf_transformation,[],[f30])).
% 1.51/0.57  fof(f538,plain,(
% 1.51/0.57    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK5,sK5)) | r2_orders_2(sK3,sK4,X1)) ) | (~spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(subsumption_resolution,[],[f537,f322])).
% 1.51/0.57  fof(f322,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK5,sK5)) | m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f321,f57])).
% 1.51/0.57  fof(f57,plain,(
% 1.51/0.57    m1_subset_1(sK5,u1_struct_0(sK3))),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f37,plain,(
% 1.51/0.57    (((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f33,f36,f35,f34])).
% 1.51/0.57  fof(f34,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f35,plain,(
% 1.51/0.57    ? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f36,plain,(
% 1.51/0.57    ? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) => ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f33,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f32])).
% 1.51/0.57  fof(f32,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.51/0.57    inference(nnf_transformation,[],[f13])).
% 1.51/0.57  fof(f13,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f12])).
% 1.51/0.57  fof(f12,plain,(
% 1.51/0.57    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f11])).
% 1.51/0.57  fof(f11,negated_conjecture,(
% 1.51/0.57    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.51/0.57    inference(negated_conjecture,[],[f10])).
% 1.51/0.57  fof(f10,conjecture,(
% 1.51/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).
% 1.51/0.57  fof(f321,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK5,sK5)) | m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f320,f51])).
% 1.51/0.57  fof(f51,plain,(
% 1.51/0.57    ~v2_struct_0(sK3)),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f320,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK5,sK5)) | v2_struct_0(sK3) | m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f319,f52])).
% 1.51/0.57  fof(f52,plain,(
% 1.51/0.57    v3_orders_2(sK3)),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f319,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK5,sK5)) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f305,f55])).
% 1.51/0.57  fof(f55,plain,(
% 1.51/0.57    l1_orders_2(sK3)),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f305,plain,(
% 1.51/0.57    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK5,sK5)) | ~l1_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | m1_subset_1(X0,u1_struct_0(sK3)) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(superposition,[],[f132,f122])).
% 1.51/0.57  fof(f122,plain,(
% 1.51/0.57    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | ~spl9_5),
% 1.51/0.57    inference(avatar_component_clause,[],[f120])).
% 1.51/0.57  fof(f120,plain,(
% 1.51/0.57    spl9_5 <=> k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 1.51/0.57  fof(f132,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.51/0.57    inference(resolution,[],[f63,f75])).
% 1.51/0.57  fof(f75,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f25])).
% 1.51/0.57  fof(f25,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.51/0.57    inference(flattening,[],[f24])).
% 1.51/0.57  fof(f24,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f3])).
% 1.51/0.57  fof(f3,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 1.51/0.57  fof(f63,plain,(
% 1.51/0.57    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f17])).
% 1.51/0.57  fof(f17,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f16])).
% 1.51/0.57  fof(f16,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f9])).
% 1.51/0.57  fof(f9,axiom,(
% 1.51/0.57    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 1.51/0.57  fof(f537,plain,(
% 1.51/0.57    ( ! [X1] : (r2_orders_2(sK3,sK4,X1) | ~r2_hidden(X1,k2_tarski(sK5,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | (~spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(subsumption_resolution,[],[f534,f505])).
% 1.51/0.57  fof(f505,plain,(
% 1.51/0.57    sP0(sK3,k2_tarski(sK5,sK5),sK4) | (~spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(resolution,[],[f426,f497])).
% 1.51/0.57  fof(f497,plain,(
% 1.51/0.57    r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (~spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(forward_demodulation,[],[f98,f122])).
% 1.51/0.57  fof(f98,plain,(
% 1.51/0.57    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~spl9_2),
% 1.51/0.57    inference(avatar_component_clause,[],[f97])).
% 1.51/0.57  fof(f97,plain,(
% 1.51/0.57    spl9_2 <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 1.51/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 1.51/0.57  fof(f426,plain,(
% 1.51/0.57    ( ! [X3] : (~r2_hidden(X3,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | sP0(sK3,k2_tarski(sK5,sK5),X3)) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f423,f328])).
% 1.51/0.57  fof(f328,plain,(
% 1.51/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f327,f57])).
% 1.51/0.57  fof(f327,plain,(
% 1.51/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f326,f51])).
% 1.51/0.57  fof(f326,plain,(
% 1.51/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f325,f52])).
% 1.51/0.57  fof(f325,plain,(
% 1.51/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f324,f53])).
% 1.51/0.57  fof(f53,plain,(
% 1.51/0.57    v4_orders_2(sK3)),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f324,plain,(
% 1.51/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f323,f54])).
% 1.51/0.57  fof(f54,plain,(
% 1.51/0.57    v5_orders_2(sK3)),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f323,plain,(
% 1.51/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f307,f55])).
% 1.51/0.57  fof(f307,plain,(
% 1.51/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 1.51/0.57    inference(superposition,[],[f139,f122])).
% 1.51/0.57  fof(f139,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (sP1(X0,k6_domain_1(u1_struct_0(X1),X2),X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 1.51/0.57    inference(duplicate_literal_removal,[],[f138])).
% 1.51/0.57  fof(f138,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (sP1(X0,k6_domain_1(u1_struct_0(X1),X2),X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.51/0.57    inference(resolution,[],[f74,f63])).
% 1.51/0.57  fof(f74,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP1(X0,X2,X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f29])).
% 1.51/0.57  fof(f29,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.51/0.57    inference(definition_folding,[],[f23,f28,f27])).
% 1.51/0.57  fof(f27,plain,(
% 1.51/0.57    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.51/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.51/0.57  fof(f28,plain,(
% 1.51/0.57    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 1.51/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.51/0.57  fof(f23,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.51/0.57    inference(flattening,[],[f22])).
% 1.51/0.57  fof(f22,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.51/0.57    inference(ennf_transformation,[],[f7])).
% 1.51/0.57  fof(f7,axiom,(
% 1.51/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 1.51/0.57  fof(f423,plain,(
% 1.51/0.57    ( ! [X3] : (~r2_hidden(X3,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | sP0(sK3,k2_tarski(sK5,sK5),X3) | ~sP1(X3,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 1.51/0.57    inference(superposition,[],[f66,f301])).
% 1.51/0.57  fof(f301,plain,(
% 1.51/0.57    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~spl9_5),
% 1.51/0.57    inference(backward_demodulation,[],[f213,f122])).
% 1.51/0.57  fof(f213,plain,(
% 1.51/0.57    k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 1.51/0.57    inference(subsumption_resolution,[],[f212,f51])).
% 1.51/0.57  fof(f212,plain,(
% 1.51/0.57    v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 1.51/0.57    inference(subsumption_resolution,[],[f211,f52])).
% 1.51/0.57  fof(f211,plain,(
% 1.51/0.57    ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 1.51/0.57    inference(subsumption_resolution,[],[f210,f53])).
% 1.51/0.57  fof(f210,plain,(
% 1.51/0.57    ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 1.51/0.57    inference(subsumption_resolution,[],[f209,f54])).
% 1.51/0.57  fof(f209,plain,(
% 1.51/0.57    ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 1.51/0.57    inference(subsumption_resolution,[],[f201,f55])).
% 1.51/0.57  fof(f201,plain,(
% 1.51/0.57    ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 1.51/0.57    inference(resolution,[],[f147,f57])).
% 1.51/0.57  fof(f147,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = a_2_1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )),
% 1.51/0.57    inference(duplicate_literal_removal,[],[f146])).
% 1.51/0.57  fof(f146,plain,(
% 1.51/0.57    ( ! [X0,X1] : (k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = a_2_1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.51/0.57    inference(resolution,[],[f61,f63])).
% 1.51/0.57  fof(f61,plain,(
% 1.51/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f15])).
% 1.51/0.57  fof(f15,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.51/0.57    inference(flattening,[],[f14])).
% 1.51/0.57  fof(f14,plain,(
% 1.51/0.57    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.51/0.57    inference(ennf_transformation,[],[f5])).
% 1.51/0.57  fof(f5,axiom,(
% 1.51/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 1.51/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 1.51/0.57  fof(f66,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f39])).
% 1.51/0.57  fof(f39,plain,(
% 1.51/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 1.51/0.57    inference(rectify,[],[f38])).
% 1.51/0.57  fof(f38,plain,(
% 1.51/0.57    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 1.51/0.57    inference(nnf_transformation,[],[f28])).
% 1.51/0.57  fof(f534,plain,(
% 1.51/0.57    ( ! [X1] : (r2_orders_2(sK3,sK4,X1) | ~r2_hidden(X1,k2_tarski(sK5,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~sP0(sK3,k2_tarski(sK5,sK5),sK4)) ) | (~spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(superposition,[],[f70,f530])).
% 1.51/0.57  fof(f530,plain,(
% 1.51/0.57    sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4) | (~spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(resolution,[],[f505,f69])).
% 1.51/0.57  fof(f69,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK7(X0,X1,X2) = X2) )),
% 1.51/0.57    inference(cnf_transformation,[],[f44])).
% 1.51/0.57  fof(f44,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.51/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f41,f43,f42])).
% 1.51/0.57  fof(f42,plain,(
% 1.51/0.57    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f43,plain,(
% 1.51/0.57    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 1.51/0.57    introduced(choice_axiom,[])).
% 1.51/0.57  fof(f41,plain,(
% 1.51/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.51/0.57    inference(rectify,[],[f40])).
% 1.51/0.57  fof(f40,plain,(
% 1.51/0.57    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 1.51/0.57    inference(nnf_transformation,[],[f27])).
% 1.51/0.57  fof(f70,plain,(
% 1.51/0.57    ( ! [X6,X2,X0,X1] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP0(X0,X1,X2)) )),
% 1.51/0.57    inference(cnf_transformation,[],[f44])).
% 1.51/0.57  fof(f496,plain,(
% 1.51/0.57    ~spl9_1 | spl9_2 | ~spl9_5),
% 1.51/0.57    inference(avatar_contradiction_clause,[],[f495])).
% 1.51/0.57  fof(f495,plain,(
% 1.51/0.57    $false | (~spl9_1 | spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(subsumption_resolution,[],[f494,f56])).
% 1.51/0.57  fof(f56,plain,(
% 1.51/0.57    m1_subset_1(sK4,u1_struct_0(sK3))),
% 1.51/0.57    inference(cnf_transformation,[],[f37])).
% 1.51/0.57  fof(f494,plain,(
% 1.51/0.57    ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(subsumption_resolution,[],[f493,f485])).
% 1.51/0.57  fof(f485,plain,(
% 1.51/0.57    ~sP0(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(resolution,[],[f425,f302])).
% 1.51/0.57  fof(f302,plain,(
% 1.51/0.57    ~r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (spl9_2 | ~spl9_5)),
% 1.51/0.57    inference(backward_demodulation,[],[f99,f122])).
% 1.51/0.57  fof(f99,plain,(
% 1.51/0.57    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | spl9_2),
% 1.51/0.57    inference(avatar_component_clause,[],[f97])).
% 1.51/0.57  fof(f425,plain,(
% 1.51/0.57    ( ! [X2] : (r2_hidden(X2,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | ~sP0(sK3,k2_tarski(sK5,sK5),X2)) ) | ~spl9_5),
% 1.51/0.57    inference(subsumption_resolution,[],[f422,f328])).
% 1.51/0.57  fof(f422,plain,(
% 1.51/0.57    ( ! [X2] : (r2_hidden(X2,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | ~sP0(sK3,k2_tarski(sK5,sK5),X2) | ~sP1(X2,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 1.51/0.57    inference(superposition,[],[f67,f301])).
% 1.51/0.57  fof(f67,plain,(
% 1.51/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f39])).
% 1.61/0.57  fof(f493,plain,(
% 1.61/0.57    sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_2 | ~spl9_5)),
% 1.61/0.57    inference(subsumption_resolution,[],[f491,f94])).
% 1.61/0.57  fof(f94,plain,(
% 1.61/0.57    r2_orders_2(sK3,sK4,sK5) | ~spl9_1),
% 1.61/0.57    inference(avatar_component_clause,[],[f93])).
% 1.61/0.57  fof(f491,plain,(
% 1.61/0.57    ~r2_orders_2(sK3,sK4,sK5) | sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (spl9_2 | ~spl9_5)),
% 1.61/0.57    inference(superposition,[],[f86,f489])).
% 1.61/0.57  fof(f489,plain,(
% 1.61/0.57    sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 1.61/0.57    inference(subsumption_resolution,[],[f488,f56])).
% 1.61/0.57  fof(f488,plain,(
% 1.61/0.57    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 1.61/0.57    inference(duplicate_literal_removal,[],[f487])).
% 1.61/0.57  fof(f487,plain,(
% 1.61/0.57    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 1.61/0.57    inference(resolution,[],[f485,f130])).
% 1.61/0.57  fof(f130,plain,(
% 1.61/0.57    ( ! [X6,X4,X7,X5] : (sP0(X4,k2_tarski(X5,X6),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | sK6(X4,k2_tarski(X5,X6),X7) = X5 | sK6(X4,k2_tarski(X5,X6),X7) = X6) )),
% 1.61/0.57    inference(resolution,[],[f87,f126])).
% 1.61/0.57  fof(f126,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.61/0.57    inference(resolution,[],[f76,f91])).
% 1.61/0.57  fof(f76,plain,(
% 1.61/0.57    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.61/0.57    inference(cnf_transformation,[],[f49])).
% 1.61/0.57  fof(f87,plain,(
% 1.61/0.57    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.61/0.57    inference(equality_resolution,[],[f72])).
% 1.61/0.57  % (24009)Refutation not found, incomplete strategy% (24009)------------------------------
% 1.61/0.57  % (24009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (24009)Termination reason: Refutation not found, incomplete strategy
% 1.61/0.57  fof(f72,plain,(
% 1.61/0.57    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | r2_hidden(sK6(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f44])).
% 1.61/0.57  
% 1.61/0.57  % (24009)Memory used [KB]: 10746
% 1.61/0.57  fof(f86,plain,(
% 1.61/0.57    ( ! [X0,X3,X1] : (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.61/0.57    inference(equality_resolution,[],[f73])).
% 1.61/0.57  % (24009)Time elapsed: 0.160 s
% 1.61/0.57  % (24009)------------------------------
% 1.61/0.57  % (24009)------------------------------
% 1.61/0.57  fof(f73,plain,(
% 1.61/0.57    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | ~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.61/0.57    inference(cnf_transformation,[],[f44])).
% 1.61/0.57  fof(f257,plain,(
% 1.61/0.57    ~spl9_3),
% 1.61/0.57    inference(avatar_contradiction_clause,[],[f252])).
% 1.61/0.57  fof(f252,plain,(
% 1.61/0.57    $false | ~spl9_3),
% 1.61/0.57    inference(resolution,[],[f251,f56])).
% 1.61/0.57  fof(f251,plain,(
% 1.61/0.57    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f250,f55])).
% 1.61/0.57  fof(f250,plain,(
% 1.61/0.57    ( ! [X0] : (~l1_orders_2(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f249,f56])).
% 1.61/0.57  fof(f249,plain,(
% 1.61/0.57    ( ! [X0] : (~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f248,f113])).
% 1.61/0.57  fof(f113,plain,(
% 1.61/0.57    v1_xboole_0(u1_struct_0(sK3)) | ~spl9_3),
% 1.61/0.57    inference(avatar_component_clause,[],[f111])).
% 1.61/0.57  fof(f111,plain,(
% 1.61/0.57    spl9_3 <=> v1_xboole_0(u1_struct_0(sK3))),
% 1.61/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 1.61/0.57  fof(f248,plain,(
% 1.61/0.57    ( ! [X0] : (~v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f247,f51])).
% 1.61/0.57  fof(f247,plain,(
% 1.61/0.57    ( ! [X0] : (v2_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f245,f52])).
% 1.61/0.57  fof(f245,plain,(
% 1.61/0.57    ( ! [X0] : (~v3_orders_2(sK3) | v2_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(X0,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(resolution,[],[f244,f140])).
% 1.61/0.57  fof(f140,plain,(
% 1.61/0.57    ( ! [X2,X0,X3,X1] : (sP0(X2,k6_domain_1(u1_struct_0(X0),X1),X3) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X2))) )),
% 1.61/0.57    inference(resolution,[],[f133,f87])).
% 1.61/0.57  fof(f133,plain,(
% 1.61/0.57    ( ! [X4,X5,X3] : (~r2_hidden(X5,k6_domain_1(u1_struct_0(X4),X3)) | ~l1_orders_2(X4) | ~v3_orders_2(X4) | v2_struct_0(X4) | ~v1_xboole_0(u1_struct_0(X4)) | ~m1_subset_1(X3,u1_struct_0(X4))) )),
% 1.61/0.57    inference(resolution,[],[f63,f84])).
% 1.61/0.57  fof(f84,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f26])).
% 1.61/0.57  fof(f26,plain,(
% 1.61/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.61/0.57    inference(ennf_transformation,[],[f4])).
% 1.61/0.57  fof(f4,axiom,(
% 1.61/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 1.61/0.57  fof(f244,plain,(
% 1.61/0.57    ( ! [X0] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f243,f56])).
% 1.61/0.57  fof(f243,plain,(
% 1.61/0.57    ( ! [X0] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f242,f51])).
% 1.61/0.57  fof(f242,plain,(
% 1.61/0.57    ( ! [X0] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f241,f52])).
% 1.61/0.57  fof(f241,plain,(
% 1.61/0.57    ( ! [X0] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f240,f53])).
% 1.61/0.57  fof(f240,plain,(
% 1.61/0.57    ( ! [X0] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f239,f54])).
% 1.61/0.57  fof(f239,plain,(
% 1.61/0.57    ( ! [X0] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f238,f55])).
% 1.61/0.57  fof(f238,plain,(
% 1.61/0.57    ( ! [X0] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(resolution,[],[f233,f139])).
% 1.61/0.57  fof(f233,plain,(
% 1.61/0.57    ( ! [X1] : (~sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1)) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f232,f56])).
% 1.61/0.57  fof(f232,plain,(
% 1.61/0.57    ( ! [X1] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1) | ~sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f231,f55])).
% 1.61/0.57  fof(f231,plain,(
% 1.61/0.57    ( ! [X1] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1) | ~sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~l1_orders_2(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) ) | ~spl9_3),
% 1.61/0.57    inference(subsumption_resolution,[],[f230,f113])).
% 1.61/0.57  fof(f230,plain,(
% 1.61/0.57    ( ! [X1] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1) | ~sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f229,f51])).
% 1.61/0.57  fof(f229,plain,(
% 1.61/0.57    ( ! [X1] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1) | ~sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | v2_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f228,f52])).
% 1.61/0.57  fof(f228,plain,(
% 1.61/0.57    ( ! [X1] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1) | ~sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f227,f53])).
% 1.61/0.57  fof(f227,plain,(
% 1.61/0.57    ( ! [X1] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1) | ~sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) )),
% 1.61/0.57    inference(subsumption_resolution,[],[f219,f54])).
% 1.61/0.57  fof(f219,plain,(
% 1.61/0.57    ( ! [X1] : (~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X1) | ~sP1(X1,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3))) )),
% 1.61/0.57    inference(resolution,[],[f214,f165])).
% 1.61/0.57  fof(f165,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.61/0.57    inference(duplicate_literal_removal,[],[f162])).
% 1.61/0.57  fof(f162,plain,(
% 1.61/0.57    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.61/0.57    inference(resolution,[],[f153,f63])).
% 1.61/0.57  fof(f153,plain,(
% 1.61/0.57    ( ! [X10,X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(X9))) | ~l1_orders_2(X9) | ~v5_orders_2(X9) | ~v4_orders_2(X9) | ~v3_orders_2(X9) | v2_struct_0(X9) | ~v1_xboole_0(u1_struct_0(X9)) | ~r2_hidden(X10,k2_orders_2(X9,X8))) )),
% 1.61/0.57    inference(resolution,[],[f65,f84])).
% 1.61/0.57  fof(f65,plain,(
% 1.61/0.57    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f21])).
% 1.61/0.57  fof(f21,plain,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.61/0.57    inference(flattening,[],[f20])).
% 1.61/0.57  fof(f20,plain,(
% 1.61/0.57    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f6])).
% 1.61/0.57  fof(f6,axiom,(
% 1.61/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 1.61/0.57  fof(f214,plain,(
% 1.61/0.57    ( ! [X0] : (r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0) | ~sP1(X0,k6_domain_1(u1_struct_0(sK3),sK4),sK3)) )),
% 1.61/0.57    inference(superposition,[],[f67,f208])).
% 1.61/0.57  fof(f208,plain,(
% 1.61/0.57    k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 1.61/0.57    inference(subsumption_resolution,[],[f207,f51])).
% 1.61/0.57  fof(f207,plain,(
% 1.61/0.57    v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 1.61/0.57    inference(subsumption_resolution,[],[f206,f52])).
% 1.61/0.57  fof(f206,plain,(
% 1.61/0.57    ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 1.61/0.57    inference(subsumption_resolution,[],[f205,f53])).
% 1.61/0.57  fof(f205,plain,(
% 1.61/0.57    ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 1.61/0.57    inference(subsumption_resolution,[],[f204,f54])).
% 1.61/0.57  fof(f204,plain,(
% 1.61/0.57    ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 1.61/0.57    inference(subsumption_resolution,[],[f200,f55])).
% 1.61/0.57  fof(f200,plain,(
% 1.61/0.57    ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 1.61/0.57    inference(resolution,[],[f147,f56])).
% 1.61/0.57  fof(f123,plain,(
% 1.61/0.57    spl9_3 | spl9_5),
% 1.61/0.57    inference(avatar_split_clause,[],[f108,f120,f111])).
% 1.61/0.57  fof(f108,plain,(
% 1.61/0.57    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | v1_xboole_0(u1_struct_0(sK3))),
% 1.61/0.57    inference(resolution,[],[f85,f57])).
% 1.61/0.57  fof(f85,plain,(
% 1.61/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 1.61/0.57    inference(definition_unfolding,[],[f64,f60])).
% 1.61/0.57  fof(f60,plain,(
% 1.61/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f2])).
% 1.61/0.57  fof(f2,axiom,(
% 1.61/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.61/0.57  fof(f64,plain,(
% 1.61/0.57    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.61/0.57    inference(cnf_transformation,[],[f19])).
% 1.61/0.57  fof(f19,plain,(
% 1.61/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.61/0.57    inference(flattening,[],[f18])).
% 1.61/0.57  fof(f18,plain,(
% 1.61/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.61/0.57    inference(ennf_transformation,[],[f8])).
% 1.61/0.57  fof(f8,axiom,(
% 1.61/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.61/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.61/0.57  fof(f101,plain,(
% 1.61/0.57    spl9_1 | spl9_2),
% 1.61/0.57    inference(avatar_split_clause,[],[f58,f97,f93])).
% 1.61/0.57  fof(f58,plain,(
% 1.61/0.57    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)),
% 1.61/0.57    inference(cnf_transformation,[],[f37])).
% 1.61/0.57  fof(f100,plain,(
% 1.61/0.57    ~spl9_1 | ~spl9_2),
% 1.61/0.57    inference(avatar_split_clause,[],[f59,f97,f93])).
% 1.61/0.57  fof(f59,plain,(
% 1.61/0.57    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)),
% 1.61/0.57    inference(cnf_transformation,[],[f37])).
% 1.61/0.57  % SZS output end Proof for theBenchmark
% 1.61/0.57  % (23987)------------------------------
% 1.61/0.57  % (23987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.61/0.57  % (23987)Termination reason: Refutation
% 1.61/0.57  
% 1.61/0.57  % (23987)Memory used [KB]: 11001
% 1.61/0.57  % (23987)Time elapsed: 0.129 s
% 1.61/0.57  % (23987)------------------------------
% 1.61/0.57  % (23987)------------------------------
% 1.61/0.57  % (23980)Success in time 0.206 s
%------------------------------------------------------------------------------
