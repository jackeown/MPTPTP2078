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
% DateTime   : Thu Dec  3 13:10:04 EST 2020

% Result     : Theorem 0.39s
% Output     : Refutation 0.66s
% Verified   : 
% Statistics : Number of formulae       :  164 (1304 expanded)
%              Number of leaves         :   25 ( 423 expanded)
%              Depth                    :   29
%              Number of atoms          :  826 (11566 expanded)
%              Number of equality atoms :   96 ( 242 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f638,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f114,f115,f139,f194,f323,f637])).

fof(f637,plain,
    ( ~ spl11_1
    | spl11_2
    | ~ spl11_5 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f635,f64])).

fof(f64,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

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

fof(f635,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl11_1
    | spl11_2
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f634,f325])).

fof(f325,plain,
    ( ~ sP1(sK4,k2_tarski(sK6,sK6),sK5)
    | spl11_2
    | ~ spl11_5 ),
    inference(resolution,[],[f324,f288])).

fof(f288,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_orders_2(sK4,k2_tarski(sK6,sK6)))
        | ~ sP1(sK4,k2_tarski(sK6,sK6),X0) )
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f286,f275])).

fof(f275,plain,
    ( ! [X2] : sP2(X2,k2_tarski(sK6,sK6),sK4)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f274,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f274,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK6,sK6),sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f273,f60])).

fof(f60,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f273,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK6,sK6),sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f272,f61])).

fof(f61,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f272,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK6,sK6),sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f271,f62])).

fof(f62,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f271,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK6,sK6),sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f260,f63])).

fof(f63,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f260,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK6,sK6),sK4)
        | ~ l1_orders_2(sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_5 ),
    inference(resolution,[],[f253,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP2(X0,X2,X1)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f26,f31,f30])).

fof(f30,plain,(
    ! [X1,X2,X0] :
      ( sP1(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X3,X4)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP1(X1,X2,X0) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f253,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f252,f59])).

fof(f252,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f251,f60])).

fof(f251,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f250,f63])).

fof(f250,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f248,f65])).

fof(f65,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f248,plain,
    ( m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_5 ),
    inference(superposition,[],[f72,f138])).

fof(f138,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6)
    | ~ spl11_5 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl11_5
  <=> k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f286,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_orders_2(sK4,k2_tarski(sK6,sK6)))
        | ~ sP1(sK4,k2_tarski(sK6,sK6),X0)
        | ~ sP2(X0,k2_tarski(sK6,sK6),sK4) )
    | ~ spl11_5 ),
    inference(superposition,[],[f82,f270])).

fof(f270,plain,
    ( k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6))
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f269,f59])).

fof(f269,plain,
    ( k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6))
    | v2_struct_0(sK4)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f268,f60])).

fof(f268,plain,
    ( k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6))
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f267,f61])).

fof(f267,plain,
    ( k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6))
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f266,f62])).

fof(f266,plain,
    ( k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6))
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f259,f63])).

fof(f259,plain,
    ( k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_5 ),
    inference(resolution,[],[f253,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

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
    inference(flattening,[],[f15])).

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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP1(X1,X2,X0) )
        & ( sP1(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f324,plain,
    ( ~ r2_hidden(sK5,k2_orders_2(sK4,k2_tarski(sK6,sK6)))
    | spl11_2
    | ~ spl11_5 ),
    inference(forward_demodulation,[],[f113,f138])).

fof(f113,plain,
    ( ~ r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl11_2
  <=> r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f634,plain,
    ( sP1(sK4,k2_tarski(sK6,sK6),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl11_1
    | spl11_2
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f620,f108])).

fof(f108,plain,
    ( r2_orders_2(sK4,sK5,sK6)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl11_1
  <=> r2_orders_2(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f620,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | sP1(sK4,k2_tarski(sK6,sK6),sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl11_2
    | ~ spl11_5 ),
    inference(superposition,[],[f100,f607])).

fof(f607,plain,
    ( sK6 = sK8(sK4,k2_tarski(sK6,sK6),sK5)
    | spl11_2
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f606,f64])).

fof(f606,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | sK6 = sK8(sK4,k2_tarski(sK6,sK6),sK5)
    | spl11_2
    | ~ spl11_5 ),
    inference(duplicate_literal_removal,[],[f599])).

fof(f599,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | sK6 = sK8(sK4,k2_tarski(sK6,sK6),sK5)
    | sK6 = sK8(sK4,k2_tarski(sK6,sK6),sK5)
    | spl11_2
    | ~ spl11_5 ),
    inference(resolution,[],[f159,f325])).

fof(f159,plain,(
    ! [X6,X4,X7,X5] :
      ( sP1(X4,k2_tarski(X5,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | sK8(X4,k2_tarski(X5,X6),X7) = X5
      | sK8(X4,k2_tarski(X5,X6),X7) = X6 ) ),
    inference(resolution,[],[f101,f142])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f90,f105])).

fof(f105,plain,(
    ! [X0,X1] : sP3(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP3(X1,X0,X2) )
      & ( sP3(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP3(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f33])).

fof(f33,plain,(
    ! [X1,X0,X2] :
      ( sP3(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f90,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
        | ( ( ( sK10(X0,X1,X2) != X0
              & sK10(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK10(X0,X1,X2),X2) )
          & ( sK10(X0,X1,X2) = X0
            | sK10(X0,X1,X2) = X1
            | r2_hidden(sK10(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f55,f56])).

fof(f56,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK10(X0,X1,X2) != X0
            & sK10(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK10(X0,X1,X2),X2) )
        & ( sK10(X0,X1,X2) = X0
          | sK10(X0,X1,X2) = X1
          | r2_hidden(sK10(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( ( sP3(X0,X1,X2)
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
        | ~ sP3(X0,X1,X2) ) ) ),
    inference(rectify,[],[f54])).

fof(f54,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
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
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X1,X0,X2] :
      ( ( sP3(X1,X0,X2)
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
        | ~ sP3(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f101,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | sP1(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f87])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | r2_hidden(sK8(X0,X1,X3),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,X3,sK8(X0,X1,X3))
              & r2_hidden(sK8(X0,X1,X3),X1)
              & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,sK9(X0,X1,X2),X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK9(X0,X1,X2) = X2
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f49,f51,f50])).

fof(f50,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK8(X0,X1,X3))
        & r2_hidden(sK8(X0,X1,X3),X1)
        & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X5,X6)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,sK9(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK9(X0,X1,X2) = X2
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
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
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(rectify,[],[f48])).

fof(f48,plain,(
    ! [X1,X2,X0] :
      ( ( sP1(X1,X2,X0)
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
        | ~ sP1(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_orders_2(X0,X3,sK8(X0,X1,X3))
      | sP1(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | ~ r2_orders_2(X0,X3,sK8(X0,X1,X3))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f323,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f321,f65])).

fof(f321,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f315,f109])).

fof(f109,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f315,plain,
    ( r2_orders_2(sK4,sK5,sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(resolution,[],[f309,f119])).

fof(f119,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f104,f105])).

fof(f104,plain,(
    ! [X4,X2,X0] :
      ( ~ sP3(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f91])).

fof(f91,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f309,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK6,sK6))
        | r2_orders_2(sK4,sK5,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK4)) )
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f306,f300])).

fof(f300,plain,
    ( sP1(sK4,k2_tarski(sK6,sK6),sK5)
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(resolution,[],[f289,f246])).

fof(f246,plain,
    ( r2_hidden(sK5,k2_orders_2(sK4,k2_tarski(sK6,sK6)))
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(backward_demodulation,[],[f112,f138])).

fof(f112,plain,
    ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f289,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK4,k2_tarski(sK6,sK6)))
        | sP1(sK4,k2_tarski(sK6,sK6),X1) )
    | ~ spl11_5 ),
    inference(subsumption_resolution,[],[f287,f275])).

fof(f287,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK4,k2_tarski(sK6,sK6)))
        | sP1(sK4,k2_tarski(sK6,sK6),X1)
        | ~ sP2(X1,k2_tarski(sK6,sK6),sK4) )
    | ~ spl11_5 ),
    inference(superposition,[],[f81,f270])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f306,plain,
    ( ! [X1] :
        ( r2_orders_2(sK4,sK5,X1)
        | ~ r2_hidden(X1,k2_tarski(sK6,sK6))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ sP1(sK4,k2_tarski(sK6,sK6),sK5) )
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(superposition,[],[f85,f303])).

fof(f303,plain,
    ( sK5 = sK9(sK4,k2_tarski(sK6,sK6),sK5)
    | ~ spl11_2
    | ~ spl11_5 ),
    inference(resolution,[],[f300,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sK9(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X0,sK9(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f194,plain,(
    ~ spl11_3 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f192,f129])).

fof(f129,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl11_3
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f192,plain,(
    ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f178,f147])).

fof(f147,plain,(
    ! [X4,X5,X3] :
      ( ~ sP0(X4,X5,X3)
      | ~ v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_xboole_0(u1_struct_0(X3))
      | ~ sP0(X4,X5,X3)
      | ~ sP0(X4,X5,X3) ) ),
    inference(resolution,[],[f121,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK7(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,sK7(X0,X1,X2))
        & r2_hidden(X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK7(X0,X1,X2),X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).

fof(f43,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
     => ( r2_hidden(X0,sK7(X0,X1,X2))
        & r2_hidden(X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK7(X0,X1,X2),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_hidden(X3,sK7(X0,X1,X2))
      | ~ v1_xboole_0(u1_struct_0(X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(resolution,[],[f74,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f178,plain,(
    sP0(sK5,sK5,sK4) ),
    inference(subsumption_resolution,[],[f177,f60])).

fof(f177,plain,
    ( sP0(sK5,sK5,sK4)
    | ~ v3_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f176,f63])).

fof(f176,plain,
    ( sP0(sK5,sK5,sK4)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f175,f64])).

fof(f175,plain,
    ( sP0(sK5,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(duplicate_literal_removal,[],[f172])).

fof(f172,plain,
    ( sP0(sK5,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(resolution,[],[f78,f154])).

fof(f154,plain,(
    r1_orders_2(sK4,sK5,sK5) ),
    inference(subsumption_resolution,[],[f153,f59])).

fof(f153,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f152,f60])).

fof(f152,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f149,f63])).

fof(f149,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f70,f64])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | sP0(X2,X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( sP0(X2,X1,X0)
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X3] :
                      ( ~ r2_hidden(X2,X3)
                      | ~ r2_hidden(X1,X3)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X3,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(rectify,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( sP0(X2,X1,X0)
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(definition_folding,[],[f22,f28])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ? [X3] :
                      ( r2_hidden(X2,X3)
                      & r2_hidden(X1,X3)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                      & v6_orders_2(X3,X0) )
                  | ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2) ) )
                & ( r1_orders_2(X0,X2,X1)
                  | r1_orders_2(X0,X1,X2)
                  | ! [X4] :
                      ( ~ r2_hidden(X2,X4)
                      | ~ r2_hidden(X1,X4)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                      | ~ v6_orders_2(X4,X0) ) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X4] :
                        ( r2_hidden(X2,X4)
                        & r2_hidden(X1,X4)
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X4,X0) ) ) ) ) ) ) ),
    inference(rectify,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & v6_orders_2(X3,X0) )
                       => ~ ( r2_hidden(X2,X3)
                            & r2_hidden(X1,X3) ) )
                    & ( r1_orders_2(X0,X2,X1)
                      | r1_orders_2(X0,X1,X2) ) )
                & ~ ( ~ r1_orders_2(X0,X2,X1)
                    & ~ r1_orders_2(X0,X1,X2)
                    & ? [X3] :
                        ( r2_hidden(X2,X3)
                        & r2_hidden(X1,X3)
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & v6_orders_2(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).

fof(f139,plain,
    ( spl11_3
    | spl11_5 ),
    inference(avatar_split_clause,[],[f123,f136,f127])).

fof(f123,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f99,f65])).

fof(f99,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f80,f68])).

fof(f68,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f80,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f115,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f66,f111,f107])).

fof(f66,plain,
    ( r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    | r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f114,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f67,f111,f107])).

fof(f67,plain,
    ( ~ r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))
    | ~ r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n017.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:23:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.37  ipcrm: permission denied for id (806060032)
% 0.14/0.37  ipcrm: permission denied for id (808747009)
% 0.14/0.37  ipcrm: permission denied for id (806092802)
% 0.14/0.37  ipcrm: permission denied for id (811696132)
% 0.14/0.37  ipcrm: permission denied for id (811728901)
% 0.14/0.37  ipcrm: permission denied for id (806223878)
% 0.14/0.38  ipcrm: permission denied for id (806256647)
% 0.14/0.38  ipcrm: permission denied for id (806289416)
% 0.14/0.38  ipcrm: permission denied for id (806322185)
% 0.14/0.38  ipcrm: permission denied for id (808878090)
% 0.14/0.38  ipcrm: permission denied for id (806387723)
% 0.14/0.38  ipcrm: permission denied for id (806420492)
% 0.21/0.38  ipcrm: permission denied for id (811794446)
% 0.21/0.39  ipcrm: permission denied for id (806486031)
% 0.21/0.39  ipcrm: permission denied for id (809009168)
% 0.21/0.39  ipcrm: permission denied for id (806551569)
% 0.21/0.39  ipcrm: permission denied for id (813203474)
% 0.21/0.39  ipcrm: permission denied for id (811859987)
% 0.21/0.39  ipcrm: permission denied for id (813236244)
% 0.21/0.39  ipcrm: permission denied for id (809140245)
% 0.21/0.39  ipcrm: permission denied for id (811925526)
% 0.21/0.40  ipcrm: permission denied for id (809205783)
% 0.21/0.40  ipcrm: permission denied for id (806715416)
% 0.21/0.40  ipcrm: permission denied for id (809238553)
% 0.21/0.40  ipcrm: permission denied for id (813269018)
% 0.21/0.40  ipcrm: permission denied for id (806748187)
% 0.21/0.40  ipcrm: permission denied for id (809304092)
% 0.21/0.40  ipcrm: permission denied for id (811991069)
% 0.21/0.40  ipcrm: permission denied for id (809369630)
% 0.21/0.41  ipcrm: permission denied for id (809402399)
% 0.21/0.41  ipcrm: permission denied for id (806813728)
% 0.21/0.41  ipcrm: permission denied for id (809435169)
% 0.21/0.41  ipcrm: permission denied for id (806846498)
% 0.21/0.41  ipcrm: permission denied for id (806912036)
% 0.21/0.41  ipcrm: permission denied for id (813334565)
% 0.21/0.42  ipcrm: permission denied for id (806977575)
% 0.21/0.42  ipcrm: permission denied for id (809566248)
% 0.21/0.42  ipcrm: permission denied for id (809631786)
% 0.21/0.42  ipcrm: permission denied for id (812154923)
% 0.21/0.42  ipcrm: permission denied for id (809697324)
% 0.21/0.42  ipcrm: permission denied for id (809730093)
% 0.21/0.43  ipcrm: permission denied for id (807075887)
% 0.21/0.43  ipcrm: permission denied for id (813465648)
% 0.21/0.43  ipcrm: permission denied for id (809828401)
% 0.21/0.43  ipcrm: permission denied for id (809861170)
% 0.21/0.43  ipcrm: permission denied for id (809893939)
% 0.21/0.43  ipcrm: permission denied for id (812286005)
% 0.21/0.44  ipcrm: permission denied for id (807174198)
% 0.21/0.44  ipcrm: permission denied for id (809992247)
% 0.21/0.44  ipcrm: permission denied for id (813531192)
% 0.21/0.44  ipcrm: permission denied for id (812384313)
% 0.21/0.44  ipcrm: permission denied for id (812417082)
% 0.21/0.44  ipcrm: permission denied for id (807239739)
% 0.21/0.44  ipcrm: permission denied for id (810156092)
% 0.21/0.44  ipcrm: permission denied for id (812449853)
% 0.21/0.45  ipcrm: permission denied for id (807305278)
% 0.21/0.45  ipcrm: permission denied for id (810221631)
% 0.21/0.45  ipcrm: permission denied for id (807338048)
% 0.21/0.45  ipcrm: permission denied for id (812482625)
% 0.21/0.45  ipcrm: permission denied for id (813563970)
% 0.21/0.45  ipcrm: permission denied for id (810319939)
% 0.21/0.45  ipcrm: permission denied for id (807403588)
% 0.21/0.46  ipcrm: permission denied for id (807436357)
% 0.21/0.46  ipcrm: permission denied for id (807469126)
% 0.21/0.46  ipcrm: permission denied for id (812548167)
% 0.21/0.46  ipcrm: permission denied for id (810385480)
% 0.21/0.46  ipcrm: permission denied for id (812580937)
% 0.21/0.46  ipcrm: permission denied for id (807600202)
% 0.21/0.46  ipcrm: permission denied for id (807632971)
% 0.21/0.47  ipcrm: permission denied for id (810582096)
% 0.21/0.47  ipcrm: permission denied for id (810614865)
% 0.21/0.47  ipcrm: permission denied for id (810647634)
% 0.21/0.47  ipcrm: permission denied for id (812777555)
% 0.21/0.47  ipcrm: permission denied for id (813727828)
% 0.21/0.48  ipcrm: permission denied for id (810745941)
% 0.21/0.48  ipcrm: permission denied for id (810778710)
% 0.21/0.48  ipcrm: permission denied for id (810811479)
% 0.21/0.48  ipcrm: permission denied for id (810844248)
% 0.21/0.48  ipcrm: permission denied for id (810877017)
% 0.21/0.48  ipcrm: permission denied for id (812843098)
% 0.21/0.48  ipcrm: permission denied for id (810942555)
% 0.21/0.48  ipcrm: permission denied for id (810975324)
% 0.21/0.49  ipcrm: permission denied for id (807862365)
% 0.21/0.49  ipcrm: permission denied for id (807927902)
% 0.21/0.49  ipcrm: permission denied for id (812875871)
% 0.21/0.49  ipcrm: permission denied for id (811040864)
% 0.21/0.49  ipcrm: permission denied for id (811073633)
% 0.21/0.49  ipcrm: permission denied for id (811139171)
% 0.21/0.50  ipcrm: permission denied for id (812941412)
% 0.21/0.50  ipcrm: permission denied for id (813793381)
% 0.21/0.50  ipcrm: permission denied for id (813826150)
% 0.21/0.50  ipcrm: permission denied for id (811303016)
% 0.21/0.50  ipcrm: permission denied for id (811335785)
% 0.21/0.50  ipcrm: permission denied for id (811368554)
% 0.21/0.50  ipcrm: permission denied for id (808190059)
% 0.21/0.50  ipcrm: permission denied for id (808222828)
% 0.21/0.51  ipcrm: permission denied for id (811401325)
% 0.21/0.51  ipcrm: permission denied for id (808321134)
% 0.21/0.51  ipcrm: permission denied for id (808353903)
% 0.21/0.51  ipcrm: permission denied for id (808386672)
% 0.21/0.51  ipcrm: permission denied for id (808419441)
% 0.21/0.51  ipcrm: permission denied for id (808452210)
% 0.21/0.51  ipcrm: permission denied for id (808484979)
% 0.21/0.52  ipcrm: permission denied for id (808517748)
% 0.21/0.52  ipcrm: permission denied for id (808550517)
% 0.21/0.52  ipcrm: permission denied for id (811466871)
% 0.21/0.52  ipcrm: permission denied for id (811499640)
% 0.21/0.52  ipcrm: permission denied for id (811532409)
% 0.35/0.52  ipcrm: permission denied for id (808583291)
% 0.35/0.53  ipcrm: permission denied for id (811597948)
% 0.35/0.53  ipcrm: permission denied for id (808648829)
% 0.35/0.53  ipcrm: permission denied for id (808681598)
% 0.35/0.53  ipcrm: permission denied for id (808714367)
% 0.39/0.64  % (8871)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.39/0.67  % (8879)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.39/0.67  % (8877)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.39/0.68  % (8879)Refutation not found, incomplete strategy% (8879)------------------------------
% 0.39/0.68  % (8879)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.68  % (8879)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.68  
% 0.39/0.68  % (8879)Memory used [KB]: 10746
% 0.39/0.68  % (8879)Time elapsed: 0.110 s
% 0.39/0.68  % (8879)------------------------------
% 0.39/0.68  % (8879)------------------------------
% 0.39/0.68  % (8869)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.39/0.68  % (8875)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.39/0.68  % (8898)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.39/0.68  % (8890)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.39/0.69  % (8880)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.39/0.69  % (8874)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.39/0.69  % (8878)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.39/0.69  % (8885)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.39/0.69  % (8897)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.39/0.69  % (8899)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.39/0.70  % (8873)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.39/0.70  % (8886)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.39/0.70  % (8870)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.39/0.70  % (8892)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.39/0.70  % (8893)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.39/0.70  % (8899)Refutation not found, incomplete strategy% (8899)------------------------------
% 0.39/0.70  % (8899)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.70  % (8899)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.70  
% 0.39/0.70  % (8899)Memory used [KB]: 10746
% 0.39/0.70  % (8899)Time elapsed: 0.133 s
% 0.39/0.70  % (8899)------------------------------
% 0.39/0.70  % (8899)------------------------------
% 0.39/0.70  % (8887)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.39/0.70  % (8895)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.39/0.70  % (8872)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.39/0.71  % (8876)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.39/0.71  % (8889)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.39/0.71  % (8891)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.39/0.71  % (8884)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.39/0.71  % (8882)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.39/0.71  % (8888)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.39/0.72  % (8881)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.39/0.72  % (8886)Refutation not found, incomplete strategy% (8886)------------------------------
% 0.39/0.72  % (8886)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.72  % (8886)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.72  
% 0.39/0.72  % (8886)Memory used [KB]: 10746
% 0.39/0.72  % (8886)Time elapsed: 0.145 s
% 0.39/0.72  % (8886)------------------------------
% 0.39/0.72  % (8886)------------------------------
% 0.39/0.72  % (8894)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.39/0.72  % (8900)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.39/0.72  % (8900)Refutation not found, incomplete strategy% (8900)------------------------------
% 0.39/0.72  % (8900)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.72  % (8900)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.72  
% 0.39/0.72  % (8900)Memory used [KB]: 1663
% 0.39/0.72  % (8900)Time elapsed: 0.002 s
% 0.39/0.72  % (8900)------------------------------
% 0.39/0.72  % (8900)------------------------------
% 0.39/0.72  % (8873)Refutation not found, incomplete strategy% (8873)------------------------------
% 0.39/0.72  % (8873)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.72  % (8873)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.72  
% 0.39/0.72  % (8873)Memory used [KB]: 1918
% 0.39/0.72  % (8873)Time elapsed: 0.145 s
% 0.39/0.72  % (8873)------------------------------
% 0.39/0.72  % (8873)------------------------------
% 0.39/0.73  % (8881)Refutation not found, incomplete strategy% (8881)------------------------------
% 0.39/0.73  % (8881)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.39/0.73  % (8881)Termination reason: Refutation not found, incomplete strategy
% 0.39/0.73  
% 0.39/0.73  % (8881)Memory used [KB]: 10746
% 0.39/0.73  % (8881)Time elapsed: 0.158 s
% 0.39/0.73  % (8881)------------------------------
% 0.39/0.73  % (8881)------------------------------
% 0.39/0.73  % (8875)Refutation found. Thanks to Tanya!
% 0.39/0.73  % SZS status Theorem for theBenchmark
% 0.66/0.74  % SZS output start Proof for theBenchmark
% 0.66/0.74  fof(f638,plain,(
% 0.66/0.74    $false),
% 0.66/0.74    inference(avatar_sat_refutation,[],[f114,f115,f139,f194,f323,f637])).
% 0.66/0.74  fof(f637,plain,(
% 0.66/0.74    ~spl11_1 | spl11_2 | ~spl11_5),
% 0.66/0.74    inference(avatar_contradiction_clause,[],[f636])).
% 0.66/0.74  fof(f636,plain,(
% 0.66/0.74    $false | (~spl11_1 | spl11_2 | ~spl11_5)),
% 0.66/0.74    inference(subsumption_resolution,[],[f635,f64])).
% 0.66/0.74  fof(f64,plain,(
% 0.66/0.74    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.66/0.74    inference(cnf_transformation,[],[f40])).
% 0.66/0.74  fof(f40,plain,(
% 0.66/0.74    (((~r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) | ~r2_orders_2(sK4,sK5,sK6)) & (r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) | r2_orders_2(sK4,sK5,sK6)) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 0.66/0.74    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).
% 0.66/0.74  fof(f37,plain,(
% 0.66/0.74    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2))) | ~r2_orders_2(sK4,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2))) | r2_orders_2(sK4,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 0.66/0.74    introduced(choice_axiom,[])).
% 0.66/0.74  fof(f38,plain,(
% 0.66/0.74    ? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2))) | ~r2_orders_2(sK4,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2))) | r2_orders_2(sK4,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) => (? [X2] : ((~r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2))) | ~r2_orders_2(sK4,sK5,X2)) & (r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2))) | r2_orders_2(sK4,sK5,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4)))),
% 0.66/0.74    introduced(choice_axiom,[])).
% 0.66/0.74  fof(f39,plain,(
% 0.66/0.74    ? [X2] : ((~r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2))) | ~r2_orders_2(sK4,sK5,X2)) & (r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X2))) | r2_orders_2(sK4,sK5,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) => ((~r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) | ~r2_orders_2(sK4,sK5,sK6)) & (r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) | r2_orders_2(sK4,sK5,sK6)) & m1_subset_1(sK6,u1_struct_0(sK4)))),
% 0.66/0.74    introduced(choice_axiom,[])).
% 0.66/0.74  fof(f36,plain,(
% 0.66/0.74    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.66/0.74    inference(flattening,[],[f35])).
% 0.66/0.74  fof(f35,plain,(
% 0.66/0.74    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.66/0.74    inference(nnf_transformation,[],[f14])).
% 0.66/0.75  fof(f14,plain,(
% 0.66/0.75    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.66/0.75    inference(flattening,[],[f13])).
% 0.66/0.75  fof(f13,plain,(
% 0.66/0.75    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.66/0.75    inference(ennf_transformation,[],[f11])).
% 0.66/0.75  fof(f11,negated_conjecture,(
% 0.66/0.75    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.66/0.75    inference(negated_conjecture,[],[f10])).
% 0.66/0.75  fof(f10,conjecture,(
% 0.66/0.75    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).
% 0.66/0.75  fof(f635,plain,(
% 0.66/0.75    ~m1_subset_1(sK5,u1_struct_0(sK4)) | (~spl11_1 | spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(subsumption_resolution,[],[f634,f325])).
% 0.66/0.75  fof(f325,plain,(
% 0.66/0.75    ~sP1(sK4,k2_tarski(sK6,sK6),sK5) | (spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(resolution,[],[f324,f288])).
% 0.66/0.75  fof(f288,plain,(
% 0.66/0.75    ( ! [X0] : (r2_hidden(X0,k2_orders_2(sK4,k2_tarski(sK6,sK6))) | ~sP1(sK4,k2_tarski(sK6,sK6),X0)) ) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f286,f275])).
% 0.66/0.75  fof(f275,plain,(
% 0.66/0.75    ( ! [X2] : (sP2(X2,k2_tarski(sK6,sK6),sK4)) ) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f274,f59])).
% 0.66/0.75  fof(f59,plain,(
% 0.66/0.75    ~v2_struct_0(sK4)),
% 0.66/0.75    inference(cnf_transformation,[],[f40])).
% 0.66/0.75  fof(f274,plain,(
% 0.66/0.75    ( ! [X2] : (sP2(X2,k2_tarski(sK6,sK6),sK4) | v2_struct_0(sK4)) ) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f273,f60])).
% 0.66/0.75  fof(f60,plain,(
% 0.66/0.75    v3_orders_2(sK4)),
% 0.66/0.75    inference(cnf_transformation,[],[f40])).
% 0.66/0.75  fof(f273,plain,(
% 0.66/0.75    ( ! [X2] : (sP2(X2,k2_tarski(sK6,sK6),sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f272,f61])).
% 0.66/0.75  fof(f61,plain,(
% 0.66/0.75    v4_orders_2(sK4)),
% 0.66/0.75    inference(cnf_transformation,[],[f40])).
% 0.66/0.75  fof(f272,plain,(
% 0.66/0.75    ( ! [X2] : (sP2(X2,k2_tarski(sK6,sK6),sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f271,f62])).
% 0.66/0.75  fof(f62,plain,(
% 0.66/0.75    v5_orders_2(sK4)),
% 0.66/0.75    inference(cnf_transformation,[],[f40])).
% 0.66/0.75  fof(f271,plain,(
% 0.66/0.75    ( ! [X2] : (sP2(X2,k2_tarski(sK6,sK6),sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f260,f63])).
% 0.66/0.75  fof(f63,plain,(
% 0.66/0.75    l1_orders_2(sK4)),
% 0.66/0.75    inference(cnf_transformation,[],[f40])).
% 0.66/0.75  fof(f260,plain,(
% 0.66/0.75    ( ! [X2] : (sP2(X2,k2_tarski(sK6,sK6),sK4) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl11_5),
% 0.66/0.75    inference(resolution,[],[f253,f89])).
% 0.66/0.75  fof(f89,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP2(X0,X2,X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f32])).
% 0.66/0.75  fof(f32,plain,(
% 0.66/0.75    ! [X0,X1,X2] : (sP2(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.66/0.75    inference(definition_folding,[],[f26,f31,f30])).
% 0.66/0.75  fof(f30,plain,(
% 0.66/0.75    ! [X1,X2,X0] : (sP1(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.66/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.66/0.75  fof(f31,plain,(
% 0.66/0.75    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP1(X1,X2,X0)) | ~sP2(X0,X2,X1))),
% 0.66/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.66/0.75  fof(f26,plain,(
% 0.66/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.66/0.75    inference(flattening,[],[f25])).
% 0.66/0.75  fof(f25,plain,(
% 0.66/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.66/0.75    inference(ennf_transformation,[],[f5])).
% 0.66/0.75  fof(f5,axiom,(
% 0.66/0.75    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.66/0.75  fof(f253,plain,(
% 0.66/0.75    m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f252,f59])).
% 0.66/0.75  fof(f252,plain,(
% 0.66/0.75    m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) | v2_struct_0(sK4) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f251,f60])).
% 0.66/0.75  fof(f251,plain,(
% 0.66/0.75    m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f250,f63])).
% 0.66/0.75  fof(f250,plain,(
% 0.66/0.75    m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f248,f65])).
% 0.66/0.75  fof(f65,plain,(
% 0.66/0.75    m1_subset_1(sK6,u1_struct_0(sK4))),
% 0.66/0.75    inference(cnf_transformation,[],[f40])).
% 0.66/0.75  fof(f248,plain,(
% 0.66/0.75    m1_subset_1(k2_tarski(sK6,sK6),k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_5),
% 0.66/0.75    inference(superposition,[],[f72,f138])).
% 0.66/0.75  fof(f138,plain,(
% 0.66/0.75    k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) | ~spl11_5),
% 0.66/0.75    inference(avatar_component_clause,[],[f136])).
% 0.66/0.75  fof(f136,plain,(
% 0.66/0.75    spl11_5 <=> k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6)),
% 0.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_5])])).
% 0.66/0.75  fof(f72,plain,(
% 0.66/0.75    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f20])).
% 0.66/0.75  fof(f20,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.66/0.75    inference(flattening,[],[f19])).
% 0.66/0.75  fof(f19,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.66/0.75    inference(ennf_transformation,[],[f8])).
% 0.66/0.75  fof(f8,axiom,(
% 0.66/0.75    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 0.66/0.75  fof(f286,plain,(
% 0.66/0.75    ( ! [X0] : (r2_hidden(X0,k2_orders_2(sK4,k2_tarski(sK6,sK6))) | ~sP1(sK4,k2_tarski(sK6,sK6),X0) | ~sP2(X0,k2_tarski(sK6,sK6),sK4)) ) | ~spl11_5),
% 0.66/0.75    inference(superposition,[],[f82,f270])).
% 0.66/0.75  fof(f270,plain,(
% 0.66/0.75    k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6)) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f269,f59])).
% 0.66/0.75  fof(f269,plain,(
% 0.66/0.75    k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6)) | v2_struct_0(sK4) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f268,f60])).
% 0.66/0.75  fof(f268,plain,(
% 0.66/0.75    k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6)) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f267,f61])).
% 0.66/0.75  fof(f267,plain,(
% 0.66/0.75    k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6)) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f266,f62])).
% 0.66/0.75  fof(f266,plain,(
% 0.66/0.75    k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6)) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f259,f63])).
% 0.66/0.75  fof(f259,plain,(
% 0.66/0.75    k2_orders_2(sK4,k2_tarski(sK6,sK6)) = a_2_1_orders_2(sK4,k2_tarski(sK6,sK6)) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_5),
% 0.66/0.75    inference(resolution,[],[f253,f69])).
% 0.66/0.75  fof(f69,plain,(
% 0.66/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f16])).
% 0.66/0.75  fof(f16,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.66/0.75    inference(flattening,[],[f15])).
% 0.66/0.75  fof(f15,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.66/0.75    inference(ennf_transformation,[],[f4])).
% 0.66/0.75  fof(f4,axiom,(
% 0.66/0.75    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.66/0.75  fof(f82,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f47])).
% 0.66/0.75  fof(f47,plain,(
% 0.66/0.75    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP2(X0,X1,X2))),
% 0.66/0.75    inference(rectify,[],[f46])).
% 0.66/0.75  fof(f46,plain,(
% 0.66/0.75    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP1(X1,X2,X0)) & (sP1(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP2(X0,X2,X1))),
% 0.66/0.75    inference(nnf_transformation,[],[f31])).
% 0.66/0.75  fof(f324,plain,(
% 0.66/0.75    ~r2_hidden(sK5,k2_orders_2(sK4,k2_tarski(sK6,sK6))) | (spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(forward_demodulation,[],[f113,f138])).
% 0.66/0.75  fof(f113,plain,(
% 0.66/0.75    ~r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) | spl11_2),
% 0.66/0.75    inference(avatar_component_clause,[],[f111])).
% 0.66/0.75  fof(f111,plain,(
% 0.66/0.75    spl11_2 <=> r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6)))),
% 0.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.66/0.75  fof(f634,plain,(
% 0.66/0.75    sP1(sK4,k2_tarski(sK6,sK6),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | (~spl11_1 | spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(subsumption_resolution,[],[f620,f108])).
% 0.66/0.75  fof(f108,plain,(
% 0.66/0.75    r2_orders_2(sK4,sK5,sK6) | ~spl11_1),
% 0.66/0.75    inference(avatar_component_clause,[],[f107])).
% 0.66/0.75  fof(f107,plain,(
% 0.66/0.75    spl11_1 <=> r2_orders_2(sK4,sK5,sK6)),
% 0.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.66/0.75  fof(f620,plain,(
% 0.66/0.75    ~r2_orders_2(sK4,sK5,sK6) | sP1(sK4,k2_tarski(sK6,sK6),sK5) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | (spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(superposition,[],[f100,f607])).
% 0.66/0.75  fof(f607,plain,(
% 0.66/0.75    sK6 = sK8(sK4,k2_tarski(sK6,sK6),sK5) | (spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(subsumption_resolution,[],[f606,f64])).
% 0.66/0.75  fof(f606,plain,(
% 0.66/0.75    ~m1_subset_1(sK5,u1_struct_0(sK4)) | sK6 = sK8(sK4,k2_tarski(sK6,sK6),sK5) | (spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(duplicate_literal_removal,[],[f599])).
% 0.66/0.75  fof(f599,plain,(
% 0.66/0.75    ~m1_subset_1(sK5,u1_struct_0(sK4)) | sK6 = sK8(sK4,k2_tarski(sK6,sK6),sK5) | sK6 = sK8(sK4,k2_tarski(sK6,sK6),sK5) | (spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(resolution,[],[f159,f325])).
% 0.66/0.75  fof(f159,plain,(
% 0.66/0.75    ( ! [X6,X4,X7,X5] : (sP1(X4,k2_tarski(X5,X6),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | sK8(X4,k2_tarski(X5,X6),X7) = X5 | sK8(X4,k2_tarski(X5,X6),X7) = X6) )),
% 0.66/0.75    inference(resolution,[],[f101,f142])).
% 0.66/0.75  fof(f142,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.66/0.75    inference(resolution,[],[f90,f105])).
% 0.66/0.75  fof(f105,plain,(
% 0.66/0.75    ( ! [X0,X1] : (sP3(X1,X0,k2_tarski(X0,X1))) )),
% 0.66/0.75    inference(equality_resolution,[],[f96])).
% 0.66/0.75  fof(f96,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.66/0.75    inference(cnf_transformation,[],[f58])).
% 0.66/0.75  fof(f58,plain,(
% 0.66/0.75    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.66/0.75    inference(nnf_transformation,[],[f34])).
% 0.66/0.75  fof(f34,plain,(
% 0.66/0.75    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP3(X1,X0,X2))),
% 0.66/0.75    inference(definition_folding,[],[f1,f33])).
% 0.66/0.75  fof(f33,plain,(
% 0.66/0.75    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.66/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.66/0.75  fof(f1,axiom,(
% 0.66/0.75    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.66/0.75  fof(f90,plain,(
% 0.66/0.75    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.66/0.75    inference(cnf_transformation,[],[f57])).
% 0.66/0.75  fof(f57,plain,(
% 0.66/0.75    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (((sK10(X0,X1,X2) != X0 & sK10(X0,X1,X2) != X1) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sK10(X0,X1,X2) = X0 | sK10(X0,X1,X2) = X1 | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.66/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f55,f56])).
% 0.66/0.75  fof(f56,plain,(
% 0.66/0.75    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK10(X0,X1,X2) != X0 & sK10(X0,X1,X2) != X1) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sK10(X0,X1,X2) = X0 | sK10(X0,X1,X2) = X1 | r2_hidden(sK10(X0,X1,X2),X2))))),
% 0.66/0.75    introduced(choice_axiom,[])).
% 0.66/0.75  fof(f55,plain,(
% 0.66/0.75    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.66/0.75    inference(rectify,[],[f54])).
% 0.66/0.75  fof(f54,plain,(
% 0.66/0.75    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP3(X1,X0,X2)))),
% 0.66/0.75    inference(flattening,[],[f53])).
% 0.66/0.75  fof(f53,plain,(
% 0.66/0.75    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP3(X1,X0,X2)))),
% 0.66/0.75    inference(nnf_transformation,[],[f33])).
% 0.66/0.75  fof(f101,plain,(
% 0.66/0.75    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | sP1(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.66/0.75    inference(equality_resolution,[],[f87])).
% 0.66/0.75  fof(f87,plain,(
% 0.66/0.75    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2) | r2_hidden(sK8(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.66/0.75    inference(cnf_transformation,[],[f52])).
% 0.66/0.75  fof(f52,plain,(
% 0.66/0.75    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK8(X0,X1,X3)) & r2_hidden(sK8(X0,X1,X3),X1) & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK9(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))) | ~sP1(X0,X1,X2)))),
% 0.66/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f49,f51,f50])).
% 0.66/0.75  fof(f50,plain,(
% 0.66/0.75    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK8(X0,X1,X3)) & r2_hidden(sK8(X0,X1,X3),X1) & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0))))),
% 0.66/0.75    introduced(choice_axiom,[])).
% 0.66/0.75  fof(f51,plain,(
% 0.66/0.75    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK9(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))))),
% 0.66/0.75    introduced(choice_axiom,[])).
% 0.66/0.75  fof(f49,plain,(
% 0.66/0.75    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP1(X0,X1,X2)))),
% 0.66/0.75    inference(rectify,[],[f48])).
% 0.66/0.75  fof(f48,plain,(
% 0.66/0.75    ! [X1,X2,X0] : ((sP1(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X1,X2,X0)))),
% 0.66/0.75    inference(nnf_transformation,[],[f30])).
% 0.66/0.75  fof(f100,plain,(
% 0.66/0.75    ( ! [X0,X3,X1] : (~r2_orders_2(X0,X3,sK8(X0,X1,X3)) | sP1(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.66/0.75    inference(equality_resolution,[],[f88])).
% 0.66/0.75  fof(f88,plain,(
% 0.66/0.75    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2) | ~r2_orders_2(X0,X3,sK8(X0,X1,X3)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.66/0.75    inference(cnf_transformation,[],[f52])).
% 0.66/0.75  fof(f323,plain,(
% 0.66/0.75    spl11_1 | ~spl11_2 | ~spl11_5),
% 0.66/0.75    inference(avatar_contradiction_clause,[],[f322])).
% 0.66/0.75  fof(f322,plain,(
% 0.66/0.75    $false | (spl11_1 | ~spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(subsumption_resolution,[],[f321,f65])).
% 0.66/0.75  fof(f321,plain,(
% 0.66/0.75    ~m1_subset_1(sK6,u1_struct_0(sK4)) | (spl11_1 | ~spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(subsumption_resolution,[],[f315,f109])).
% 0.66/0.75  fof(f109,plain,(
% 0.66/0.75    ~r2_orders_2(sK4,sK5,sK6) | spl11_1),
% 0.66/0.75    inference(avatar_component_clause,[],[f107])).
% 0.66/0.75  fof(f315,plain,(
% 0.66/0.75    r2_orders_2(sK4,sK5,sK6) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | (~spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(resolution,[],[f309,f119])).
% 0.66/0.75  fof(f119,plain,(
% 0.66/0.75    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.66/0.75    inference(resolution,[],[f104,f105])).
% 0.66/0.75  fof(f104,plain,(
% 0.66/0.75    ( ! [X4,X2,X0] : (~sP3(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.66/0.75    inference(equality_resolution,[],[f91])).
% 0.66/0.75  fof(f91,plain,(
% 0.66/0.75    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP3(X0,X1,X2)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f57])).
% 0.66/0.75  fof(f309,plain,(
% 0.66/0.75    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK6,sK6)) | r2_orders_2(sK4,sK5,X1) | ~m1_subset_1(X1,u1_struct_0(sK4))) ) | (~spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(subsumption_resolution,[],[f306,f300])).
% 0.66/0.75  fof(f300,plain,(
% 0.66/0.75    sP1(sK4,k2_tarski(sK6,sK6),sK5) | (~spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(resolution,[],[f289,f246])).
% 0.66/0.75  fof(f246,plain,(
% 0.66/0.75    r2_hidden(sK5,k2_orders_2(sK4,k2_tarski(sK6,sK6))) | (~spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(backward_demodulation,[],[f112,f138])).
% 0.66/0.75  fof(f112,plain,(
% 0.66/0.75    r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) | ~spl11_2),
% 0.66/0.75    inference(avatar_component_clause,[],[f111])).
% 0.66/0.75  fof(f289,plain,(
% 0.66/0.75    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK4,k2_tarski(sK6,sK6))) | sP1(sK4,k2_tarski(sK6,sK6),X1)) ) | ~spl11_5),
% 0.66/0.75    inference(subsumption_resolution,[],[f287,f275])).
% 0.66/0.75  fof(f287,plain,(
% 0.66/0.75    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK4,k2_tarski(sK6,sK6))) | sP1(sK4,k2_tarski(sK6,sK6),X1) | ~sP2(X1,k2_tarski(sK6,sK6),sK4)) ) | ~spl11_5),
% 0.66/0.75    inference(superposition,[],[f81,f270])).
% 0.66/0.75  fof(f81,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f47])).
% 0.66/0.75  fof(f306,plain,(
% 0.66/0.75    ( ! [X1] : (r2_orders_2(sK4,sK5,X1) | ~r2_hidden(X1,k2_tarski(sK6,sK6)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~sP1(sK4,k2_tarski(sK6,sK6),sK5)) ) | (~spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(superposition,[],[f85,f303])).
% 0.66/0.75  fof(f303,plain,(
% 0.66/0.75    sK5 = sK9(sK4,k2_tarski(sK6,sK6),sK5) | (~spl11_2 | ~spl11_5)),
% 0.66/0.75    inference(resolution,[],[f300,f84])).
% 0.66/0.75  fof(f84,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | sK9(X0,X1,X2) = X2) )),
% 0.66/0.75    inference(cnf_transformation,[],[f52])).
% 0.66/0.75  fof(f85,plain,(
% 0.66/0.75    ( ! [X6,X2,X0,X1] : (r2_orders_2(X0,sK9(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP1(X0,X1,X2)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f52])).
% 0.66/0.75  fof(f194,plain,(
% 0.66/0.75    ~spl11_3),
% 0.66/0.75    inference(avatar_contradiction_clause,[],[f193])).
% 0.66/0.75  fof(f193,plain,(
% 0.66/0.75    $false | ~spl11_3),
% 0.66/0.75    inference(subsumption_resolution,[],[f192,f129])).
% 0.66/0.75  fof(f129,plain,(
% 0.66/0.75    v1_xboole_0(u1_struct_0(sK4)) | ~spl11_3),
% 0.66/0.75    inference(avatar_component_clause,[],[f127])).
% 0.66/0.75  fof(f127,plain,(
% 0.66/0.75    spl11_3 <=> v1_xboole_0(u1_struct_0(sK4))),
% 0.66/0.75    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.66/0.75  fof(f192,plain,(
% 0.66/0.75    ~v1_xboole_0(u1_struct_0(sK4))),
% 0.66/0.75    inference(resolution,[],[f178,f147])).
% 0.66/0.75  fof(f147,plain,(
% 0.66/0.75    ( ! [X4,X5,X3] : (~sP0(X4,X5,X3) | ~v1_xboole_0(u1_struct_0(X3))) )),
% 0.66/0.75    inference(duplicate_literal_removal,[],[f146])).
% 0.66/0.75  fof(f146,plain,(
% 0.66/0.75    ( ! [X4,X5,X3] : (~v1_xboole_0(u1_struct_0(X3)) | ~sP0(X4,X5,X3) | ~sP0(X4,X5,X3)) )),
% 0.66/0.75    inference(resolution,[],[f121,f76])).
% 0.66/0.75  fof(f76,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (r2_hidden(X0,sK7(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f44])).
% 0.66/0.75  fof(f44,plain,(
% 0.66/0.75    ! [X0,X1,X2] : ((r2_hidden(X0,sK7(X0,X1,X2)) & r2_hidden(X1,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK7(X0,X1,X2),X2)) | ~sP0(X0,X1,X2))),
% 0.66/0.75    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).
% 0.66/0.75  fof(f43,plain,(
% 0.66/0.75    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) => (r2_hidden(X0,sK7(X0,X1,X2)) & r2_hidden(X1,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK7(X0,X1,X2),X2)))),
% 0.66/0.75    introduced(choice_axiom,[])).
% 0.66/0.75  fof(f42,plain,(
% 0.66/0.75    ! [X0,X1,X2] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) | ~sP0(X0,X1,X2))),
% 0.66/0.75    inference(rectify,[],[f41])).
% 0.66/0.75  fof(f41,plain,(
% 0.66/0.75    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | ~sP0(X2,X1,X0))),
% 0.66/0.75    inference(nnf_transformation,[],[f28])).
% 0.66/0.75  fof(f28,plain,(
% 0.66/0.75    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | ~sP0(X2,X1,X0))),
% 0.66/0.75    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.66/0.75  fof(f121,plain,(
% 0.66/0.75    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,sK7(X0,X1,X2)) | ~v1_xboole_0(u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 0.66/0.75    inference(resolution,[],[f74,f98])).
% 0.66/0.75  fof(f98,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f27])).
% 0.66/0.75  fof(f27,plain,(
% 0.66/0.75    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.66/0.75    inference(ennf_transformation,[],[f3])).
% 0.66/0.75  fof(f3,axiom,(
% 0.66/0.75    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.66/0.75  fof(f74,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f44])).
% 0.66/0.75  fof(f178,plain,(
% 0.66/0.75    sP0(sK5,sK5,sK4)),
% 0.66/0.75    inference(subsumption_resolution,[],[f177,f60])).
% 0.66/0.75  fof(f177,plain,(
% 0.66/0.75    sP0(sK5,sK5,sK4) | ~v3_orders_2(sK4)),
% 0.66/0.75    inference(subsumption_resolution,[],[f176,f63])).
% 0.66/0.75  fof(f176,plain,(
% 0.66/0.75    sP0(sK5,sK5,sK4) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4)),
% 0.66/0.75    inference(subsumption_resolution,[],[f175,f64])).
% 0.66/0.75  fof(f175,plain,(
% 0.66/0.75    sP0(sK5,sK5,sK4) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4)),
% 0.66/0.75    inference(duplicate_literal_removal,[],[f172])).
% 0.66/0.75  fof(f172,plain,(
% 0.66/0.75    sP0(sK5,sK5,sK4) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4)),
% 0.66/0.75    inference(resolution,[],[f78,f154])).
% 0.66/0.75  fof(f154,plain,(
% 0.66/0.75    r1_orders_2(sK4,sK5,sK5)),
% 0.66/0.75    inference(subsumption_resolution,[],[f153,f59])).
% 0.66/0.75  fof(f153,plain,(
% 0.66/0.75    r1_orders_2(sK4,sK5,sK5) | v2_struct_0(sK4)),
% 0.66/0.75    inference(subsumption_resolution,[],[f152,f60])).
% 0.66/0.75  fof(f152,plain,(
% 0.66/0.75    r1_orders_2(sK4,sK5,sK5) | ~v3_orders_2(sK4) | v2_struct_0(sK4)),
% 0.66/0.75    inference(subsumption_resolution,[],[f149,f63])).
% 0.66/0.75  fof(f149,plain,(
% 0.66/0.75    r1_orders_2(sK4,sK5,sK5) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)),
% 0.66/0.75    inference(resolution,[],[f70,f64])).
% 0.66/0.75  fof(f70,plain,(
% 0.66/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f18])).
% 0.66/0.75  fof(f18,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.66/0.75    inference(flattening,[],[f17])).
% 0.66/0.75  fof(f17,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.66/0.75    inference(ennf_transformation,[],[f7])).
% 0.66/0.75  fof(f7,axiom,(
% 0.66/0.75    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).
% 0.66/0.75  fof(f78,plain,(
% 0.66/0.75    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | sP0(X2,X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f45])).
% 0.66/0.75  fof(f45,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : (! [X2] : (((sP0(X2,X1,X0) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.66/0.75    inference(rectify,[],[f29])).
% 0.66/0.75  fof(f29,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : (! [X2] : (((sP0(X2,X1,X0) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.66/0.75    inference(definition_folding,[],[f22,f28])).
% 0.66/0.75  fof(f22,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.66/0.75    inference(flattening,[],[f21])).
% 0.66/0.75  fof(f21,plain,(
% 0.66/0.75    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.66/0.75    inference(ennf_transformation,[],[f12])).
% 0.66/0.75  fof(f12,plain,(
% 0.66/0.75    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 0.66/0.75    inference(rectify,[],[f9])).
% 0.66/0.75  fof(f9,axiom,(
% 0.66/0.75    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).
% 0.66/0.75  fof(f139,plain,(
% 0.66/0.75    spl11_3 | spl11_5),
% 0.66/0.75    inference(avatar_split_clause,[],[f123,f136,f127])).
% 0.66/0.75  fof(f123,plain,(
% 0.66/0.75    k6_domain_1(u1_struct_0(sK4),sK6) = k2_tarski(sK6,sK6) | v1_xboole_0(u1_struct_0(sK4))),
% 0.66/0.75    inference(resolution,[],[f99,f65])).
% 0.66/0.75  fof(f99,plain,(
% 0.66/0.75    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.66/0.75    inference(definition_unfolding,[],[f80,f68])).
% 0.66/0.75  fof(f68,plain,(
% 0.66/0.75    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f2])).
% 0.66/0.75  fof(f2,axiom,(
% 0.66/0.75    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.66/0.75  fof(f80,plain,(
% 0.66/0.75    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.66/0.75    inference(cnf_transformation,[],[f24])).
% 0.66/0.75  fof(f24,plain,(
% 0.66/0.75    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.66/0.75    inference(flattening,[],[f23])).
% 0.66/0.75  fof(f23,plain,(
% 0.66/0.75    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.66/0.75    inference(ennf_transformation,[],[f6])).
% 0.66/0.75  fof(f6,axiom,(
% 0.66/0.75    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.66/0.75    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.66/0.75  fof(f115,plain,(
% 0.66/0.75    spl11_1 | spl11_2),
% 0.66/0.75    inference(avatar_split_clause,[],[f66,f111,f107])).
% 0.66/0.75  fof(f66,plain,(
% 0.66/0.75    r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) | r2_orders_2(sK4,sK5,sK6)),
% 0.66/0.75    inference(cnf_transformation,[],[f40])).
% 0.66/0.75  fof(f114,plain,(
% 0.66/0.75    ~spl11_1 | ~spl11_2),
% 0.66/0.75    inference(avatar_split_clause,[],[f67,f111,f107])).
% 0.66/0.75  fof(f67,plain,(
% 0.66/0.75    ~r2_hidden(sK5,k2_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK6))) | ~r2_orders_2(sK4,sK5,sK6)),
% 0.66/0.75    inference(cnf_transformation,[],[f40])).
% 0.66/0.75  % SZS output end Proof for theBenchmark
% 0.66/0.75  % (8875)------------------------------
% 0.66/0.75  % (8875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.66/0.75  % (8875)Termination reason: Refutation
% 0.66/0.75  
% 0.66/0.75  % (8875)Memory used [KB]: 11129
% 0.66/0.75  % (8875)Time elapsed: 0.144 s
% 0.66/0.75  % (8875)------------------------------
% 0.66/0.75  % (8875)------------------------------
% 0.66/0.75  % (8683)Success in time 0.383 s
%------------------------------------------------------------------------------
