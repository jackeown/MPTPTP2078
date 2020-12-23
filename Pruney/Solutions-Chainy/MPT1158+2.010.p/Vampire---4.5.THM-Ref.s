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
% DateTime   : Thu Dec  3 13:10:04 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  173 (1232 expanded)
%              Number of leaves         :   24 ( 396 expanded)
%              Depth                    :   26
%              Number of atoms          :  833 (10763 expanded)
%              Number of equality atoms :  105 ( 280 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f456,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f97,f119,f191,f202,f210,f434,f455])).

fof(f455,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f454])).

fof(f454,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f453,f53])).

fof(f53,plain,(
    m1_subset_1(sK4,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f453,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f452,f436])).

fof(f436,plain,
    ( ~ sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f435,f337])).

fof(f337,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),X4) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f333,f258])).

fof(f258,plain,
    ( ! [X2] : sP1(X2,k2_tarski(sK5,sK5),sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f257,f54])).

fof(f54,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f257,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f256,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f256,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f255,f49])).

fof(f49,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f255,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f254,f50])).

fof(f50,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f254,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f253,f51])).

fof(f51,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f253,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f248,f52])).

fof(f52,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f248,plain,
    ( ! [X2] :
        ( sP1(X2,k2_tarski(sK5,sK5),sK3)
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3)
        | ~ m1_subset_1(sK5,u1_struct_0(sK3)) )
    | ~ spl9_5 ),
    inference(superposition,[],[f134,f118])).

fof(f118,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl9_5
  <=> k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,k6_domain_1(u1_struct_0(X1),X2),X1)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f133])).

fof(f133,plain,(
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
    inference(resolution,[],[f71,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
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
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP1(X0,X2,X1)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f22,f25,f24])).

fof(f24,plain,(
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

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

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
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f333,plain,
    ( ! [X4] :
        ( r2_hidden(X4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),X4)
        | ~ sP1(X4,k2_tarski(sK5,sK5),sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f64,f245])).

fof(f245,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f170,f118])).

fof(f170,plain,(
    k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f169,f48])).

fof(f169,plain,
    ( v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f168,f49])).

fof(f168,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f167,f50])).

fof(f167,plain,
    ( ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f166,f51])).

fof(f166,plain,
    ( ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(subsumption_resolution,[],[f158,f52])).

fof(f158,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) ),
    inference(resolution,[],[f142,f54])).

fof(f142,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = a_2_1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(duplicate_literal_removal,[],[f141])).

fof(f141,plain,(
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
    inference(resolution,[],[f59,f61])).

fof(f59,plain,(
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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f435,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | spl9_2
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f95,f118])).

fof(f95,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl9_2
  <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f452,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f450,f90])).

fof(f90,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl9_1
  <=> r2_orders_2(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f450,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_2
    | ~ spl9_5 ),
    inference(superposition,[],[f82,f448])).

fof(f448,plain,
    ( sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f447,f53])).

fof(f447,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f446])).

fof(f446,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f436,f126])).

fof(f126,plain,(
    ! [X6,X4,X7,X5] :
      ( sP0(X4,k2_tarski(X5,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | sK6(X4,k2_tarski(X5,X6),X7) = X5
      | sK6(X4,k2_tarski(X5,X6),X7) = X6 ) ),
    inference(resolution,[],[f83,f122])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f72,f87])).

fof(f87,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( sP2(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP2(X1,X0,X2) )
      & ( sP2(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP2(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f27])).

fof(f27,plain,(
    ! [X1,X0,X2] :
      ( sP2(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

% (6820)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% (6828)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

fof(f72,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP2(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).

fof(f45,plain,(
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

fof(f44,plain,(
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
    inference(rectify,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | sP0(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f40,f39])).

fof(f39,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X3,X4)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
        & r2_hidden(sK6(X0,X1,X3),X1)
        & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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

fof(f38,plain,(
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
    inference(rectify,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f82,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
      | sP0(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f434,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f433])).

fof(f433,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f432,f54])).

fof(f432,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f426,f91])).

fof(f91,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f426,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f416,f101])).

fof(f101,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f86,f87])).

fof(f86,plain,(
    ! [X4,X2,X0] :
      ( ~ sP2(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f73])).

fof(f73,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f416,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | r2_orders_2(sK3,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f413,f383])).

fof(f383,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f338,f246])).

fof(f246,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f94,f118])).

fof(f94,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f338,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | sP0(sK3,k2_tarski(sK5,sK5),X5) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f334,f258])).

fof(f334,plain,
    ( ! [X5] :
        ( ~ r2_hidden(X5,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | sP0(sK3,k2_tarski(sK5,sK5),X5)
        | ~ sP1(X5,k2_tarski(sK5,sK5),sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f63,f245])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f413,plain,
    ( ! [X1] :
        ( r2_orders_2(sK3,sK4,X1)
        | ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),sK4) )
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(superposition,[],[f67,f390])).

fof(f390,plain,
    ( sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f383,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK7(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f67,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X0,sK7(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f210,plain,
    ( ~ spl9_3
    | spl9_7 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl9_3
    | spl9_7 ),
    inference(subsumption_resolution,[],[f208,f52])).

fof(f208,plain,
    ( ~ l1_orders_2(sK3)
    | ~ spl9_3
    | spl9_7 ),
    inference(subsumption_resolution,[],[f207,f53])).

fof(f207,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ spl9_3
    | spl9_7 ),
    inference(subsumption_resolution,[],[f206,f109])).

fof(f109,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f107])).

fof(f107,plain,
    ( spl9_3
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f206,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl9_7 ),
    inference(subsumption_resolution,[],[f205,f48])).

fof(f205,plain,
    ( v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl9_7 ),
    inference(subsumption_resolution,[],[f204,f49])).

fof(f204,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | spl9_7 ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ v1_xboole_0(u1_struct_0(sK3))
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_7 ),
    inference(resolution,[],[f190,f135])).

fof(f135,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,k6_domain_1(u1_struct_0(X0),X1),X3)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f128,f83])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0))
      | ~ l1_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(resolution,[],[f61,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f190,plain,
    ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4)
    | spl9_7 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl9_7
  <=> sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).

fof(f202,plain,(
    spl9_6 ),
    inference(avatar_contradiction_clause,[],[f201])).

fof(f201,plain,
    ( $false
    | spl9_6 ),
    inference(subsumption_resolution,[],[f200,f53])).

fof(f200,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_6 ),
    inference(subsumption_resolution,[],[f199,f48])).

fof(f199,plain,
    ( v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_6 ),
    inference(subsumption_resolution,[],[f198,f49])).

fof(f198,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_6 ),
    inference(subsumption_resolution,[],[f197,f50])).

fof(f197,plain,
    ( ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_6 ),
    inference(subsumption_resolution,[],[f196,f51])).

fof(f196,plain,
    ( ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_6 ),
    inference(subsumption_resolution,[],[f195,f52])).

fof(f195,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_6 ),
    inference(resolution,[],[f186,f134])).

fof(f186,plain,
    ( ~ sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
    | spl9_6 ),
    inference(avatar_component_clause,[],[f184])).

fof(f184,plain,
    ( spl9_6
  <=> sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).

fof(f191,plain,
    ( ~ spl9_6
    | ~ spl9_7 ),
    inference(avatar_split_clause,[],[f182,f188,f184])).

fof(f182,plain,
    ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4)
    | ~ sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3) ),
    inference(subsumption_resolution,[],[f181,f48])).

fof(f181,plain,
    ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4)
    | ~ sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f180,f49])).

fof(f180,plain,
    ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4)
    | ~ sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f179,f50])).

fof(f179,plain,
    ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4)
    | ~ sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f178,f51])).

fof(f178,plain,
    ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4)
    | ~ sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f177,f52])).

fof(f177,plain,
    ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4)
    | ~ sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(subsumption_resolution,[],[f175,f53])).

fof(f175,plain,
    ( ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4)
    | ~ sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3) ),
    inference(resolution,[],[f171,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

fof(f171,plain,(
    ! [X0] :
      ( r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)))
      | ~ sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0)
      | ~ sP1(X0,k6_domain_1(u1_struct_0(sK3),sK4),sK3) ) ),
    inference(superposition,[],[f64,f165])).

fof(f165,plain,(
    k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f164,f48])).

fof(f164,plain,
    ( v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f163,f49])).

fof(f163,plain,
    ( ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f162,f50])).

fof(f162,plain,
    ( ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f161,f51])).

fof(f161,plain,
    ( ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(subsumption_resolution,[],[f157,f52])).

fof(f157,plain,
    ( ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) ),
    inference(resolution,[],[f142,f53])).

fof(f119,plain,
    ( spl9_3
    | spl9_5 ),
    inference(avatar_split_clause,[],[f104,f116,f107])).

fof(f104,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f81,f54])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f62,f57])).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f97,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f55,f93,f89])).

fof(f55,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f56,f93,f89])).

fof(f56,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:56:50 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (6829)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.52  % (6837)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.52  % (6821)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.52  % (6816)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (6821)Refutation not found, incomplete strategy% (6821)------------------------------
% 0.22/0.52  % (6821)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6825)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (6837)Refutation not found, incomplete strategy% (6837)------------------------------
% 0.22/0.52  % (6837)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (6837)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6837)Memory used [KB]: 6268
% 0.22/0.52  % (6837)Time elapsed: 0.099 s
% 0.22/0.52  % (6837)------------------------------
% 0.22/0.52  % (6837)------------------------------
% 0.22/0.52  % (6813)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (6821)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (6821)Memory used [KB]: 10746
% 0.22/0.52  % (6821)Time elapsed: 0.109 s
% 0.22/0.52  % (6821)------------------------------
% 0.22/0.52  % (6821)------------------------------
% 0.22/0.53  % (6834)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.53  % (6829)Refutation not found, incomplete strategy% (6829)------------------------------
% 0.22/0.53  % (6829)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (6829)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (6829)Memory used [KB]: 1791
% 0.22/0.53  % (6829)Time elapsed: 0.109 s
% 0.22/0.53  % (6829)------------------------------
% 0.22/0.53  % (6829)------------------------------
% 0.22/0.53  % (6811)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  % (6812)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (6826)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (6814)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (6839)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (6833)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (6815)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.54  % (6824)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.54  % (6818)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.54  % (6817)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (6835)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (6815)Refutation not found, incomplete strategy% (6815)------------------------------
% 0.22/0.54  % (6815)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (6815)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (6815)Memory used [KB]: 1918
% 0.22/0.54  % (6815)Time elapsed: 0.129 s
% 0.22/0.54  % (6815)------------------------------
% 0.22/0.54  % (6815)------------------------------
% 0.22/0.54  % (6838)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (6835)Refutation not found, incomplete strategy% (6835)------------------------------
% 0.22/0.55  % (6835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6835)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6835)Memory used [KB]: 10746
% 0.22/0.55  % (6835)Time elapsed: 0.129 s
% 0.22/0.55  % (6835)------------------------------
% 0.22/0.55  % (6835)------------------------------
% 0.22/0.55  % (6831)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (6838)Refutation not found, incomplete strategy% (6838)------------------------------
% 0.22/0.55  % (6838)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6838)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6838)Memory used [KB]: 6268
% 0.22/0.55  % (6838)Time elapsed: 0.131 s
% 0.22/0.55  % (6838)------------------------------
% 0.22/0.55  % (6838)------------------------------
% 0.22/0.55  % (6827)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (6840)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.55  % (6840)Refutation not found, incomplete strategy% (6840)------------------------------
% 0.22/0.55  % (6840)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6840)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (6840)Memory used [KB]: 1663
% 0.22/0.55  % (6840)Time elapsed: 0.002 s
% 0.22/0.55  % (6840)------------------------------
% 0.22/0.55  % (6840)------------------------------
% 0.22/0.55  % (6830)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (6827)Refutation not found, incomplete strategy% (6827)------------------------------
% 0.22/0.55  % (6827)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (6832)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (6823)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (6839)Refutation not found, incomplete strategy% (6839)------------------------------
% 0.22/0.55  % (6839)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6822)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.56  % (6819)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.56  % (6823)Refutation not found, incomplete strategy% (6823)------------------------------
% 0.22/0.56  % (6823)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (6839)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6839)Memory used [KB]: 10746
% 0.22/0.56  % (6839)Time elapsed: 0.141 s
% 0.22/0.56  % (6839)------------------------------
% 0.22/0.56  % (6839)------------------------------
% 0.22/0.56  % (6827)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6827)Memory used [KB]: 10618
% 0.22/0.56  % (6827)Time elapsed: 0.141 s
% 0.22/0.56  % (6827)------------------------------
% 0.22/0.56  % (6827)------------------------------
% 0.22/0.56  % (6823)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (6823)Memory used [KB]: 10746
% 0.22/0.56  % (6823)Time elapsed: 0.142 s
% 0.22/0.56  % (6823)------------------------------
% 0.22/0.56  % (6823)------------------------------
% 0.22/0.57  % (6817)Refutation found. Thanks to Tanya!
% 0.22/0.57  % SZS status Theorem for theBenchmark
% 0.22/0.57  % SZS output start Proof for theBenchmark
% 0.22/0.57  fof(f456,plain,(
% 0.22/0.57    $false),
% 0.22/0.57    inference(avatar_sat_refutation,[],[f96,f97,f119,f191,f202,f210,f434,f455])).
% 0.22/0.57  fof(f455,plain,(
% 0.22/0.57    ~spl9_1 | spl9_2 | ~spl9_5),
% 0.22/0.57    inference(avatar_contradiction_clause,[],[f454])).
% 0.22/0.57  fof(f454,plain,(
% 0.22/0.57    $false | (~spl9_1 | spl9_2 | ~spl9_5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f453,f53])).
% 0.22/0.57  fof(f53,plain,(
% 0.22/0.57    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f34,plain,(
% 0.22/0.57    (((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.22/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 0.22/0.57  fof(f31,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f32,plain,(
% 0.22/0.57    ? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f33,plain,(
% 0.22/0.57    ? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) => ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.22/0.57    introduced(choice_axiom,[])).
% 0.22/0.57  fof(f30,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f29])).
% 0.22/0.57  fof(f29,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(nnf_transformation,[],[f12])).
% 0.22/0.57  fof(f12,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f11])).
% 0.22/0.57  fof(f11,plain,(
% 0.22/0.57    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f10])).
% 0.22/0.57  fof(f10,negated_conjecture,(
% 0.22/0.57    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.57    inference(negated_conjecture,[],[f9])).
% 0.22/0.57  fof(f9,conjecture,(
% 0.22/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_orders_2)).
% 0.22/0.57  fof(f453,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_2 | ~spl9_5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f452,f436])).
% 0.22/0.57  fof(f436,plain,(
% 0.22/0.57    ~sP0(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 0.22/0.57    inference(resolution,[],[f435,f337])).
% 0.22/0.57  fof(f337,plain,(
% 0.22/0.57    ( ! [X4] : (r2_hidden(X4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | ~sP0(sK3,k2_tarski(sK5,sK5),X4)) ) | ~spl9_5),
% 0.22/0.57    inference(subsumption_resolution,[],[f333,f258])).
% 0.22/0.57  fof(f258,plain,(
% 0.22/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 0.22/0.57    inference(subsumption_resolution,[],[f257,f54])).
% 0.22/0.57  fof(f54,plain,(
% 0.22/0.57    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f257,plain,(
% 0.22/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 0.22/0.57    inference(subsumption_resolution,[],[f256,f48])).
% 0.22/0.57  fof(f48,plain,(
% 0.22/0.57    ~v2_struct_0(sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f256,plain,(
% 0.22/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 0.22/0.57    inference(subsumption_resolution,[],[f255,f49])).
% 0.22/0.57  fof(f49,plain,(
% 0.22/0.57    v3_orders_2(sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f255,plain,(
% 0.22/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 0.22/0.57    inference(subsumption_resolution,[],[f254,f50])).
% 0.22/0.57  fof(f50,plain,(
% 0.22/0.57    v4_orders_2(sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f254,plain,(
% 0.22/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 0.22/0.57    inference(subsumption_resolution,[],[f253,f51])).
% 0.22/0.57  fof(f51,plain,(
% 0.22/0.57    v5_orders_2(sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f253,plain,(
% 0.22/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 0.22/0.57    inference(subsumption_resolution,[],[f248,f52])).
% 0.22/0.57  fof(f52,plain,(
% 0.22/0.57    l1_orders_2(sK3)),
% 0.22/0.57    inference(cnf_transformation,[],[f34])).
% 0.22/0.57  fof(f248,plain,(
% 0.22/0.57    ( ! [X2] : (sP1(X2,k2_tarski(sK5,sK5),sK3) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK5,u1_struct_0(sK3))) ) | ~spl9_5),
% 0.22/0.57    inference(superposition,[],[f134,f118])).
% 0.22/0.57  fof(f118,plain,(
% 0.22/0.57    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | ~spl9_5),
% 0.22/0.57    inference(avatar_component_clause,[],[f116])).
% 0.22/0.57  fof(f116,plain,(
% 0.22/0.57    spl9_5 <=> k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.57  fof(f134,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (sP1(X0,k6_domain_1(u1_struct_0(X1),X2),X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1))) )),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f133])).
% 0.22/0.57  fof(f133,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (sP1(X0,k6_domain_1(u1_struct_0(X1),X2),X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.57    inference(resolution,[],[f71,f61])).
% 0.22/0.57  fof(f61,plain,(
% 0.22/0.57    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f18])).
% 0.22/0.57  fof(f18,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f17])).
% 0.22/0.57  fof(f17,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f7])).
% 0.22/0.57  fof(f7,axiom,(
% 0.22/0.57    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 0.22/0.57  fof(f71,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP1(X0,X2,X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f26])).
% 0.22/0.57  fof(f26,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.57    inference(definition_folding,[],[f22,f25,f24])).
% 0.22/0.57  fof(f24,plain,(
% 0.22/0.57    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.57  fof(f25,plain,(
% 0.22/0.57    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.57  fof(f22,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.57    inference(flattening,[],[f21])).
% 0.22/0.57  fof(f21,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.22/0.57    inference(ennf_transformation,[],[f5])).
% 0.22/0.57  fof(f5,axiom,(
% 0.22/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.22/0.57  fof(f333,plain,(
% 0.22/0.57    ( ! [X4] : (r2_hidden(X4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | ~sP0(sK3,k2_tarski(sK5,sK5),X4) | ~sP1(X4,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 0.22/0.57    inference(superposition,[],[f64,f245])).
% 0.22/0.57  fof(f245,plain,(
% 0.22/0.57    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~spl9_5),
% 0.22/0.57    inference(backward_demodulation,[],[f170,f118])).
% 0.22/0.57  fof(f170,plain,(
% 0.22/0.57    k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 0.22/0.57    inference(subsumption_resolution,[],[f169,f48])).
% 0.22/0.57  fof(f169,plain,(
% 0.22/0.57    v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 0.22/0.57    inference(subsumption_resolution,[],[f168,f49])).
% 0.22/0.57  fof(f168,plain,(
% 0.22/0.57    ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 0.22/0.57    inference(subsumption_resolution,[],[f167,f50])).
% 0.22/0.57  fof(f167,plain,(
% 0.22/0.57    ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 0.22/0.57    inference(subsumption_resolution,[],[f166,f51])).
% 0.22/0.57  fof(f166,plain,(
% 0.22/0.57    ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 0.22/0.57    inference(subsumption_resolution,[],[f158,f52])).
% 0.22/0.57  fof(f158,plain,(
% 0.22/0.57    ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))),
% 0.22/0.57    inference(resolution,[],[f142,f54])).
% 0.22/0.57  fof(f142,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = a_2_1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) )),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f141])).
% 0.22/0.57  fof(f141,plain,(
% 0.22/0.57    ( ! [X0,X1] : (k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) = a_2_1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(resolution,[],[f59,f61])).
% 0.22/0.57  fof(f59,plain,(
% 0.22/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f16])).
% 0.22/0.57  fof(f16,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.57    inference(flattening,[],[f15])).
% 0.22/0.57  fof(f15,plain,(
% 0.22/0.57    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.57    inference(ennf_transformation,[],[f4])).
% 0.22/0.57  fof(f4,axiom,(
% 0.22/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.22/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_orders_2)).
% 0.22/0.57  fof(f64,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.22/0.57    inference(cnf_transformation,[],[f36])).
% 0.22/0.57  fof(f36,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.22/0.57    inference(rectify,[],[f35])).
% 0.22/0.57  fof(f35,plain,(
% 0.22/0.57    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.22/0.57    inference(nnf_transformation,[],[f25])).
% 0.22/0.57  fof(f435,plain,(
% 0.22/0.57    ~r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (spl9_2 | ~spl9_5)),
% 0.22/0.57    inference(forward_demodulation,[],[f95,f118])).
% 0.22/0.57  fof(f95,plain,(
% 0.22/0.57    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | spl9_2),
% 0.22/0.57    inference(avatar_component_clause,[],[f93])).
% 0.22/0.57  fof(f93,plain,(
% 0.22/0.57    spl9_2 <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.57  fof(f452,plain,(
% 0.22/0.57    sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_2 | ~spl9_5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f450,f90])).
% 0.22/0.57  fof(f90,plain,(
% 0.22/0.57    r2_orders_2(sK3,sK4,sK5) | ~spl9_1),
% 0.22/0.57    inference(avatar_component_clause,[],[f89])).
% 0.22/0.57  fof(f89,plain,(
% 0.22/0.57    spl9_1 <=> r2_orders_2(sK3,sK4,sK5)),
% 0.22/0.57    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.57  fof(f450,plain,(
% 0.22/0.57    ~r2_orders_2(sK3,sK4,sK5) | sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (spl9_2 | ~spl9_5)),
% 0.22/0.57    inference(superposition,[],[f82,f448])).
% 0.22/0.57  fof(f448,plain,(
% 0.22/0.57    sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 0.22/0.57    inference(subsumption_resolution,[],[f447,f53])).
% 0.22/0.57  fof(f447,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 0.22/0.57    inference(duplicate_literal_removal,[],[f446])).
% 0.22/0.57  fof(f446,plain,(
% 0.22/0.57    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 0.22/0.57    inference(resolution,[],[f436,f126])).
% 0.22/0.57  fof(f126,plain,(
% 0.22/0.57    ( ! [X6,X4,X7,X5] : (sP0(X4,k2_tarski(X5,X6),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | sK6(X4,k2_tarski(X5,X6),X7) = X5 | sK6(X4,k2_tarski(X5,X6),X7) = X6) )),
% 0.22/0.57    inference(resolution,[],[f83,f122])).
% 0.22/0.57  fof(f122,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.22/0.57    inference(resolution,[],[f72,f87])).
% 0.22/0.57  fof(f87,plain,(
% 0.22/0.57    ( ! [X0,X1] : (sP2(X1,X0,k2_tarski(X0,X1))) )),
% 0.22/0.57    inference(equality_resolution,[],[f78])).
% 0.22/0.57  fof(f78,plain,(
% 0.22/0.57    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.57    inference(cnf_transformation,[],[f47])).
% 0.22/0.57  fof(f47,plain,(
% 0.22/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.22/0.57    inference(nnf_transformation,[],[f28])).
% 0.22/0.57  fof(f28,plain,(
% 0.22/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 0.22/0.57    inference(definition_folding,[],[f1,f27])).
% 0.22/0.57  fof(f27,plain,(
% 0.22/0.57    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.58  % (6820)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.58  % (6828)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.58  fof(f1,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.58  fof(f72,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.22/0.58    inference(cnf_transformation,[],[f46])).
% 0.22/0.58  fof(f46,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).
% 0.22/0.58  fof(f45,plain,(
% 0.22/0.58    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f44,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.58    inference(rectify,[],[f43])).
% 0.22/0.58  fof(f43,plain,(
% 0.22/0.58    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.22/0.58    inference(flattening,[],[f42])).
% 0.22/0.58  fof(f42,plain,(
% 0.22/0.58    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.22/0.58    inference(nnf_transformation,[],[f27])).
% 0.22/0.58  fof(f83,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.58    inference(equality_resolution,[],[f69])).
% 0.22/0.58  fof(f69,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | r2_hidden(sK6(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f41])).
% 0.22/0.58  fof(f41,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.22/0.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f40,f39])).
% 0.22/0.58  fof(f39,plain,(
% 0.22/0.58    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f40,plain,(
% 0.22/0.58    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.58    introduced(choice_axiom,[])).
% 0.22/0.58  fof(f38,plain,(
% 0.22/0.58    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.22/0.58    inference(rectify,[],[f37])).
% 0.22/0.58  fof(f37,plain,(
% 0.22/0.58    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.22/0.58    inference(nnf_transformation,[],[f24])).
% 0.22/0.58  fof(f82,plain,(
% 0.22/0.58    ( ! [X0,X3,X1] : (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.58    inference(equality_resolution,[],[f70])).
% 0.22/0.58  fof(f70,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | ~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.58    inference(cnf_transformation,[],[f41])).
% 0.22/0.58  fof(f434,plain,(
% 0.22/0.58    spl9_1 | ~spl9_2 | ~spl9_5),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f433])).
% 0.22/0.58  fof(f433,plain,(
% 0.22/0.58    $false | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f432,f54])).
% 0.22/0.58  fof(f432,plain,(
% 0.22/0.58    ~m1_subset_1(sK5,u1_struct_0(sK3)) | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f426,f91])).
% 0.22/0.58  fof(f91,plain,(
% 0.22/0.58    ~r2_orders_2(sK3,sK4,sK5) | spl9_1),
% 0.22/0.58    inference(avatar_component_clause,[],[f89])).
% 0.22/0.58  fof(f426,plain,(
% 0.22/0.58    r2_orders_2(sK3,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl9_2 | ~spl9_5)),
% 0.22/0.58    inference(resolution,[],[f416,f101])).
% 0.22/0.58  fof(f101,plain,(
% 0.22/0.58    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.22/0.58    inference(resolution,[],[f86,f87])).
% 0.22/0.58  fof(f86,plain,(
% 0.22/0.58    ( ! [X4,X2,X0] : (~sP2(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.22/0.58    inference(equality_resolution,[],[f73])).
% 0.22/0.58  fof(f73,plain,(
% 0.22/0.58    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP2(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f46])).
% 0.22/0.58  fof(f416,plain,(
% 0.22/0.58    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK5,sK5)) | r2_orders_2(sK3,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | (~spl9_2 | ~spl9_5)),
% 0.22/0.58    inference(subsumption_resolution,[],[f413,f383])).
% 0.22/0.58  fof(f383,plain,(
% 0.22/0.58    sP0(sK3,k2_tarski(sK5,sK5),sK4) | (~spl9_2 | ~spl9_5)),
% 0.22/0.58    inference(resolution,[],[f338,f246])).
% 0.22/0.58  fof(f246,plain,(
% 0.22/0.58    r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (~spl9_2 | ~spl9_5)),
% 0.22/0.58    inference(backward_demodulation,[],[f94,f118])).
% 0.22/0.58  fof(f94,plain,(
% 0.22/0.58    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~spl9_2),
% 0.22/0.58    inference(avatar_component_clause,[],[f93])).
% 0.22/0.58  fof(f338,plain,(
% 0.22/0.58    ( ! [X5] : (~r2_hidden(X5,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | sP0(sK3,k2_tarski(sK5,sK5),X5)) ) | ~spl9_5),
% 0.22/0.58    inference(subsumption_resolution,[],[f334,f258])).
% 0.22/0.58  fof(f334,plain,(
% 0.22/0.58    ( ! [X5] : (~r2_hidden(X5,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | sP0(sK3,k2_tarski(sK5,sK5),X5) | ~sP1(X5,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 0.22/0.58    inference(superposition,[],[f63,f245])).
% 0.22/0.58  fof(f63,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f36])).
% 0.22/0.58  fof(f413,plain,(
% 0.22/0.58    ( ! [X1] : (r2_orders_2(sK3,sK4,X1) | ~r2_hidden(X1,k2_tarski(sK5,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~sP0(sK3,k2_tarski(sK5,sK5),sK4)) ) | (~spl9_2 | ~spl9_5)),
% 0.22/0.58    inference(superposition,[],[f67,f390])).
% 0.22/0.58  fof(f390,plain,(
% 0.22/0.58    sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4) | (~spl9_2 | ~spl9_5)),
% 0.22/0.58    inference(resolution,[],[f383,f66])).
% 0.22/0.58  fof(f66,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK7(X0,X1,X2) = X2) )),
% 0.22/0.58    inference(cnf_transformation,[],[f41])).
% 0.22/0.58  fof(f67,plain,(
% 0.22/0.58    ( ! [X6,X2,X0,X1] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f41])).
% 0.22/0.58  fof(f210,plain,(
% 0.22/0.58    ~spl9_3 | spl9_7),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f209])).
% 0.22/0.58  fof(f209,plain,(
% 0.22/0.58    $false | (~spl9_3 | spl9_7)),
% 0.22/0.58    inference(subsumption_resolution,[],[f208,f52])).
% 0.22/0.58  fof(f208,plain,(
% 0.22/0.58    ~l1_orders_2(sK3) | (~spl9_3 | spl9_7)),
% 0.22/0.58    inference(subsumption_resolution,[],[f207,f53])).
% 0.22/0.58  fof(f207,plain,(
% 0.22/0.58    ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | (~spl9_3 | spl9_7)),
% 0.22/0.58    inference(subsumption_resolution,[],[f206,f109])).
% 0.22/0.58  fof(f109,plain,(
% 0.22/0.58    v1_xboole_0(u1_struct_0(sK3)) | ~spl9_3),
% 0.22/0.58    inference(avatar_component_clause,[],[f107])).
% 0.22/0.58  fof(f107,plain,(
% 0.22/0.58    spl9_3 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.58  fof(f206,plain,(
% 0.22/0.58    ~v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | spl9_7),
% 0.22/0.58    inference(subsumption_resolution,[],[f205,f48])).
% 0.22/0.58  fof(f205,plain,(
% 0.22/0.58    v2_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | spl9_7),
% 0.22/0.58    inference(subsumption_resolution,[],[f204,f49])).
% 0.22/0.58  fof(f204,plain,(
% 0.22/0.58    ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | spl9_7),
% 0.22/0.58    inference(duplicate_literal_removal,[],[f203])).
% 0.22/0.58  fof(f203,plain,(
% 0.22/0.58    ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~v1_xboole_0(u1_struct_0(sK3)) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl9_7),
% 0.22/0.58    inference(resolution,[],[f190,f135])).
% 0.22/0.58  fof(f135,plain,(
% 0.22/0.58    ( ! [X2,X0,X3,X1] : (sP0(X2,k6_domain_1(u1_struct_0(X0),X1),X3) | ~v3_orders_2(X0) | v2_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~m1_subset_1(X3,u1_struct_0(X2))) )),
% 0.22/0.58    inference(resolution,[],[f128,f83])).
% 0.22/0.58  fof(f128,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,k6_domain_1(u1_struct_0(X1),X0)) | ~l1_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~m1_subset_1(X0,u1_struct_0(X1))) )),
% 0.22/0.58    inference(resolution,[],[f61,f80])).
% 0.22/0.58  fof(f80,plain,(
% 0.22/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f23])).
% 0.22/0.58  fof(f23,plain,(
% 0.22/0.58    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.58    inference(ennf_transformation,[],[f3])).
% 0.22/0.58  fof(f3,axiom,(
% 0.22/0.58    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.58  fof(f190,plain,(
% 0.22/0.58    ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4) | spl9_7),
% 0.22/0.58    inference(avatar_component_clause,[],[f188])).
% 0.22/0.58  fof(f188,plain,(
% 0.22/0.58    spl9_7 <=> sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_7])])).
% 0.22/0.58  fof(f202,plain,(
% 0.22/0.58    spl9_6),
% 0.22/0.58    inference(avatar_contradiction_clause,[],[f201])).
% 0.22/0.58  fof(f201,plain,(
% 0.22/0.58    $false | spl9_6),
% 0.22/0.58    inference(subsumption_resolution,[],[f200,f53])).
% 0.22/0.58  fof(f200,plain,(
% 0.22/0.58    ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl9_6),
% 0.22/0.58    inference(subsumption_resolution,[],[f199,f48])).
% 0.22/0.58  fof(f199,plain,(
% 0.22/0.58    v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl9_6),
% 0.22/0.58    inference(subsumption_resolution,[],[f198,f49])).
% 0.22/0.58  fof(f198,plain,(
% 0.22/0.58    ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl9_6),
% 0.22/0.58    inference(subsumption_resolution,[],[f197,f50])).
% 0.22/0.58  fof(f197,plain,(
% 0.22/0.58    ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl9_6),
% 0.22/0.58    inference(subsumption_resolution,[],[f196,f51])).
% 0.22/0.58  fof(f196,plain,(
% 0.22/0.58    ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl9_6),
% 0.22/0.58    inference(subsumption_resolution,[],[f195,f52])).
% 0.22/0.58  fof(f195,plain,(
% 0.22/0.58    ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | spl9_6),
% 0.22/0.58    inference(resolution,[],[f186,f134])).
% 0.22/0.58  fof(f186,plain,(
% 0.22/0.58    ~sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | spl9_6),
% 0.22/0.58    inference(avatar_component_clause,[],[f184])).
% 0.22/0.58  fof(f184,plain,(
% 0.22/0.58    spl9_6 <=> sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3)),
% 0.22/0.58    introduced(avatar_definition,[new_symbols(naming,[spl9_6])])).
% 0.22/0.58  fof(f191,plain,(
% 0.22/0.58    ~spl9_6 | ~spl9_7),
% 0.22/0.58    inference(avatar_split_clause,[],[f182,f188,f184])).
% 0.22/0.58  fof(f182,plain,(
% 0.22/0.58    ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4) | ~sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f181,f48])).
% 0.22/0.58  fof(f181,plain,(
% 0.22/0.58    ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4) | ~sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | v2_struct_0(sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f180,f49])).
% 0.22/0.58  fof(f180,plain,(
% 0.22/0.58    ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4) | ~sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f179,f50])).
% 0.22/0.58  fof(f179,plain,(
% 0.22/0.58    ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4) | ~sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f178,f51])).
% 0.22/0.58  fof(f178,plain,(
% 0.22/0.58    ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4) | ~sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f177,f52])).
% 0.22/0.58  fof(f177,plain,(
% 0.22/0.58    ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4) | ~sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.22/0.58    inference(subsumption_resolution,[],[f175,f53])).
% 0.22/0.58  fof(f175,plain,(
% 0.22/0.58    ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),sK4) | ~sP1(sK4,k6_domain_1(u1_struct_0(sK3),sK4),sK3) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)),
% 0.22/0.58    inference(resolution,[],[f171,f58])).
% 0.22/0.58  fof(f58,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f14])).
% 0.22/0.58  fof(f14,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.58    inference(flattening,[],[f13])).
% 0.22/0.58  fof(f13,plain,(
% 0.22/0.58    ! [X0] : (! [X1] : (~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f8])).
% 0.22/0.58  fof(f8,axiom,(
% 0.22/0.58    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).
% 0.22/0.58  fof(f171,plain,(
% 0.22/0.58    ( ! [X0] : (r2_hidden(X0,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))) | ~sP0(sK3,k6_domain_1(u1_struct_0(sK3),sK4),X0) | ~sP1(X0,k6_domain_1(u1_struct_0(sK3),sK4),sK3)) )),
% 0.22/0.58    inference(superposition,[],[f64,f165])).
% 0.22/0.58  fof(f165,plain,(
% 0.22/0.58    k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 0.22/0.58    inference(subsumption_resolution,[],[f164,f48])).
% 0.22/0.58  fof(f164,plain,(
% 0.22/0.58    v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 0.22/0.58    inference(subsumption_resolution,[],[f163,f49])).
% 0.22/0.58  fof(f163,plain,(
% 0.22/0.58    ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 0.22/0.58    inference(subsumption_resolution,[],[f162,f50])).
% 0.22/0.58  fof(f162,plain,(
% 0.22/0.58    ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 0.22/0.58    inference(subsumption_resolution,[],[f161,f51])).
% 0.22/0.58  fof(f161,plain,(
% 0.22/0.58    ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 0.22/0.58    inference(subsumption_resolution,[],[f157,f52])).
% 0.22/0.58  fof(f157,plain,(
% 0.22/0.58    ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4)) = a_2_1_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK4))),
% 0.22/0.58    inference(resolution,[],[f142,f53])).
% 0.22/0.58  fof(f119,plain,(
% 0.22/0.58    spl9_3 | spl9_5),
% 0.22/0.58    inference(avatar_split_clause,[],[f104,f116,f107])).
% 0.22/0.58  fof(f104,plain,(
% 0.22/0.58    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.58    inference(resolution,[],[f81,f54])).
% 0.22/0.58  fof(f81,plain,(
% 0.22/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(definition_unfolding,[],[f62,f57])).
% 0.22/0.58  fof(f57,plain,(
% 0.22/0.58    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f2])).
% 0.22/0.58  fof(f2,axiom,(
% 0.22/0.58    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.58  fof(f62,plain,(
% 0.22/0.58    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.58    inference(cnf_transformation,[],[f20])).
% 0.22/0.58  fof(f20,plain,(
% 0.22/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.58    inference(flattening,[],[f19])).
% 0.22/0.58  fof(f19,plain,(
% 0.22/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.58    inference(ennf_transformation,[],[f6])).
% 0.22/0.58  fof(f6,axiom,(
% 0.22/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.58  fof(f97,plain,(
% 0.22/0.58    spl9_1 | spl9_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f55,f93,f89])).
% 0.22/0.58  fof(f55,plain,(
% 0.22/0.58    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  fof(f96,plain,(
% 0.22/0.58    ~spl9_1 | ~spl9_2),
% 0.22/0.58    inference(avatar_split_clause,[],[f56,f93,f89])).
% 0.22/0.58  fof(f56,plain,(
% 0.22/0.58    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)),
% 0.22/0.58    inference(cnf_transformation,[],[f34])).
% 0.22/0.58  % SZS output end Proof for theBenchmark
% 0.22/0.58  % (6817)------------------------------
% 0.22/0.58  % (6817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.58  % (6817)Termination reason: Refutation
% 0.22/0.58  
% 0.22/0.58  % (6817)Memory used [KB]: 11001
% 0.22/0.58  % (6817)Time elapsed: 0.163 s
% 0.22/0.58  % (6817)------------------------------
% 0.22/0.58  % (6817)------------------------------
% 0.22/0.58  % (6810)Success in time 0.211 s
%------------------------------------------------------------------------------
