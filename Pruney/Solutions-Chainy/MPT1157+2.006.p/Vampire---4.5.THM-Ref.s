%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:02 EST 2020

% Result     : Theorem 1.26s
% Output     : Refutation 1.38s
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
    inference(avatar_sat_refutation,[],[f114,f115,f134,f194,f323,f637])).

fof(f637,plain,
    ( ~ spl11_1
    | spl11_2
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f636])).

fof(f636,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f635,f65])).

fof(f65,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).

fof(f37,plain,
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

fof(f38,plain,
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

fof(f39,plain,
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

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
                <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
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
              <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).

fof(f635,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ spl11_1
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f634,f325])).

fof(f325,plain,
    ( ~ sP1(sK4,k2_tarski(sK5,sK5),sK6)
    | spl11_2
    | ~ spl11_4 ),
    inference(resolution,[],[f324,f284])).

fof(f284,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
        | ~ sP1(sK4,k2_tarski(sK5,sK5),X0) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f282,f237])).

fof(f237,plain,
    ( ! [X2] : sP2(X2,k2_tarski(sK5,sK5),sK4)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f236,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f236,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK5,sK5),sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f235,f60])).

fof(f60,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f235,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK5,sK5),sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f234,f61])).

fof(f61,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f234,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK5,sK5),sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f233,f62])).

fof(f62,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f233,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK5,sK5),sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f222,f63])).

fof(f63,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f40])).

fof(f222,plain,
    ( ! [X2] :
        ( sP2(X2,k2_tarski(sK5,sK5),sK4)
        | ~ l1_orders_2(sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | ~ spl11_4 ),
    inference(resolution,[],[f210,f89])).

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
              ( r2_orders_2(X1,X4,X3)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f31,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> sP1(X1,X2,X0) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f5])).

% (29788)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).

fof(f210,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f209,f59])).

fof(f209,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v2_struct_0(sK4)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f208,f60])).

fof(f208,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f207,f63])).

fof(f207,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f205,f64])).

fof(f64,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f40])).

fof(f205,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_4 ),
    inference(superposition,[],[f72,f133])).

fof(f133,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl11_4
  <=> k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(f282,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
        | ~ sP1(sK4,k2_tarski(sK5,sK5),X0)
        | ~ sP2(X0,k2_tarski(sK5,sK5),sK4) )
    | ~ spl11_4 ),
    inference(superposition,[],[f82,f232])).

fof(f232,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f231,f59])).

fof(f231,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | v2_struct_0(sK4)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f230,f60])).

fof(f230,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f229,f61])).

fof(f229,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f228,f62])).

fof(f228,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f221,f63])).

fof(f221,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | ~ spl11_4 ),
    inference(resolution,[],[f210,f69])).

% (29774)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
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
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
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
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f46])).

fof(f46,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ~ sP1(X1,X2,X0) )
        & ( sP1(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f324,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
    | spl11_2
    | ~ spl11_4 ),
    inference(forward_demodulation,[],[f113,f133])).

fof(f113,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl11_2
  <=> r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f634,plain,
    ( sP1(sK4,k2_tarski(sK5,sK5),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ spl11_1
    | spl11_2
    | ~ spl11_4 ),
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
    | sP1(sK4,k2_tarski(sK5,sK5),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | spl11_2
    | ~ spl11_4 ),
    inference(superposition,[],[f100,f607])).

fof(f607,plain,
    ( sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6)
    | spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f606,f65])).

fof(f606,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6)
    | spl11_2
    | ~ spl11_4 ),
    inference(duplicate_literal_removal,[],[f599])).

fof(f599,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6)
    | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6)
    | spl11_2
    | ~ spl11_4 ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

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
            ( ( ~ r2_orders_2(X0,sK8(X0,X1,X3),X3)
              & r2_hidden(sK8(X0,X1,X3),X1)
              & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,X6,sK9(X0,X1,X2))
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK9(X0,X1,X2) = X2
          & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP1(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f49,f51,f50])).

fof(f50,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X4,X3)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK8(X0,X1,X3),X3)
        & r2_hidden(sK8(X0,X1,X3),X1)
        & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X6,X5)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,X6,sK9(X0,X1,X2))
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK9(X0,X1,X2) = X2
        & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (29789)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( sP1(X0,X1,X2)
        | ! [X3] :
            ( ? [X4] :
                ( ~ r2_orders_2(X0,X4,X3)
                & r2_hidden(X4,X1)
                & m1_subset_1(X4,u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ? [X5] :
            ( ! [X6] :
                ( r2_orders_2(X0,X6,X5)
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
                ( ~ r2_orders_2(X1,X4,X3)
                & r2_hidden(X4,X2)
                & m1_subset_1(X4,u1_struct_0(X1)) )
            | X0 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
      & ( ? [X3] :
            ( ! [X4] :
                ( r2_orders_2(X1,X4,X3)
                | ~ r2_hidden(X4,X2)
                | ~ m1_subset_1(X4,u1_struct_0(X1)) )
            & X0 = X3
            & m1_subset_1(X3,u1_struct_0(X1)) )
        | ~ sP1(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f100,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_orders_2(X0,sK8(X0,X1,X3),X3)
      | sP1(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | ~ r2_orders_2(X0,sK8(X0,X1,X3),X3)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f323,plain,
    ( spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f322])).

fof(f322,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f321,f64])).

fof(f321,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | spl11_1
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f315,f109])).

fof(f109,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f107])).

fof(f315,plain,
    ( r2_orders_2(sK4,sK5,sK6)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(resolution,[],[f305,f119])).

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

fof(f305,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | r2_orders_2(sK4,X1,sK6)
        | ~ m1_subset_1(X1,u1_struct_0(sK4)) )
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f302,f296])).

% (29782)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f296,plain,
    ( sP1(sK4,k2_tarski(sK5,sK5),sK6)
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(resolution,[],[f285,f203])).

fof(f203,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(backward_demodulation,[],[f112,f133])).

fof(f112,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f111])).

fof(f285,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
        | sP1(sK4,k2_tarski(sK5,sK5),X1) )
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f283,f237])).

fof(f283,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
        | sP1(sK4,k2_tarski(sK5,sK5),X1)
        | ~ sP2(X1,k2_tarski(sK5,sK5),sK4) )
    | ~ spl11_4 ),
    inference(superposition,[],[f81,f232])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f302,plain,
    ( ! [X1] :
        ( r2_orders_2(sK4,X1,sK6)
        | ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ sP1(sK4,k2_tarski(sK5,sK5),sK6) )
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(superposition,[],[f85,f299])).

fof(f299,plain,
    ( sK6 = sK9(sK4,k2_tarski(sK5,sK5),sK6)
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(resolution,[],[f296,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sK9(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f85,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X0,X6,sK9(X0,X1,X2))
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).

fof(f134,plain,
    ( spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f122,f131,f127])).

fof(f122,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f99,f64])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f115,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f66,f111,f107])).

fof(f66,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).

fof(f114,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f67,f111,f107])).

fof(f67,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | ~ r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 15:50:51 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.50  % (29767)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.51  % (29776)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.51  % (29763)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (29784)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (29765)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (29787)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.52  % (29773)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.52  % (29766)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.26/0.53  % (29779)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.26/0.53  % (29761)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.26/0.53  % (29762)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.26/0.53  % (29785)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.26/0.53  % (29777)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.26/0.53  % (29764)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.54  % (29772)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.26/0.54  % (29767)Refutation found. Thanks to Tanya!
% 1.26/0.54  % SZS status Theorem for theBenchmark
% 1.26/0.54  % (29772)Refutation not found, incomplete strategy% (29772)------------------------------
% 1.26/0.54  % (29772)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (29772)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (29772)Memory used [KB]: 10746
% 1.26/0.54  % (29772)Time elapsed: 0.137 s
% 1.26/0.54  % (29772)------------------------------
% 1.26/0.54  % (29772)------------------------------
% 1.26/0.54  % (29792)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.26/0.54  % (29792)Refutation not found, incomplete strategy% (29792)------------------------------
% 1.26/0.54  % (29792)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (29792)Termination reason: Refutation not found, incomplete strategy
% 1.26/0.54  
% 1.26/0.54  % (29792)Memory used [KB]: 1663
% 1.26/0.54  % (29792)Time elapsed: 0.001 s
% 1.26/0.54  % (29792)------------------------------
% 1.26/0.54  % (29792)------------------------------
% 1.26/0.54  % SZS output start Proof for theBenchmark
% 1.26/0.54  fof(f638,plain,(
% 1.26/0.54    $false),
% 1.26/0.54    inference(avatar_sat_refutation,[],[f114,f115,f134,f194,f323,f637])).
% 1.26/0.54  fof(f637,plain,(
% 1.26/0.54    ~spl11_1 | spl11_2 | ~spl11_4),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f636])).
% 1.26/0.54  fof(f636,plain,(
% 1.26/0.54    $false | (~spl11_1 | spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f635,f65])).
% 1.26/0.54  fof(f65,plain,(
% 1.26/0.54    m1_subset_1(sK6,u1_struct_0(sK4))),
% 1.26/0.54    inference(cnf_transformation,[],[f40])).
% 1.26/0.54  fof(f40,plain,(
% 1.26/0.54    (((~r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,sK6)) & (r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,sK6)) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f36,f39,f38,f37])).
% 1.26/0.54  fof(f37,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1))) | ~r2_orders_2(sK4,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1))) | r2_orders_2(sK4,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f38,plain,(
% 1.26/0.54    ? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1))) | ~r2_orders_2(sK4,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1))) | r2_orders_2(sK4,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) => (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,X2)) & (r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4)))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f39,plain,(
% 1.26/0.54    ? [X2] : ((~r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,X2)) & (r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) => ((~r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,sK6)) & (r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,sK6)) & m1_subset_1(sK6,u1_struct_0(sK4)))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f36,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.26/0.54    inference(flattening,[],[f35])).
% 1.26/0.54  fof(f35,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.26/0.54    inference(nnf_transformation,[],[f14])).
% 1.26/0.54  fof(f14,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.26/0.54    inference(flattening,[],[f13])).
% 1.26/0.54  fof(f13,plain,(
% 1.26/0.54    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f11])).
% 1.26/0.54  fof(f11,negated_conjecture,(
% 1.26/0.54    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 1.26/0.54    inference(negated_conjecture,[],[f10])).
% 1.26/0.54  fof(f10,conjecture,(
% 1.26/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_orders_2)).
% 1.26/0.54  fof(f635,plain,(
% 1.26/0.54    ~m1_subset_1(sK6,u1_struct_0(sK4)) | (~spl11_1 | spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f634,f325])).
% 1.26/0.54  fof(f325,plain,(
% 1.26/0.54    ~sP1(sK4,k2_tarski(sK5,sK5),sK6) | (spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(resolution,[],[f324,f284])).
% 1.26/0.54  fof(f284,plain,(
% 1.26/0.54    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | ~sP1(sK4,k2_tarski(sK5,sK5),X0)) ) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f282,f237])).
% 1.26/0.54  fof(f237,plain,(
% 1.26/0.54    ( ! [X2] : (sP2(X2,k2_tarski(sK5,sK5),sK4)) ) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f236,f59])).
% 1.26/0.54  fof(f59,plain,(
% 1.26/0.54    ~v2_struct_0(sK4)),
% 1.26/0.54    inference(cnf_transformation,[],[f40])).
% 1.26/0.54  fof(f236,plain,(
% 1.26/0.54    ( ! [X2] : (sP2(X2,k2_tarski(sK5,sK5),sK4) | v2_struct_0(sK4)) ) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f235,f60])).
% 1.26/0.54  fof(f60,plain,(
% 1.26/0.54    v3_orders_2(sK4)),
% 1.26/0.54    inference(cnf_transformation,[],[f40])).
% 1.26/0.54  fof(f235,plain,(
% 1.26/0.54    ( ! [X2] : (sP2(X2,k2_tarski(sK5,sK5),sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f234,f61])).
% 1.26/0.54  fof(f61,plain,(
% 1.26/0.54    v4_orders_2(sK4)),
% 1.26/0.54    inference(cnf_transformation,[],[f40])).
% 1.26/0.54  fof(f234,plain,(
% 1.26/0.54    ( ! [X2] : (sP2(X2,k2_tarski(sK5,sK5),sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f233,f62])).
% 1.26/0.54  fof(f62,plain,(
% 1.26/0.54    v5_orders_2(sK4)),
% 1.26/0.54    inference(cnf_transformation,[],[f40])).
% 1.26/0.54  fof(f233,plain,(
% 1.26/0.54    ( ! [X2] : (sP2(X2,k2_tarski(sK5,sK5),sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f222,f63])).
% 1.26/0.54  fof(f63,plain,(
% 1.26/0.54    l1_orders_2(sK4)),
% 1.26/0.54    inference(cnf_transformation,[],[f40])).
% 1.26/0.54  fof(f222,plain,(
% 1.26/0.54    ( ! [X2] : (sP2(X2,k2_tarski(sK5,sK5),sK4) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | ~spl11_4),
% 1.26/0.54    inference(resolution,[],[f210,f89])).
% 1.26/0.54  fof(f89,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP2(X0,X2,X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f32])).
% 1.26/0.54  fof(f32,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (sP2(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.26/0.54    inference(definition_folding,[],[f26,f31,f30])).
% 1.26/0.54  fof(f30,plain,(
% 1.26/0.54    ! [X1,X2,X0] : (sP1(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.26/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.26/0.54  fof(f31,plain,(
% 1.26/0.54    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> sP1(X1,X2,X0)) | ~sP2(X0,X2,X1))),
% 1.26/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 1.26/0.54  fof(f26,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.26/0.54    inference(flattening,[],[f25])).
% 1.26/0.54  fof(f25,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.26/0.54    inference(ennf_transformation,[],[f5])).
% 1.26/0.54  % (29788)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.26/0.54  fof(f5,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 1.26/0.54  fof(f210,plain,(
% 1.26/0.54    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f209,f59])).
% 1.26/0.54  fof(f209,plain,(
% 1.26/0.54    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v2_struct_0(sK4) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f208,f60])).
% 1.26/0.54  fof(f208,plain,(
% 1.26/0.54    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f207,f63])).
% 1.26/0.54  fof(f207,plain,(
% 1.26/0.54    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f205,f64])).
% 1.26/0.54  fof(f64,plain,(
% 1.26/0.54    m1_subset_1(sK5,u1_struct_0(sK4))),
% 1.26/0.54    inference(cnf_transformation,[],[f40])).
% 1.26/0.54  fof(f205,plain,(
% 1.26/0.54    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_4),
% 1.26/0.54    inference(superposition,[],[f72,f133])).
% 1.26/0.54  fof(f133,plain,(
% 1.26/0.54    k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) | ~spl11_4),
% 1.26/0.54    inference(avatar_component_clause,[],[f131])).
% 1.26/0.54  fof(f131,plain,(
% 1.26/0.54    spl11_4 <=> k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 1.26/0.54  fof(f72,plain,(
% 1.26/0.54    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f20])).
% 1.26/0.54  fof(f20,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.54    inference(flattening,[],[f19])).
% 1.26/0.54  fof(f19,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f8])).
% 1.26/0.54  fof(f8,axiom,(
% 1.26/0.54    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
% 1.26/0.54  fof(f282,plain,(
% 1.26/0.54    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | ~sP1(sK4,k2_tarski(sK5,sK5),X0) | ~sP2(X0,k2_tarski(sK5,sK5),sK4)) ) | ~spl11_4),
% 1.26/0.54    inference(superposition,[],[f82,f232])).
% 1.26/0.54  fof(f232,plain,(
% 1.26/0.54    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f231,f59])).
% 1.26/0.54  fof(f231,plain,(
% 1.26/0.54    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | v2_struct_0(sK4) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f230,f60])).
% 1.26/0.54  fof(f230,plain,(
% 1.26/0.54    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f229,f61])).
% 1.26/0.54  fof(f229,plain,(
% 1.26/0.54    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f228,f62])).
% 1.26/0.54  fof(f228,plain,(
% 1.26/0.54    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_4),
% 1.26/0.54    inference(subsumption_resolution,[],[f221,f63])).
% 1.26/0.54  fof(f221,plain,(
% 1.26/0.54    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | ~spl11_4),
% 1.26/0.54    inference(resolution,[],[f210,f69])).
% 1.26/0.54  % (29774)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.26/0.54  fof(f69,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f16])).
% 1.26/0.54  fof(f16,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.54    inference(flattening,[],[f15])).
% 1.26/0.54  fof(f15,plain,(
% 1.26/0.54    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f4])).
% 1.26/0.54  fof(f4,axiom,(
% 1.26/0.54    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_orders_2)).
% 1.26/0.54  fof(f82,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f47])).
% 1.26/0.54  fof(f47,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)))) | ~sP2(X0,X1,X2))),
% 1.26/0.54    inference(rectify,[],[f46])).
% 1.26/0.54  fof(f46,plain,(
% 1.26/0.54    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~sP1(X1,X2,X0)) & (sP1(X1,X2,X0) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~sP2(X0,X2,X1))),
% 1.26/0.54    inference(nnf_transformation,[],[f31])).
% 1.26/0.54  fof(f324,plain,(
% 1.26/0.54    ~r2_hidden(sK6,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | (spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(forward_demodulation,[],[f113,f133])).
% 1.26/0.54  fof(f113,plain,(
% 1.26/0.54    ~r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | spl11_2),
% 1.26/0.54    inference(avatar_component_clause,[],[f111])).
% 1.26/0.54  fof(f111,plain,(
% 1.26/0.54    spl11_2 <=> r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 1.26/0.54  fof(f634,plain,(
% 1.26/0.54    sP1(sK4,k2_tarski(sK5,sK5),sK6) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | (~spl11_1 | spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f620,f108])).
% 1.26/0.54  fof(f108,plain,(
% 1.26/0.54    r2_orders_2(sK4,sK5,sK6) | ~spl11_1),
% 1.26/0.54    inference(avatar_component_clause,[],[f107])).
% 1.26/0.54  fof(f107,plain,(
% 1.26/0.54    spl11_1 <=> r2_orders_2(sK4,sK5,sK6)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 1.26/0.54  fof(f620,plain,(
% 1.26/0.54    ~r2_orders_2(sK4,sK5,sK6) | sP1(sK4,k2_tarski(sK5,sK5),sK6) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | (spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(superposition,[],[f100,f607])).
% 1.26/0.54  fof(f607,plain,(
% 1.26/0.54    sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6) | (spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f606,f65])).
% 1.26/0.54  fof(f606,plain,(
% 1.26/0.54    ~m1_subset_1(sK6,u1_struct_0(sK4)) | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6) | (spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(duplicate_literal_removal,[],[f599])).
% 1.26/0.54  fof(f599,plain,(
% 1.26/0.54    ~m1_subset_1(sK6,u1_struct_0(sK4)) | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6) | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6) | (spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(resolution,[],[f159,f325])).
% 1.26/0.54  fof(f159,plain,(
% 1.26/0.54    ( ! [X6,X4,X7,X5] : (sP1(X4,k2_tarski(X5,X6),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | sK8(X4,k2_tarski(X5,X6),X7) = X5 | sK8(X4,k2_tarski(X5,X6),X7) = X6) )),
% 1.26/0.54    inference(resolution,[],[f101,f142])).
% 1.26/0.54  fof(f142,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 1.26/0.54    inference(resolution,[],[f90,f105])).
% 1.26/0.54  fof(f105,plain,(
% 1.26/0.54    ( ! [X0,X1] : (sP3(X1,X0,k2_tarski(X0,X1))) )),
% 1.26/0.54    inference(equality_resolution,[],[f96])).
% 1.26/0.54  fof(f96,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.26/0.54    inference(cnf_transformation,[],[f58])).
% 1.26/0.54  fof(f58,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.26/0.54    inference(nnf_transformation,[],[f34])).
% 1.26/0.54  fof(f34,plain,(
% 1.26/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP3(X1,X0,X2))),
% 1.26/0.54    inference(definition_folding,[],[f1,f33])).
% 1.26/0.54  fof(f33,plain,(
% 1.26/0.54    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.26/0.54    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 1.26/0.54  fof(f1,axiom,(
% 1.26/0.54    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.26/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.26/0.54  fof(f90,plain,(
% 1.26/0.54    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 1.26/0.54    inference(cnf_transformation,[],[f57])).
% 1.26/0.54  fof(f57,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (((sK10(X0,X1,X2) != X0 & sK10(X0,X1,X2) != X1) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sK10(X0,X1,X2) = X0 | sK10(X0,X1,X2) = X1 | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f55,f56])).
% 1.26/0.54  fof(f56,plain,(
% 1.26/0.54    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK10(X0,X1,X2) != X0 & sK10(X0,X1,X2) != X1) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sK10(X0,X1,X2) = X0 | sK10(X0,X1,X2) = X1 | r2_hidden(sK10(X0,X1,X2),X2))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f55,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 1.26/0.54    inference(rectify,[],[f54])).
% 1.26/0.54  fof(f54,plain,(
% 1.26/0.54    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP3(X1,X0,X2)))),
% 1.26/0.54    inference(flattening,[],[f53])).
% 1.26/0.54  fof(f53,plain,(
% 1.26/0.54    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP3(X1,X0,X2)))),
% 1.26/0.54    inference(nnf_transformation,[],[f33])).
% 1.26/0.54  fof(f101,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | sP1(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.26/0.54    inference(equality_resolution,[],[f87])).
% 1.26/0.54  fof(f87,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2) | r2_hidden(sK8(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f52])).
% 1.26/0.54  fof(f52,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,sK8(X0,X1,X3),X3) & r2_hidden(sK8(X0,X1,X3),X1) & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,X6,sK9(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))) | ~sP1(X0,X1,X2)))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f49,f51,f50])).
% 1.26/0.54  fof(f50,plain,(
% 1.26/0.54    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,sK8(X0,X1,X3),X3) & r2_hidden(sK8(X0,X1,X3),X1) & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f51,plain,(
% 1.26/0.54    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,X6,sK9(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  % (29789)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.26/0.54  fof(f49,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP1(X0,X1,X2)))),
% 1.26/0.54    inference(rectify,[],[f48])).
% 1.26/0.54  fof(f48,plain,(
% 1.26/0.54    ! [X1,X2,X0] : ((sP1(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X1,X2,X0)))),
% 1.26/0.54    inference(nnf_transformation,[],[f30])).
% 1.26/0.54  fof(f100,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (~r2_orders_2(X0,sK8(X0,X1,X3),X3) | sP1(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.26/0.54    inference(equality_resolution,[],[f88])).
% 1.26/0.54  fof(f88,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2) | ~r2_orders_2(X0,sK8(X0,X1,X3),X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f52])).
% 1.26/0.54  fof(f323,plain,(
% 1.26/0.54    spl11_1 | ~spl11_2 | ~spl11_4),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f322])).
% 1.26/0.54  fof(f322,plain,(
% 1.26/0.54    $false | (spl11_1 | ~spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f321,f64])).
% 1.26/0.54  fof(f321,plain,(
% 1.26/0.54    ~m1_subset_1(sK5,u1_struct_0(sK4)) | (spl11_1 | ~spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f315,f109])).
% 1.26/0.54  fof(f109,plain,(
% 1.26/0.54    ~r2_orders_2(sK4,sK5,sK6) | spl11_1),
% 1.26/0.54    inference(avatar_component_clause,[],[f107])).
% 1.26/0.54  fof(f315,plain,(
% 1.26/0.54    r2_orders_2(sK4,sK5,sK6) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | (~spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(resolution,[],[f305,f119])).
% 1.26/0.54  fof(f119,plain,(
% 1.26/0.54    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 1.26/0.54    inference(resolution,[],[f104,f105])).
% 1.26/0.54  fof(f104,plain,(
% 1.26/0.54    ( ! [X4,X2,X0] : (~sP3(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 1.26/0.54    inference(equality_resolution,[],[f91])).
% 1.26/0.54  fof(f91,plain,(
% 1.26/0.54    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP3(X0,X1,X2)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f57])).
% 1.26/0.54  fof(f305,plain,(
% 1.26/0.54    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK5,sK5)) | r2_orders_2(sK4,X1,sK6) | ~m1_subset_1(X1,u1_struct_0(sK4))) ) | (~spl11_2 | ~spl11_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f302,f296])).
% 1.38/0.55  % (29782)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.55  fof(f296,plain,(
% 1.38/0.55    sP1(sK4,k2_tarski(sK5,sK5),sK6) | (~spl11_2 | ~spl11_4)),
% 1.38/0.55    inference(resolution,[],[f285,f203])).
% 1.38/0.55  fof(f203,plain,(
% 1.38/0.55    r2_hidden(sK6,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | (~spl11_2 | ~spl11_4)),
% 1.38/0.55    inference(backward_demodulation,[],[f112,f133])).
% 1.38/0.55  fof(f112,plain,(
% 1.38/0.55    r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~spl11_2),
% 1.38/0.55    inference(avatar_component_clause,[],[f111])).
% 1.38/0.55  fof(f285,plain,(
% 1.38/0.55    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | sP1(sK4,k2_tarski(sK5,sK5),X1)) ) | ~spl11_4),
% 1.38/0.55    inference(subsumption_resolution,[],[f283,f237])).
% 1.38/0.55  fof(f283,plain,(
% 1.38/0.55    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | sP1(sK4,k2_tarski(sK5,sK5),X1) | ~sP2(X1,k2_tarski(sK5,sK5),sK4)) ) | ~spl11_4),
% 1.38/0.55    inference(superposition,[],[f81,f232])).
% 1.38/0.55  fof(f81,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(X2,X1)) | sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f47])).
% 1.38/0.55  fof(f302,plain,(
% 1.38/0.55    ( ! [X1] : (r2_orders_2(sK4,X1,sK6) | ~r2_hidden(X1,k2_tarski(sK5,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~sP1(sK4,k2_tarski(sK5,sK5),sK6)) ) | (~spl11_2 | ~spl11_4)),
% 1.38/0.55    inference(superposition,[],[f85,f299])).
% 1.38/0.55  fof(f299,plain,(
% 1.38/0.55    sK6 = sK9(sK4,k2_tarski(sK5,sK5),sK6) | (~spl11_2 | ~spl11_4)),
% 1.38/0.55    inference(resolution,[],[f296,f84])).
% 1.38/0.55  fof(f84,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | sK9(X0,X1,X2) = X2) )),
% 1.38/0.55    inference(cnf_transformation,[],[f52])).
% 1.38/0.55  fof(f85,plain,(
% 1.38/0.55    ( ! [X6,X2,X0,X1] : (r2_orders_2(X0,X6,sK9(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP1(X0,X1,X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f52])).
% 1.38/0.55  fof(f194,plain,(
% 1.38/0.55    ~spl11_3),
% 1.38/0.55    inference(avatar_contradiction_clause,[],[f193])).
% 1.38/0.55  fof(f193,plain,(
% 1.38/0.55    $false | ~spl11_3),
% 1.38/0.55    inference(subsumption_resolution,[],[f192,f129])).
% 1.38/0.55  fof(f129,plain,(
% 1.38/0.55    v1_xboole_0(u1_struct_0(sK4)) | ~spl11_3),
% 1.38/0.55    inference(avatar_component_clause,[],[f127])).
% 1.38/0.55  fof(f127,plain,(
% 1.38/0.55    spl11_3 <=> v1_xboole_0(u1_struct_0(sK4))),
% 1.38/0.55    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 1.38/0.55  fof(f192,plain,(
% 1.38/0.55    ~v1_xboole_0(u1_struct_0(sK4))),
% 1.38/0.55    inference(resolution,[],[f178,f147])).
% 1.38/0.55  fof(f147,plain,(
% 1.38/0.55    ( ! [X4,X5,X3] : (~sP0(X4,X5,X3) | ~v1_xboole_0(u1_struct_0(X3))) )),
% 1.38/0.55    inference(duplicate_literal_removal,[],[f146])).
% 1.38/0.55  fof(f146,plain,(
% 1.38/0.55    ( ! [X4,X5,X3] : (~v1_xboole_0(u1_struct_0(X3)) | ~sP0(X4,X5,X3) | ~sP0(X4,X5,X3)) )),
% 1.38/0.55    inference(resolution,[],[f121,f76])).
% 1.38/0.55  fof(f76,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (r2_hidden(X0,sK7(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f44])).
% 1.38/0.55  fof(f44,plain,(
% 1.38/0.55    ! [X0,X1,X2] : ((r2_hidden(X0,sK7(X0,X1,X2)) & r2_hidden(X1,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK7(X0,X1,X2),X2)) | ~sP0(X0,X1,X2))),
% 1.38/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f42,f43])).
% 1.38/0.55  fof(f43,plain,(
% 1.38/0.55    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) => (r2_hidden(X0,sK7(X0,X1,X2)) & r2_hidden(X1,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK7(X0,X1,X2),X2)))),
% 1.38/0.55    introduced(choice_axiom,[])).
% 1.38/0.55  fof(f42,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) | ~sP0(X0,X1,X2))),
% 1.38/0.55    inference(rectify,[],[f41])).
% 1.38/0.55  fof(f41,plain,(
% 1.38/0.55    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | ~sP0(X2,X1,X0))),
% 1.38/0.55    inference(nnf_transformation,[],[f28])).
% 1.38/0.55  fof(f28,plain,(
% 1.38/0.55    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | ~sP0(X2,X1,X0))),
% 1.38/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.38/0.55  fof(f121,plain,(
% 1.38/0.55    ( ! [X2,X0,X3,X1] : (~r2_hidden(X3,sK7(X0,X1,X2)) | ~v1_xboole_0(u1_struct_0(X2)) | ~sP0(X0,X1,X2)) )),
% 1.38/0.55    inference(resolution,[],[f74,f98])).
% 1.38/0.55  fof(f98,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f27])).
% 1.38/0.55  fof(f27,plain,(
% 1.38/0.55    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.38/0.55    inference(ennf_transformation,[],[f3])).
% 1.38/0.55  fof(f3,axiom,(
% 1.38/0.55    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.38/0.55  fof(f74,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f44])).
% 1.38/0.55  fof(f178,plain,(
% 1.38/0.55    sP0(sK5,sK5,sK4)),
% 1.38/0.55    inference(subsumption_resolution,[],[f177,f60])).
% 1.38/0.55  fof(f177,plain,(
% 1.38/0.55    sP0(sK5,sK5,sK4) | ~v3_orders_2(sK4)),
% 1.38/0.55    inference(subsumption_resolution,[],[f176,f63])).
% 1.38/0.55  fof(f176,plain,(
% 1.38/0.55    sP0(sK5,sK5,sK4) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4)),
% 1.38/0.55    inference(subsumption_resolution,[],[f175,f64])).
% 1.38/0.55  fof(f175,plain,(
% 1.38/0.55    sP0(sK5,sK5,sK4) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4)),
% 1.38/0.55    inference(duplicate_literal_removal,[],[f172])).
% 1.38/0.55  fof(f172,plain,(
% 1.38/0.55    sP0(sK5,sK5,sK4) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4)),
% 1.38/0.55    inference(resolution,[],[f78,f154])).
% 1.38/0.55  fof(f154,plain,(
% 1.38/0.55    r1_orders_2(sK4,sK5,sK5)),
% 1.38/0.55    inference(subsumption_resolution,[],[f153,f59])).
% 1.38/0.55  fof(f153,plain,(
% 1.38/0.55    r1_orders_2(sK4,sK5,sK5) | v2_struct_0(sK4)),
% 1.38/0.55    inference(subsumption_resolution,[],[f152,f60])).
% 1.38/0.55  fof(f152,plain,(
% 1.38/0.55    r1_orders_2(sK4,sK5,sK5) | ~v3_orders_2(sK4) | v2_struct_0(sK4)),
% 1.38/0.55    inference(subsumption_resolution,[],[f149,f63])).
% 1.38/0.55  fof(f149,plain,(
% 1.38/0.55    r1_orders_2(sK4,sK5,sK5) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)),
% 1.38/0.55    inference(resolution,[],[f70,f64])).
% 1.38/0.55  fof(f70,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f18])).
% 1.38/0.55  fof(f18,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.38/0.55    inference(flattening,[],[f17])).
% 1.38/0.55  fof(f17,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f7])).
% 1.38/0.55  fof(f7,axiom,(
% 1.38/0.55    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_orders_2)).
% 1.38/0.55  fof(f78,plain,(
% 1.38/0.55    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | sP0(X2,X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f45])).
% 1.38/0.55  fof(f45,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (((sP0(X2,X1,X0) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.38/0.55    inference(rectify,[],[f29])).
% 1.38/0.55  fof(f29,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (((sP0(X2,X1,X0) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.38/0.55    inference(definition_folding,[],[f22,f28])).
% 1.38/0.55  fof(f22,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 1.38/0.55    inference(flattening,[],[f21])).
% 1.38/0.55  fof(f21,plain,(
% 1.38/0.55    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f12])).
% 1.38/0.55  fof(f12,plain,(
% 1.38/0.55    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 1.38/0.55    inference(rectify,[],[f9])).
% 1.38/0.55  fof(f9,axiom,(
% 1.38/0.55    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_orders_2)).
% 1.38/0.55  fof(f134,plain,(
% 1.38/0.55    spl11_3 | spl11_4),
% 1.38/0.55    inference(avatar_split_clause,[],[f122,f131,f127])).
% 1.38/0.55  fof(f122,plain,(
% 1.38/0.55    k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) | v1_xboole_0(u1_struct_0(sK4))),
% 1.38/0.55    inference(resolution,[],[f99,f64])).
% 1.38/0.55  fof(f99,plain,(
% 1.38/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 1.38/0.55    inference(definition_unfolding,[],[f80,f68])).
% 1.38/0.55  fof(f68,plain,(
% 1.38/0.55    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f2])).
% 1.38/0.55  fof(f2,axiom,(
% 1.38/0.55    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.38/0.55  fof(f80,plain,(
% 1.38/0.55    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.38/0.55    inference(cnf_transformation,[],[f24])).
% 1.38/0.55  fof(f24,plain,(
% 1.38/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.38/0.55    inference(flattening,[],[f23])).
% 1.38/0.55  fof(f23,plain,(
% 1.38/0.55    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.38/0.55    inference(ennf_transformation,[],[f6])).
% 1.38/0.55  fof(f6,axiom,(
% 1.38/0.55    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.38/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.38/0.55  fof(f115,plain,(
% 1.38/0.55    spl11_1 | spl11_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f66,f111,f107])).
% 1.38/0.55  fof(f66,plain,(
% 1.38/0.55    r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,sK6)),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  fof(f114,plain,(
% 1.38/0.55    ~spl11_1 | ~spl11_2),
% 1.38/0.55    inference(avatar_split_clause,[],[f67,f111,f107])).
% 1.38/0.55  fof(f67,plain,(
% 1.38/0.55    ~r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,sK6)),
% 1.38/0.55    inference(cnf_transformation,[],[f40])).
% 1.38/0.55  % SZS output end Proof for theBenchmark
% 1.38/0.55  % (29767)------------------------------
% 1.38/0.55  % (29767)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (29767)Termination reason: Refutation
% 1.38/0.55  
% 1.38/0.55  % (29767)Memory used [KB]: 11129
% 1.38/0.55  % (29767)Time elapsed: 0.112 s
% 1.38/0.55  % (29767)------------------------------
% 1.38/0.55  % (29767)------------------------------
% 1.38/0.55  % (29757)Success in time 0.181 s
%------------------------------------------------------------------------------
