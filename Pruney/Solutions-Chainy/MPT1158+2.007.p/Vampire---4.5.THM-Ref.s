%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:04 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  140 (1219 expanded)
%              Number of leaves         :   22 ( 397 expanded)
%              Depth                    :   29
%              Number of atoms          :  659 (10796 expanded)
%              Number of equality atoms :   96 ( 242 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f286,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f97,f120,f124,f239,f285])).

% (7424)Termination reason: Refutation not found, incomplete strategy

% (7424)Memory used [KB]: 1791
% (7424)Time elapsed: 0.152 s
% (7424)------------------------------
% (7424)------------------------------
fof(f285,plain,
    ( ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f284])).

fof(f284,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f283,f53])).

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

% (7422)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
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

% (7436)Termination reason: Refutation not found, incomplete strategy

% (7436)Memory used [KB]: 1663
% (7436)Time elapsed: 0.004 s
% (7436)------------------------------
% (7436)------------------------------
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

% (7431)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% (7422)Refutation not found, incomplete strategy% (7422)------------------------------
% (7422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (7435)Refutation not found, incomplete strategy% (7435)------------------------------
% (7435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).

fof(f283,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f282,f241])).

fof(f241,plain,
    ( ~ sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f240,f203])).

% (7423)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
fof(f203,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),X0) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f201,f182])).

fof(f182,plain,
    ( ! [X4] : sP1(X4,k2_tarski(sK5,sK5),sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f181,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f181,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f180,f49])).

fof(f49,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f180,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f179,f50])).

fof(f50,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f179,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f178,f51])).

fof(f51,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f178,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f171,f52])).

fof(f52,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f171,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3) )
    | ~ spl9_5 ),
    inference(resolution,[],[f72,f154])).

fof(f154,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f153,f48])).

fof(f153,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f152,f49])).

fof(f152,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f151,f52])).

fof(f151,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f146,f54])).

fof(f54,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f146,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ l1_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(superposition,[],[f62,f119])).

fof(f119,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | ~ spl9_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl9_5
  <=> k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f72,plain,(
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
    inference(definition_folding,[],[f23,f25,f24])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f201,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),X0)
        | ~ sP1(X0,k2_tarski(sK5,sK5),sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f65,f196])).

fof(f196,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f195,f48])).

fof(f195,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f194,f49])).

fof(f194,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f193,f50])).

fof(f193,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f192,f51])).

fof(f192,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f185,f52])).

fof(f185,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_5 ),
    inference(resolution,[],[f60,f154])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).

fof(f65,plain,(
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

fof(f240,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | spl9_2
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f95,f119])).

fof(f95,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl9_2
  <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f282,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f280,f90])).

fof(f90,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl9_1
  <=> r2_orders_2(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f280,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_2
    | ~ spl9_5 ),
    inference(superposition,[],[f82,f278])).

fof(f278,plain,
    ( sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f277,f53])).

fof(f277,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f276])).

fof(f276,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f132,f241])).

fof(f132,plain,(
    ! [X6,X4,X7,X5] :
      ( sP0(X4,k2_tarski(X5,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | sK6(X4,k2_tarski(X5,X6),X7) = X5
      | sK6(X4,k2_tarski(X5,X6),X7) = X6 ) ),
    inference(resolution,[],[f83,f128])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f73,f87])).

fof(f87,plain,(
    ! [X0,X1] : sP2(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
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

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f73,plain,(
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
    inference(equality_resolution,[],[f70])).

fof(f70,plain,(
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
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_orders_2(X0,X3,sK6(X0,X1,X3))
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f239,plain,
    ( spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f238])).

fof(f238,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f237,f54])).

fof(f237,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f231,f91])).

fof(f91,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f89])).

fof(f231,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f225,f102])).

fof(f102,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f86,f87])).

fof(f86,plain,(
    ! [X4,X2,X0] :
      ( ~ sP2(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f225,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | r2_orders_2(sK3,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f222,f217])).

fof(f217,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f204,f127])).

fof(f127,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f94,f119])).

fof(f94,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f93])).

fof(f204,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | sP0(sK3,k2_tarski(sK5,sK5),X1) )
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f202,f182])).

fof(f202,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | sP0(sK3,k2_tarski(sK5,sK5),X1)
        | ~ sP1(X1,k2_tarski(sK5,sK5),sK3) )
    | ~ spl9_5 ),
    inference(superposition,[],[f64,f196])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f222,plain,
    ( ! [X1] :
        ( r2_orders_2(sK3,sK4,X1)
        | ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),sK4) )
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(superposition,[],[f68,f220])).

fof(f220,plain,
    ( sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(resolution,[],[f217,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK7(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f68,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X0,sK7(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f124,plain,(
    ~ spl9_3 ),
    inference(avatar_contradiction_clause,[],[f123])).

fof(f123,plain,
    ( $false
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f122,plain,
    ( v2_struct_0(sK3)
    | ~ spl9_3 ),
    inference(subsumption_resolution,[],[f121,f100])).

fof(f100,plain,(
    l1_struct_0(sK3) ),
    inference(resolution,[],[f58,f52])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f121,plain,
    ( ~ l1_struct_0(sK3)
    | v2_struct_0(sK3)
    | ~ spl9_3 ),
    inference(resolution,[],[f110,f59])).

fof(f59,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f110,plain,
    ( v1_xboole_0(u1_struct_0(sK3))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl9_3
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f120,plain,
    ( spl9_3
    | spl9_5 ),
    inference(avatar_split_clause,[],[f105,f117,f108])).

fof(f105,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f81,f54])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f63,f57])).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f63,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

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
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:35:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (7429)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.51  % (7421)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.51  % (7434)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.51  % (7413)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (7410)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (7416)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (7417)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (7411)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (7418)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.53  % (7434)Refutation not found, incomplete strategy% (7434)------------------------------
% 0.21/0.53  % (7434)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (7434)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (7434)Memory used [KB]: 6268
% 0.21/0.53  % (7434)Time elapsed: 0.126 s
% 0.21/0.53  % (7434)------------------------------
% 0.21/0.53  % (7434)------------------------------
% 0.21/0.53  % (7405)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (7436)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (7409)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.54  % (7411)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % (7407)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (7406)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (7414)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (7408)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (7415)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.54  % (7409)Refutation not found, incomplete strategy% (7409)------------------------------
% 0.21/0.54  % (7409)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7435)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.54  % (7416)Refutation not found, incomplete strategy% (7416)------------------------------
% 0.21/0.54  % (7416)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (7416)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (7416)Memory used [KB]: 10746
% 0.21/0.54  % (7416)Time elapsed: 0.137 s
% 0.21/0.54  % (7416)------------------------------
% 0.21/0.54  % (7416)------------------------------
% 0.21/0.54  % (7428)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (7420)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (7432)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (7425)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (7424)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (7427)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (7432)Refutation not found, incomplete strategy% (7432)------------------------------
% 0.21/0.55  % (7432)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7409)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (7409)Memory used [KB]: 1918
% 0.21/0.55  % (7409)Time elapsed: 0.132 s
% 0.21/0.55  % (7409)------------------------------
% 0.21/0.55  % (7409)------------------------------
% 0.21/0.55  % (7426)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.55  % (7419)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (7424)Refutation not found, incomplete strategy% (7424)------------------------------
% 0.21/0.55  % (7424)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7436)Refutation not found, incomplete strategy% (7436)------------------------------
% 0.21/0.55  % (7436)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (7430)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (7432)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7432)Memory used [KB]: 6268
% 0.21/0.56  % (7432)Time elapsed: 0.141 s
% 0.21/0.56  % (7432)------------------------------
% 0.21/0.56  % (7432)------------------------------
% 0.21/0.56  % SZS output start Proof for theBenchmark
% 0.21/0.56  fof(f286,plain,(
% 0.21/0.56    $false),
% 0.21/0.56    inference(avatar_sat_refutation,[],[f96,f97,f120,f124,f239,f285])).
% 0.21/0.56  % (7424)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7424)Memory used [KB]: 1791
% 0.21/0.56  % (7424)Time elapsed: 0.152 s
% 0.21/0.56  % (7424)------------------------------
% 0.21/0.56  % (7424)------------------------------
% 0.21/0.56  fof(f285,plain,(
% 0.21/0.56    ~spl9_1 | spl9_2 | ~spl9_5),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f284])).
% 0.21/0.56  fof(f284,plain,(
% 0.21/0.56    $false | (~spl9_1 | spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f283,f53])).
% 0.21/0.56  fof(f53,plain,(
% 0.21/0.56    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f34,plain,(
% 0.21/0.56    (((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 0.21/0.56  % (7422)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  fof(f31,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  % (7436)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (7436)Memory used [KB]: 1663
% 0.21/0.56  % (7436)Time elapsed: 0.004 s
% 0.21/0.56  % (7436)------------------------------
% 0.21/0.56  % (7436)------------------------------
% 0.21/0.56  fof(f32,plain,(
% 0.21/0.56    ? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f33,plain,(
% 0.21/0.56    ? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) => ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  % (7431)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.56  % (7422)Refutation not found, incomplete strategy% (7422)------------------------------
% 0.21/0.56  % (7422)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7435)Refutation not found, incomplete strategy% (7435)------------------------------
% 0.21/0.56  % (7435)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  fof(f30,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f29])).
% 0.21/0.56  fof(f29,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(nnf_transformation,[],[f12])).
% 0.21/0.56  fof(f12,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f11])).
% 0.21/0.56  fof(f11,plain,(
% 0.21/0.56    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f10])).
% 0.21/0.56  fof(f10,negated_conjecture,(
% 0.21/0.56    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.56    inference(negated_conjecture,[],[f9])).
% 0.21/0.56  fof(f9,conjecture,(
% 0.21/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).
% 0.21/0.56  fof(f283,plain,(
% 0.21/0.56    ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f282,f241])).
% 0.21/0.56  fof(f241,plain,(
% 0.21/0.56    ~sP0(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(resolution,[],[f240,f203])).
% 0.21/0.56  % (7423)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.56  fof(f203,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | ~sP0(sK3,k2_tarski(sK5,sK5),X0)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f201,f182])).
% 0.21/0.56  fof(f182,plain,(
% 0.21/0.56    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f181,f48])).
% 0.21/0.56  fof(f48,plain,(
% 0.21/0.56    ~v2_struct_0(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f181,plain,(
% 0.21/0.56    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | v2_struct_0(sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f180,f49])).
% 0.21/0.56  fof(f49,plain,(
% 0.21/0.56    v3_orders_2(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f180,plain,(
% 0.21/0.56    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f179,f50])).
% 0.21/0.56  fof(f50,plain,(
% 0.21/0.56    v4_orders_2(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f179,plain,(
% 0.21/0.56    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f178,f51])).
% 0.21/0.56  fof(f51,plain,(
% 0.21/0.56    v5_orders_2(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f178,plain,(
% 0.21/0.56    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f171,f52])).
% 0.21/0.56  fof(f52,plain,(
% 0.21/0.56    l1_orders_2(sK3)),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f171,plain,(
% 0.21/0.56    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(resolution,[],[f72,f154])).
% 0.21/0.56  fof(f154,plain,(
% 0.21/0.56    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f153,f48])).
% 0.21/0.56  fof(f153,plain,(
% 0.21/0.56    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | v2_struct_0(sK3) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f152,f49])).
% 0.21/0.56  fof(f152,plain,(
% 0.21/0.56    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f151,f52])).
% 0.21/0.56  fof(f151,plain,(
% 0.21/0.56    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~l1_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f146,f54])).
% 0.21/0.56  fof(f54,plain,(
% 0.21/0.56    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f146,plain,(
% 0.21/0.56    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | ~l1_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~spl9_5),
% 0.21/0.56    inference(superposition,[],[f62,f119])).
% 0.21/0.56  fof(f119,plain,(
% 0.21/0.56    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | ~spl9_5),
% 0.21/0.56    inference(avatar_component_clause,[],[f117])).
% 0.21/0.56  fof(f117,plain,(
% 0.21/0.56    spl9_5 <=> k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.21/0.56  fof(f62,plain,(
% 0.21/0.56    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f19])).
% 0.21/0.56  fof(f19,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f18])).
% 0.21/0.56  fof(f18,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f8])).
% 0.21/0.56  fof(f8,axiom,(
% 0.21/0.56    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
% 0.21/0.56  fof(f72,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP1(X0,X2,X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f26])).
% 0.21/0.56  fof(f26,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.56    inference(definition_folding,[],[f23,f25,f24])).
% 0.21/0.56  fof(f24,plain,(
% 0.21/0.56    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.56  fof(f25,plain,(
% 0.21/0.56    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.56  fof(f23,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.21/0.56    inference(flattening,[],[f22])).
% 0.21/0.56  fof(f22,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.21/0.56    inference(ennf_transformation,[],[f6])).
% 0.21/0.56  fof(f6,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.21/0.56  fof(f201,plain,(
% 0.21/0.56    ( ! [X0] : (r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | ~sP0(sK3,k2_tarski(sK5,sK5),X0) | ~sP1(X0,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(superposition,[],[f65,f196])).
% 0.21/0.56  fof(f196,plain,(
% 0.21/0.56    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f195,f48])).
% 0.21/0.56  fof(f195,plain,(
% 0.21/0.56    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | v2_struct_0(sK3) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f194,f49])).
% 0.21/0.56  fof(f194,plain,(
% 0.21/0.56    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f193,f50])).
% 0.21/0.56  fof(f193,plain,(
% 0.21/0.56    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f192,f51])).
% 0.21/0.56  fof(f192,plain,(
% 0.21/0.56    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f185,f52])).
% 0.21/0.56  fof(f185,plain,(
% 0.21/0.56    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | ~spl9_5),
% 0.21/0.56    inference(resolution,[],[f60,f154])).
% 0.21/0.56  fof(f60,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f17])).
% 0.21/0.56  fof(f17,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f16])).
% 0.21/0.56  fof(f16,plain,(
% 0.21/0.56    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f4])).
% 0.21/0.56  fof(f4,axiom,(
% 0.21/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.21/0.56  fof(f65,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f36,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.21/0.56    inference(rectify,[],[f35])).
% 0.21/0.56  fof(f35,plain,(
% 0.21/0.56    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.21/0.56    inference(nnf_transformation,[],[f25])).
% 0.21/0.56  fof(f240,plain,(
% 0.21/0.56    ~r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(forward_demodulation,[],[f95,f119])).
% 0.21/0.56  fof(f95,plain,(
% 0.21/0.56    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | spl9_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f93])).
% 0.21/0.56  fof(f93,plain,(
% 0.21/0.56    spl9_2 <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.21/0.56  fof(f282,plain,(
% 0.21/0.56    sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f280,f90])).
% 0.21/0.56  fof(f90,plain,(
% 0.21/0.56    r2_orders_2(sK3,sK4,sK5) | ~spl9_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f89])).
% 0.21/0.56  fof(f89,plain,(
% 0.21/0.56    spl9_1 <=> r2_orders_2(sK3,sK4,sK5)),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.21/0.56  fof(f280,plain,(
% 0.21/0.56    ~r2_orders_2(sK3,sK4,sK5) | sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(superposition,[],[f82,f278])).
% 0.21/0.56  fof(f278,plain,(
% 0.21/0.56    sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f277,f53])).
% 0.21/0.56  fof(f277,plain,(
% 0.21/0.56    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(duplicate_literal_removal,[],[f276])).
% 0.21/0.56  fof(f276,plain,(
% 0.21/0.56    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(resolution,[],[f132,f241])).
% 0.21/0.56  fof(f132,plain,(
% 0.21/0.56    ( ! [X6,X4,X7,X5] : (sP0(X4,k2_tarski(X5,X6),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | sK6(X4,k2_tarski(X5,X6),X7) = X5 | sK6(X4,k2_tarski(X5,X6),X7) = X6) )),
% 0.21/0.56    inference(resolution,[],[f83,f128])).
% 0.21/0.56  fof(f128,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.21/0.56    inference(resolution,[],[f73,f87])).
% 0.21/0.56  fof(f87,plain,(
% 0.21/0.56    ( ! [X0,X1] : (sP2(X1,X0,k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(equality_resolution,[],[f79])).
% 0.21/0.56  fof(f79,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f47])).
% 0.21/0.56  fof(f47,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.21/0.56    inference(nnf_transformation,[],[f28])).
% 0.21/0.56  fof(f28,plain,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 0.21/0.56    inference(definition_folding,[],[f1,f27])).
% 0.21/0.56  fof(f27,plain,(
% 0.21/0.56    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.56    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.56  fof(f1,axiom,(
% 0.21/0.56    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.21/0.56  fof(f73,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f46,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).
% 0.21/0.56  fof(f45,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f44,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.21/0.56    inference(rectify,[],[f43])).
% 0.21/0.56  fof(f43,plain,(
% 0.21/0.56    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.21/0.56    inference(flattening,[],[f42])).
% 0.21/0.56  fof(f42,plain,(
% 0.21/0.56    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.21/0.56    inference(nnf_transformation,[],[f27])).
% 0.21/0.56  fof(f83,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.56    inference(equality_resolution,[],[f70])).
% 0.21/0.56  fof(f70,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | r2_hidden(sK6(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f41,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f40,f39])).
% 0.21/0.56  fof(f39,plain,(
% 0.21/0.56    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f40,plain,(
% 0.21/0.56    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 0.21/0.56    introduced(choice_axiom,[])).
% 0.21/0.56  fof(f38,plain,(
% 0.21/0.56    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.21/0.56    inference(rectify,[],[f37])).
% 0.21/0.56  fof(f37,plain,(
% 0.21/0.56    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.21/0.56    inference(nnf_transformation,[],[f24])).
% 0.21/0.56  fof(f82,plain,(
% 0.21/0.56    ( ! [X0,X3,X1] : (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.56    inference(equality_resolution,[],[f71])).
% 0.21/0.56  fof(f71,plain,(
% 0.21/0.56    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | ~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f239,plain,(
% 0.21/0.56    spl9_1 | ~spl9_2 | ~spl9_5),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f238])).
% 0.21/0.56  fof(f238,plain,(
% 0.21/0.56    $false | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f237,f54])).
% 0.21/0.56  fof(f237,plain,(
% 0.21/0.56    ~m1_subset_1(sK5,u1_struct_0(sK3)) | (spl9_1 | ~spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f231,f91])).
% 0.21/0.56  fof(f91,plain,(
% 0.21/0.56    ~r2_orders_2(sK3,sK4,sK5) | spl9_1),
% 0.21/0.56    inference(avatar_component_clause,[],[f89])).
% 0.21/0.56  fof(f231,plain,(
% 0.21/0.56    r2_orders_2(sK3,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(resolution,[],[f225,f102])).
% 0.21/0.56  fof(f102,plain,(
% 0.21/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.21/0.56    inference(resolution,[],[f86,f87])).
% 0.21/0.56  fof(f86,plain,(
% 0.21/0.56    ( ! [X4,X2,X0] : (~sP2(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.21/0.56    inference(equality_resolution,[],[f74])).
% 0.21/0.56  fof(f74,plain,(
% 0.21/0.56    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP2(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f46])).
% 0.21/0.56  fof(f225,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK5,sK5)) | r2_orders_2(sK3,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | (~spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(subsumption_resolution,[],[f222,f217])).
% 0.21/0.56  fof(f217,plain,(
% 0.21/0.56    sP0(sK3,k2_tarski(sK5,sK5),sK4) | (~spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(resolution,[],[f204,f127])).
% 0.21/0.56  fof(f127,plain,(
% 0.21/0.56    r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (~spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(backward_demodulation,[],[f94,f119])).
% 0.21/0.56  fof(f94,plain,(
% 0.21/0.56    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~spl9_2),
% 0.21/0.56    inference(avatar_component_clause,[],[f93])).
% 0.21/0.56  fof(f204,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | sP0(sK3,k2_tarski(sK5,sK5),X1)) ) | ~spl9_5),
% 0.21/0.56    inference(subsumption_resolution,[],[f202,f182])).
% 0.21/0.56  fof(f202,plain,(
% 0.21/0.56    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | sP0(sK3,k2_tarski(sK5,sK5),X1) | ~sP1(X1,k2_tarski(sK5,sK5),sK3)) ) | ~spl9_5),
% 0.21/0.56    inference(superposition,[],[f64,f196])).
% 0.21/0.56  fof(f64,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f36])).
% 0.21/0.56  fof(f222,plain,(
% 0.21/0.56    ( ! [X1] : (r2_orders_2(sK3,sK4,X1) | ~r2_hidden(X1,k2_tarski(sK5,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~sP0(sK3,k2_tarski(sK5,sK5),sK4)) ) | (~spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(superposition,[],[f68,f220])).
% 0.21/0.56  fof(f220,plain,(
% 0.21/0.56    sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4) | (~spl9_2 | ~spl9_5)),
% 0.21/0.56    inference(resolution,[],[f217,f67])).
% 0.21/0.56  fof(f67,plain,(
% 0.21/0.56    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK7(X0,X1,X2) = X2) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f68,plain,(
% 0.21/0.56    ( ! [X6,X2,X0,X1] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f41])).
% 0.21/0.56  fof(f124,plain,(
% 0.21/0.56    ~spl9_3),
% 0.21/0.56    inference(avatar_contradiction_clause,[],[f123])).
% 0.21/0.56  fof(f123,plain,(
% 0.21/0.56    $false | ~spl9_3),
% 0.21/0.56    inference(subsumption_resolution,[],[f122,f48])).
% 0.21/0.56  fof(f122,plain,(
% 0.21/0.56    v2_struct_0(sK3) | ~spl9_3),
% 0.21/0.56    inference(subsumption_resolution,[],[f121,f100])).
% 0.21/0.56  fof(f100,plain,(
% 0.21/0.56    l1_struct_0(sK3)),
% 0.21/0.56    inference(resolution,[],[f58,f52])).
% 0.21/0.56  fof(f58,plain,(
% 0.21/0.56    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f13])).
% 0.21/0.56  fof(f13,plain,(
% 0.21/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.21/0.56    inference(ennf_transformation,[],[f5])).
% 0.21/0.56  fof(f5,axiom,(
% 0.21/0.56    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.21/0.56  fof(f121,plain,(
% 0.21/0.56    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl9_3),
% 0.21/0.56    inference(resolution,[],[f110,f59])).
% 0.21/0.56  fof(f59,plain,(
% 0.21/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f15])).
% 0.21/0.56  fof(f15,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.56    inference(flattening,[],[f14])).
% 0.21/0.56  fof(f14,plain,(
% 0.21/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f3])).
% 0.21/0.56  fof(f3,axiom,(
% 0.21/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.56  fof(f110,plain,(
% 0.21/0.56    v1_xboole_0(u1_struct_0(sK3)) | ~spl9_3),
% 0.21/0.56    inference(avatar_component_clause,[],[f108])).
% 0.21/0.56  fof(f108,plain,(
% 0.21/0.56    spl9_3 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.56    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.21/0.56  fof(f120,plain,(
% 0.21/0.56    spl9_3 | spl9_5),
% 0.21/0.56    inference(avatar_split_clause,[],[f105,f117,f108])).
% 0.21/0.56  fof(f105,plain,(
% 0.21/0.56    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | v1_xboole_0(u1_struct_0(sK3))),
% 0.21/0.56    inference(resolution,[],[f81,f54])).
% 0.21/0.56  fof(f81,plain,(
% 0.21/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(definition_unfolding,[],[f63,f57])).
% 0.21/0.56  fof(f57,plain,(
% 0.21/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f2])).
% 0.21/0.56  fof(f2,axiom,(
% 0.21/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.21/0.56  fof(f63,plain,(
% 0.21/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.21/0.56    inference(cnf_transformation,[],[f21])).
% 0.21/0.56  fof(f21,plain,(
% 0.21/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.56    inference(flattening,[],[f20])).
% 0.21/0.56  fof(f20,plain,(
% 0.21/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.56    inference(ennf_transformation,[],[f7])).
% 0.21/0.56  fof(f7,axiom,(
% 0.21/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.56  fof(f97,plain,(
% 0.21/0.56    spl9_1 | spl9_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f55,f93,f89])).
% 0.21/0.56  fof(f55,plain,(
% 0.21/0.56    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  fof(f96,plain,(
% 0.21/0.56    ~spl9_1 | ~spl9_2),
% 0.21/0.56    inference(avatar_split_clause,[],[f56,f93,f89])).
% 0.21/0.56  fof(f56,plain,(
% 0.21/0.56    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)),
% 0.21/0.56    inference(cnf_transformation,[],[f34])).
% 0.21/0.56  % SZS output end Proof for theBenchmark
% 0.21/0.56  % (7411)------------------------------
% 0.21/0.56  % (7411)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (7411)Termination reason: Refutation
% 0.21/0.56  
% 0.21/0.56  % (7411)Memory used [KB]: 10874
% 0.21/0.56  % (7411)Time elapsed: 0.132 s
% 0.21/0.56  % (7411)------------------------------
% 0.21/0.56  % (7411)------------------------------
% 0.21/0.56  % (7435)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  % (7402)Success in time 0.2 s
%------------------------------------------------------------------------------
