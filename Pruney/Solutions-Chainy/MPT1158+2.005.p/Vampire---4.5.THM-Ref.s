%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 955 expanded)
%              Number of leaves         :   22 ( 309 expanded)
%              Depth                    :   27
%              Number of atoms          :  673 (7999 expanded)
%              Number of equality atoms :   96 ( 242 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f260,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f95,f96,f120,f124,f227,f259])).

fof(f259,plain,
    ( ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f258])).

fof(f258,plain,
    ( $false
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f257,f53])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).

fof(f257,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f256,f229])).

fof(f229,plain,
    ( ~ sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f228,f188])).

fof(f188,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),X0) )
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f186,f166])).

fof(f166,plain,
    ( ! [X4] : sP1(X4,k2_tarski(sK5,sK5),sK3)
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f165,f48])).

fof(f48,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f165,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | v2_struct_0(sK3) )
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f164,f49])).

fof(f49,plain,(
    v3_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f164,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3) )
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f163,f50])).

fof(f50,plain,(
    v4_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f163,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3) )
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f162,f51])).

fof(f51,plain,(
    v5_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f162,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3) )
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f156,f52])).

fof(f52,plain,(
    l1_orders_2(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f156,plain,
    ( ! [X4] :
        ( sP1(X4,k2_tarski(sK5,sK5),sK3)
        | ~ l1_orders_2(sK3)
        | ~ v5_orders_2(sK3)
        | ~ v4_orders_2(sK3)
        | ~ v3_orders_2(sK3)
        | v2_struct_0(sK3) )
    | spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f71,f141])).

fof(f141,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f140,f109])).

fof(f109,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK3))
    | spl9_3 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl9_3
  <=> v1_xboole_0(u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f140,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v1_xboole_0(u1_struct_0(sK3))
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f139,f54])).

fof(f54,plain,(
    m1_subset_1(sK5,u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f34])).

fof(f139,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | v1_xboole_0(u1_struct_0(sK3))
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

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
    inference(ennf_transformation,[],[f7])).

% (18812)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).

fof(f186,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),X0)
        | ~ sP1(X0,k2_tarski(sK5,sK5),sK3) )
    | spl9_3
    | ~ spl9_5 ),
    inference(superposition,[],[f64,f179])).

fof(f179,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f178,f48])).

fof(f178,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | v2_struct_0(sK3)
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f177,f49])).

fof(f177,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f176,f50])).

fof(f176,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f175,f51])).

fof(f175,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f169,f52])).

fof(f169,plain,
    ( k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5))
    | ~ l1_orders_2(sK3)
    | ~ v5_orders_2(sK3)
    | ~ v4_orders_2(sK3)
    | ~ v3_orders_2(sK3)
    | v2_struct_0(sK3)
    | spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f60,f141])).

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

fof(f228,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | spl9_2
    | ~ spl9_5 ),
    inference(forward_demodulation,[],[f94,f119])).

fof(f94,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | spl9_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl9_2
  <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f256,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | ~ spl9_1
    | spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f254,f89])).

fof(f89,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ spl9_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl9_1
  <=> r2_orders_2(sK3,sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f254,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(superposition,[],[f81,f252])).

% (18804)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
fof(f252,plain,
    ( sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f251,f53])).

fof(f251,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(duplicate_literal_removal,[],[f250])).

fof(f250,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK3))
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4)
    | spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f149,f229])).

fof(f149,plain,(
    ! [X6,X4,X7,X5] :
      ( sP0(X4,k2_tarski(X5,X6),X7)
      | ~ m1_subset_1(X7,u1_struct_0(X4))
      | sK6(X4,k2_tarski(X5,X6),X7) = X5
      | sK6(X4,k2_tarski(X5,X6),X7) = X6 ) ),
    inference(resolution,[],[f82,f145])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f72,f86])).

fof(f86,plain,(
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

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

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

fof(f82,plain,(
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

fof(f81,plain,(
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

fof(f227,plain,
    ( spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f225,f54])).

fof(f225,plain,
    ( ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | spl9_1
    | ~ spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f219,f90])).

fof(f90,plain,
    ( ~ r2_orders_2(sK3,sK4,sK5)
    | spl9_1 ),
    inference(avatar_component_clause,[],[f88])).

fof(f219,plain,
    ( r2_orders_2(sK3,sK4,sK5)
    | ~ m1_subset_1(sK5,u1_struct_0(sK3))
    | ~ spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f215,f101])).

fof(f101,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f85,f86])).

fof(f85,plain,(
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

fof(f215,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | r2_orders_2(sK3,sK4,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK3)) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f212,f199])).

fof(f199,plain,
    ( sP0(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f189,f138])).

fof(f138,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
    | ~ spl9_2
    | ~ spl9_5 ),
    inference(backward_demodulation,[],[f93,f119])).

fof(f93,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f92])).

fof(f189,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | sP0(sK3,k2_tarski(sK5,sK5),X1) )
    | spl9_3
    | ~ spl9_5 ),
    inference(subsumption_resolution,[],[f187,f166])).

fof(f187,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5)))
        | sP0(sK3,k2_tarski(sK5,sK5),X1)
        | ~ sP1(X1,k2_tarski(sK5,sK5),sK3) )
    | spl9_3
    | ~ spl9_5 ),
    inference(superposition,[],[f63,f179])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_1_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f212,plain,
    ( ! [X1] :
        ( r2_orders_2(sK3,sK4,X1)
        | ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK3))
        | ~ sP0(sK3,k2_tarski(sK5,sK5),sK4) )
    | ~ spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(superposition,[],[f67,f203])).

fof(f203,plain,
    ( sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4)
    | ~ spl9_2
    | spl9_3
    | ~ spl9_5 ),
    inference(resolution,[],[f199,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK7(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f41])).

% (18789)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
fof(f67,plain,(
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
    inference(subsumption_resolution,[],[f121,f99])).

fof(f99,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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

% (18792)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
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

fof(f120,plain,
    ( spl9_3
    | spl9_5 ),
    inference(avatar_split_clause,[],[f104,f117,f108])).

fof(f104,plain,
    ( k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK3)) ),
    inference(resolution,[],[f80,f54])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f61,f57])).

fof(f57,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f96,plain,
    ( spl9_1
    | spl9_2 ),
    inference(avatar_split_clause,[],[f55,f92,f88])).

fof(f55,plain,
    ( r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,
    ( ~ spl9_1
    | ~ spl9_2 ),
    inference(avatar_split_clause,[],[f56,f92,f88])).

fof(f56,plain,
    ( ~ r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))
    | ~ r2_orders_2(sK3,sK4,sK5) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n008.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:07:00 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.49  % (18803)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.50  % (18811)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.51  % (18795)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (18790)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (18795)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (18794)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % SZS output start Proof for theBenchmark
% 0.22/0.52  fof(f260,plain,(
% 0.22/0.52    $false),
% 0.22/0.52    inference(avatar_sat_refutation,[],[f95,f96,f120,f124,f227,f259])).
% 0.22/0.52  fof(f259,plain,(
% 0.22/0.52    ~spl9_1 | spl9_2 | spl9_3 | ~spl9_5),
% 0.22/0.52    inference(avatar_contradiction_clause,[],[f258])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    $false | (~spl9_1 | spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f257,f53])).
% 0.22/0.52  fof(f53,plain,(
% 0.22/0.52    m1_subset_1(sK4,u1_struct_0(sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    (((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5])],[f30,f33,f32,f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) & l1_orders_2(sK3) & v5_orders_2(sK3) & v4_orders_2(sK3) & v3_orders_2(sK3) & ~v2_struct_0(sK3))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,X1,X2)) & (r2_hidden(X1,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(X1,u1_struct_0(sK3))) => (? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) & m1_subset_1(sK4,u1_struct_0(sK3)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ? [X2] : ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | ~r2_orders_2(sK3,sK4,X2)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),X2))) | r2_orders_2(sK3,sK4,X2)) & m1_subset_1(X2,u1_struct_0(sK3))) => ((~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)) & (r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)) & m1_subset_1(sK5,u1_struct_0(sK3)))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f11])).
% 0.22/0.52  fof(f11,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f10])).
% 0.22/0.52  fof(f10,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.52    inference(negated_conjecture,[],[f9])).
% 0.22/0.52  fof(f9,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_orders_2)).
% 0.22/0.52  fof(f257,plain,(
% 0.22/0.52    ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f256,f229])).
% 0.22/0.52  fof(f229,plain,(
% 0.22/0.52    ~sP0(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(resolution,[],[f228,f188])).
% 0.22/0.52  fof(f188,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | ~sP0(sK3,k2_tarski(sK5,sK5),X0)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f186,f166])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f165,f48])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    ~v2_struct_0(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | v2_struct_0(sK3)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f164,f49])).
% 0.22/0.52  fof(f49,plain,(
% 0.22/0.52    v3_orders_2(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f163,f50])).
% 0.22/0.52  fof(f50,plain,(
% 0.22/0.52    v4_orders_2(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f162,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    v5_orders_2(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f156,f52])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    l1_orders_2(sK3)),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f156,plain,(
% 0.22/0.52    ( ! [X4] : (sP1(X4,k2_tarski(sK5,sK5),sK3) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(resolution,[],[f71,f141])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f140,f109])).
% 0.22/0.52  fof(f109,plain,(
% 0.22/0.52    ~v1_xboole_0(u1_struct_0(sK3)) | spl9_3),
% 0.22/0.52    inference(avatar_component_clause,[],[f108])).
% 0.22/0.52  fof(f108,plain,(
% 0.22/0.52    spl9_3 <=> v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | v1_xboole_0(u1_struct_0(sK3)) | ~spl9_5),
% 0.22/0.52    inference(subsumption_resolution,[],[f139,f54])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    m1_subset_1(sK5,u1_struct_0(sK3))),
% 0.22/0.52    inference(cnf_transformation,[],[f34])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK3))) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | v1_xboole_0(u1_struct_0(sK3)) | ~spl9_5),
% 0.22/0.52    inference(superposition,[],[f62,f119])).
% 0.22/0.52  fof(f119,plain,(
% 0.22/0.52    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | ~spl9_5),
% 0.22/0.52    inference(avatar_component_clause,[],[f117])).
% 0.22/0.52  fof(f117,plain,(
% 0.22/0.52    spl9_5 <=> k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.22/0.52  fof(f62,plain,(
% 0.22/0.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.52    inference(flattening,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.52  fof(f71,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP1(X0,X2,X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.52    inference(definition_folding,[],[f23,f25,f24])).
% 0.22/0.52  fof(f24,plain,(
% 0.22/0.52    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 0.22/0.52    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.52  fof(f23,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.52    inference(flattening,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  % (18812)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_1_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X3,X4))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fraenkel_a_2_1_orders_2)).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    ( ! [X0] : (r2_hidden(X0,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | ~sP0(sK3,k2_tarski(sK5,sK5),X0) | ~sP1(X0,k2_tarski(sK5,sK5),sK3)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(superposition,[],[f64,f179])).
% 0.22/0.52  fof(f179,plain,(
% 0.22/0.52    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f178,f48])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | v2_struct_0(sK3) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f177,f49])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f176,f50])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f175,f51])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f169,f52])).
% 0.22/0.52  fof(f169,plain,(
% 0.22/0.52    k2_orders_2(sK3,k2_tarski(sK5,sK5)) = a_2_1_orders_2(sK3,k2_tarski(sK5,sK5)) | ~l1_orders_2(sK3) | ~v5_orders_2(sK3) | ~v4_orders_2(sK3) | ~v3_orders_2(sK3) | v2_struct_0(sK3) | (spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(resolution,[],[f60,f141])).
% 0.22/0.52  fof(f60,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f17])).
% 0.22/0.52  fof(f17,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d13_orders_2)).
% 0.22/0.52  fof(f64,plain,(
% 0.22/0.52    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f36])).
% 0.22/0.52  fof(f36,plain,(
% 0.22/0.52    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_1_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_1_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 0.22/0.52    inference(rectify,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_1_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_1_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 0.22/0.52    inference(nnf_transformation,[],[f25])).
% 0.22/0.52  fof(f228,plain,(
% 0.22/0.52    ~r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (spl9_2 | ~spl9_5)),
% 0.22/0.52    inference(forward_demodulation,[],[f94,f119])).
% 0.22/0.52  fof(f94,plain,(
% 0.22/0.52    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | spl9_2),
% 0.22/0.52    inference(avatar_component_clause,[],[f92])).
% 0.22/0.52  fof(f92,plain,(
% 0.22/0.52    spl9_2 <=> r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.22/0.52  fof(f256,plain,(
% 0.22/0.52    sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (~spl9_1 | spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(subsumption_resolution,[],[f254,f89])).
% 0.22/0.52  fof(f89,plain,(
% 0.22/0.52    r2_orders_2(sK3,sK4,sK5) | ~spl9_1),
% 0.22/0.52    inference(avatar_component_clause,[],[f88])).
% 0.22/0.52  fof(f88,plain,(
% 0.22/0.52    spl9_1 <=> r2_orders_2(sK3,sK4,sK5)),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    ~r2_orders_2(sK3,sK4,sK5) | sP0(sK3,k2_tarski(sK5,sK5),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK3)) | (spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.52    inference(superposition,[],[f81,f252])).
% 0.22/0.53  % (18804)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.53  fof(f252,plain,(
% 0.22/0.53    sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f251,f53])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f250])).
% 0.22/0.53  fof(f250,plain,(
% 0.22/0.53    ~m1_subset_1(sK4,u1_struct_0(sK3)) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | sK5 = sK6(sK3,k2_tarski(sK5,sK5),sK4) | (spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(resolution,[],[f149,f229])).
% 0.22/0.53  fof(f149,plain,(
% 0.22/0.53    ( ! [X6,X4,X7,X5] : (sP0(X4,k2_tarski(X5,X6),X7) | ~m1_subset_1(X7,u1_struct_0(X4)) | sK6(X4,k2_tarski(X5,X6),X7) = X5 | sK6(X4,k2_tarski(X5,X6),X7) = X6) )),
% 0.22/0.53    inference(resolution,[],[f82,f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.22/0.53    inference(resolution,[],[f72,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    ( ! [X0,X1] : (sP2(X1,X0,k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(equality_resolution,[],[f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP2(X1,X0,X2)) & (sP2(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.22/0.53    inference(nnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP2(X1,X0,X2))),
% 0.22/0.53    inference(definition_folding,[],[f1,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ! [X1,X0,X2] : (sP2(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (~sP2(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8])],[f44,f45])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK8(X0,X1,X2) != X0 & sK8(X0,X1,X2) != X1) | ~r2_hidden(sK8(X0,X1,X2),X2)) & (sK8(X0,X1,X2) = X0 | sK8(X0,X1,X2) = X1 | r2_hidden(sK8(X0,X1,X2),X2))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP2(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP2(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.22/0.53    inference(flattening,[],[f42])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ! [X1,X0,X2] : ((sP2(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP2(X1,X0,X2)))),
% 0.22/0.53    inference(nnf_transformation,[],[f27])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f69])).
% 0.22/0.53  fof(f69,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | r2_hidden(sK6(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f38,f40,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f40,plain,(
% 0.22/0.53    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.53    introduced(choice_axiom,[])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X3,X4) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X5,X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 0.22/0.53    inference(rectify,[],[f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X3,X4) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X3,X4) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 0.22/0.53    inference(nnf_transformation,[],[f24])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0,X3,X1] : (~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(equality_resolution,[],[f70])).
% 0.22/0.53  fof(f70,plain,(
% 0.22/0.53    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | ~r2_orders_2(X0,X3,sK6(X0,X1,X3)) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f227,plain,(
% 0.22/0.53    spl9_1 | ~spl9_2 | spl9_3 | ~spl9_5),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f226])).
% 0.22/0.53  fof(f226,plain,(
% 0.22/0.53    $false | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f225,f54])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    ~m1_subset_1(sK5,u1_struct_0(sK3)) | (spl9_1 | ~spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f219,f90])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ~r2_orders_2(sK3,sK4,sK5) | spl9_1),
% 0.22/0.53    inference(avatar_component_clause,[],[f88])).
% 0.22/0.53  fof(f219,plain,(
% 0.22/0.53    r2_orders_2(sK3,sK4,sK5) | ~m1_subset_1(sK5,u1_struct_0(sK3)) | (~spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(resolution,[],[f215,f101])).
% 0.22/0.53  fof(f101,plain,(
% 0.22/0.53    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.22/0.53    inference(resolution,[],[f85,f86])).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ( ! [X4,X2,X0] : (~sP2(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.22/0.53    inference(equality_resolution,[],[f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP2(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f46])).
% 0.22/0.53  fof(f215,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK5,sK5)) | r2_orders_2(sK3,sK4,X1) | ~m1_subset_1(X1,u1_struct_0(sK3))) ) | (~spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f212,f199])).
% 0.22/0.53  fof(f199,plain,(
% 0.22/0.53    sP0(sK3,k2_tarski(sK5,sK5),sK4) | (~spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(resolution,[],[f189,f138])).
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    r2_hidden(sK4,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | (~spl9_2 | ~spl9_5)),
% 0.22/0.53    inference(backward_demodulation,[],[f93,f119])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~spl9_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f92])).
% 0.22/0.53  fof(f189,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | sP0(sK3,k2_tarski(sK5,sK5),X1)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(subsumption_resolution,[],[f187,f166])).
% 0.22/0.53  fof(f187,plain,(
% 0.22/0.53    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK3,k2_tarski(sK5,sK5))) | sP0(sK3,k2_tarski(sK5,sK5),X1) | ~sP1(X1,k2_tarski(sK5,sK5),sK3)) ) | (spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(superposition,[],[f63,f179])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_1_orders_2(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f36])).
% 0.22/0.53  fof(f212,plain,(
% 0.22/0.53    ( ! [X1] : (r2_orders_2(sK3,sK4,X1) | ~r2_hidden(X1,k2_tarski(sK5,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK3)) | ~sP0(sK3,k2_tarski(sK5,sK5),sK4)) ) | (~spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(superposition,[],[f67,f203])).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    sK4 = sK7(sK3,k2_tarski(sK5,sK5),sK4) | (~spl9_2 | spl9_3 | ~spl9_5)),
% 0.22/0.53    inference(resolution,[],[f199,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK7(X0,X1,X2) = X2) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  % (18789)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    ( ! [X6,X2,X0,X1] : (r2_orders_2(X0,sK7(X0,X1,X2),X6) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f41])).
% 0.22/0.53  fof(f124,plain,(
% 0.22/0.53    ~spl9_3),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f123])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    $false | ~spl9_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f122,f48])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    v2_struct_0(sK3) | ~spl9_3),
% 0.22/0.53    inference(subsumption_resolution,[],[f121,f99])).
% 0.22/0.53  fof(f99,plain,(
% 0.22/0.53    l1_struct_0(sK3)),
% 0.22/0.53    inference(resolution,[],[f58,f52])).
% 0.22/0.53  fof(f58,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.22/0.53  fof(f121,plain,(
% 0.22/0.53    ~l1_struct_0(sK3) | v2_struct_0(sK3) | ~spl9_3),
% 0.22/0.53    inference(resolution,[],[f110,f59])).
% 0.22/0.53  fof(f59,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  % (18792)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    v1_xboole_0(u1_struct_0(sK3)) | ~spl9_3),
% 0.22/0.53    inference(avatar_component_clause,[],[f108])).
% 0.22/0.53  fof(f120,plain,(
% 0.22/0.53    spl9_3 | spl9_5),
% 0.22/0.53    inference(avatar_split_clause,[],[f104,f117,f108])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    k6_domain_1(u1_struct_0(sK3),sK5) = k2_tarski(sK5,sK5) | v1_xboole_0(u1_struct_0(sK3))),
% 0.22/0.53    inference(resolution,[],[f80,f54])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(definition_unfolding,[],[f61,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.53  fof(f96,plain,(
% 0.22/0.53    spl9_1 | spl9_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f55,f92,f88])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | r2_orders_2(sK3,sK4,sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  fof(f95,plain,(
% 0.22/0.53    ~spl9_1 | ~spl9_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f56,f92,f88])).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ~r2_hidden(sK4,k2_orders_2(sK3,k6_domain_1(u1_struct_0(sK3),sK5))) | ~r2_orders_2(sK3,sK4,sK5)),
% 0.22/0.53    inference(cnf_transformation,[],[f34])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (18795)------------------------------
% 0.22/0.53  % (18795)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (18795)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (18795)Memory used [KB]: 10874
% 0.22/0.53  % (18795)Time elapsed: 0.115 s
% 0.22/0.53  % (18795)------------------------------
% 0.22/0.53  % (18795)------------------------------
% 0.22/0.53  % (18806)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.53  % (18796)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.53  % (18788)Success in time 0.171 s
%------------------------------------------------------------------------------
