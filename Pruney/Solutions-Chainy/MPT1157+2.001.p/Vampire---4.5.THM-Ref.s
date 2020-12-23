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

% Result     : Theorem 0.22s
% Output     : Refutation 1.26s
% Verified   : 
% Statistics : Number of formulae       :  134 ( 946 expanded)
%              Number of leaves         :   21 ( 307 expanded)
%              Depth                    :   26
%              Number of atoms          :  626 (7904 expanded)
%              Number of equality atoms :   73 ( 194 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f318,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f94,f95,f112,f121,f299,f317])).

fof(f317,plain,
    ( ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f316])).

fof(f316,plain,
    ( $false
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f315,f52])).

fof(f52,plain,(
    m1_subset_1(sK4,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( ~ r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
      | ~ r2_orders_2(sK2,sK3,sK4) )
    & ( r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
      | r2_orders_2(sK2,sK3,sK4) )
    & m1_subset_1(sK4,u1_struct_0(sK2))
    & m1_subset_1(sK3,u1_struct_0(sK2))
    & l1_orders_2(sK2)
    & v5_orders_2(sK2)
    & v4_orders_2(sK2)
    & v3_orders_2(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).

fof(f31,plain,
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
              ( ( ~ r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
                | ~ r2_orders_2(sK2,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
                | r2_orders_2(sK2,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK2)) )
          & m1_subset_1(X1,u1_struct_0(sK2)) )
      & l1_orders_2(sK2)
      & v5_orders_2(sK2)
      & v4_orders_2(sK2)
      & v3_orders_2(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( ~ r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
              | ~ r2_orders_2(sK2,X1,X2) )
            & ( r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1)))
              | r2_orders_2(sK2,X1,X2) )
            & m1_subset_1(X2,u1_struct_0(sK2)) )
        & m1_subset_1(X1,u1_struct_0(sK2)) )
   => ( ? [X2] :
          ( ( ~ r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
            | ~ r2_orders_2(sK2,sK3,X2) )
          & ( r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
            | r2_orders_2(sK2,sK3,X2) )
          & m1_subset_1(X2,u1_struct_0(sK2)) )
      & m1_subset_1(sK3,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ( ~ r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
          | ~ r2_orders_2(sK2,sK3,X2) )
        & ( r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
          | r2_orders_2(sK2,sK3,X2) )
        & m1_subset_1(X2,u1_struct_0(sK2)) )
   => ( ( ~ r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
        | ~ r2_orders_2(sK2,sK3,sK4) )
      & ( r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
        | r2_orders_2(sK2,sK3,sK4) )
      & m1_subset_1(sK4,u1_struct_0(sK2)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).

fof(f315,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f314,f301])).

fof(f301,plain,
    ( ~ sP0(sK2,k2_tarski(sK3,sK3),sK4)
    | spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f300,f185])).

fof(f185,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_orders_2(sK2,k2_tarski(sK3,sK3)))
        | ~ sP0(sK2,k2_tarski(sK3,sK3),X0) )
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f183,f163])).

fof(f163,plain,
    ( ! [X3] : sP1(X3,k2_tarski(sK3,sK3),sK2)
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f162,f46])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f162,plain,
    ( ! [X3] :
        ( sP1(X3,k2_tarski(sK3,sK3),sK2)
        | v2_struct_0(sK2) )
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f161,f47])).

fof(f47,plain,(
    v3_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f161,plain,
    ( ! [X3] :
        ( sP1(X3,k2_tarski(sK3,sK3),sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f160,f48])).

fof(f48,plain,(
    v4_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f160,plain,
    ( ! [X3] :
        ( sP1(X3,k2_tarski(sK3,sK3),sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f159,f49])).

fof(f49,plain,(
    v5_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f159,plain,
    ( ! [X3] :
        ( sP1(X3,k2_tarski(sK3,sK3),sK2)
        | ~ v5_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f157,f50])).

fof(f50,plain,(
    l1_orders_2(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f157,plain,
    ( ! [X3] :
        ( sP1(X3,k2_tarski(sK3,sK3),sK2)
        | ~ l1_orders_2(sK2)
        | ~ v5_orders_2(sK2)
        | ~ v4_orders_2(sK2)
        | ~ v3_orders_2(sK2)
        | v2_struct_0(sK2) )
    | spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f73,f125])).

fof(f125,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f124,f106])).

fof(f106,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2))
    | spl8_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl8_3
  <=> v1_xboole_0(u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f124,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f123,f51])).

fof(f51,plain,(
    m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f34])).

fof(f123,plain,
    ( m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_4 ),
    inference(superposition,[],[f60,f111])).

fof(f111,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl8_4
  <=> k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP1(X0,X2,X1)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f24,f27,f26])).

fof(f26,plain,(
    ! [X1,X2,X0] :
      ( sP0(X1,X2,X0)
    <=> ? [X3] :
          ( ! [X4] :
              ( r2_orders_2(X1,X4,X3)
              | ~ r2_hidden(X4,X2)
              | ~ m1_subset_1(X4,u1_struct_0(X1)) )
          & X0 = X3
          & m1_subset_1(X3,u1_struct_0(X1)) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> sP0(X1,X2,X0) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f183,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_orders_2(sK2,k2_tarski(sK3,sK3)))
        | ~ sP0(sK2,k2_tarski(sK3,sK3),X0)
        | ~ sP1(X0,k2_tarski(sK3,sK3),sK2) )
    | spl8_3
    | ~ spl8_4 ),
    inference(superposition,[],[f66,f177])).

fof(f177,plain,
    ( k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3))
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f176,f46])).

fof(f176,plain,
    ( k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3))
    | v2_struct_0(sK2)
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f175,f47])).

fof(f175,plain,
    ( k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3))
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f174,f48])).

fof(f174,plain,
    ( k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3))
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f173,f49])).

fof(f173,plain,
    ( k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3))
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f171,f50])).

fof(f171,plain,
    ( k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3))
    | ~ l1_orders_2(sK2)
    | ~ v5_orders_2(sK2)
    | ~ v4_orders_2(sK2)
    | ~ v3_orders_2(sK2)
    | v2_struct_0(sK2)
    | spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f58,f125])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
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
         => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | ~ sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
          | ~ sP0(X2,X1,X0) )
        & ( sP0(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ~ sP0(X1,X2,X0) )
        & ( sP0(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f300,plain,
    ( ~ r2_hidden(sK4,k1_orders_2(sK2,k2_tarski(sK3,sK3)))
    | spl8_2
    | ~ spl8_4 ),
    inference(forward_demodulation,[],[f93,f111])).

fof(f93,plain,
    ( ~ r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
    | spl8_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl8_2
  <=> r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f314,plain,
    ( sP0(sK2,k2_tarski(sK3,sK3),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | ~ spl8_1
    | spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f312,f88])).

fof(f88,plain,
    ( r2_orders_2(sK2,sK3,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f87,plain,
    ( spl8_1
  <=> r2_orders_2(sK2,sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f312,plain,
    ( ~ r2_orders_2(sK2,sK3,sK4)
    | sP0(sK2,k2_tarski(sK3,sK3),sK4)
    | ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(superposition,[],[f83,f308])).

fof(f308,plain,
    ( sK3 = sK6(sK2,k2_tarski(sK3,sK3),sK4)
    | spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f305,f52])).

fof(f305,plain,
    ( ~ m1_subset_1(sK4,u1_struct_0(sK2))
    | sK3 = sK6(sK2,k2_tarski(sK3,sK3),sK4)
    | spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f301,f146])).

fof(f146,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,k2_tarski(X1,X1),X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | sK6(X0,k2_tarski(X1,X1),X2) = X1 ) ),
    inference(resolution,[],[f84,f82])).

fof(f82,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k2_tarski(X0,X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f61,f55])).

fof(f55,plain,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
        | ( ( sK5(X0,X1) != X0
            | ~ r2_hidden(sK5(X0,X1),X1) )
          & ( sK5(X0,X1) = X0
            | r2_hidden(sK5(X0,X1),X1) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X1)
              | X0 != X3 )
            & ( X0 = X3
              | ~ r2_hidden(X3,X1) ) )
        | k1_tarski(X0) != X1 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( X0 != X2
            | ~ r2_hidden(X2,X1) )
          & ( X0 = X2
            | r2_hidden(X2,X1) ) )
     => ( ( sK5(X0,X1) != X0
          | ~ r2_hidden(sK5(X0,X1),X1) )
        & ( sK5(X0,X1) = X0
          | r2_hidden(sK5(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( k1_tarski(X0) = X1
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
        | k1_tarski(X0) != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f84,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK6(X0,X1,X3),X1)
      | sP0(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | r2_hidden(sK6(X0,X1,X3),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ! [X3] :
            ( ( ~ r2_orders_2(X0,sK6(X0,X1,X3),X3)
              & r2_hidden(sK6(X0,X1,X3),X1)
              & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) )
            | X2 != X3
            | ~ m1_subset_1(X3,u1_struct_0(X0)) ) )
      & ( ( ! [X6] :
              ( r2_orders_2(X0,X6,sK7(X0,X1,X2))
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & sK7(X0,X1,X2) = X2
          & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f42,f44,f43])).

fof(f43,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X4,X3)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK6(X0,X1,X3),X3)
        & r2_hidden(sK6(X0,X1,X3),X1)
        & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X0,X6,X5)
              | ~ r2_hidden(X6,X1)
              | ~ m1_subset_1(X6,u1_struct_0(X0)) )
          & X2 = X5
          & m1_subset_1(X5,u1_struct_0(X0)) )
     => ( ! [X6] :
            ( r2_orders_2(X0,X6,sK7(X0,X1,X2))
            | ~ r2_hidden(X6,X1)
            | ~ m1_subset_1(X6,u1_struct_0(X0)) )
        & sK7(X0,X1,X2) = X2
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X1,X2,X0] :
      ( ( sP0(X1,X2,X0)
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
        | ~ sP0(X1,X2,X0) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_orders_2(X0,sK6(X0,X1,X3),X3)
      | sP0(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X0,X1,X2)
      | ~ r2_orders_2(X0,sK6(X0,X1,X3),X3)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f299,plain,
    ( spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(avatar_contradiction_clause,[],[f298])).

fof(f298,plain,
    ( $false
    | spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f297,f51])).

fof(f297,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl8_1
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f292,f89])).

fof(f89,plain,
    ( ~ r2_orders_2(sK2,sK3,sK4)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f87])).

fof(f292,plain,
    ( r2_orders_2(sK2,sK3,sK4)
    | ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f205,f81])).

fof(f81,plain,(
    ! [X3] : r2_hidden(X3,k2_tarski(X3,X3)) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k2_tarski(X3,X3) != X1 ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k2_tarski(X0,X0) != X1 ) ),
    inference(definition_unfolding,[],[f62,f55])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f38])).

fof(f205,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK3,sK3))
        | r2_orders_2(sK2,X1,sK4)
        | ~ m1_subset_1(X1,u1_struct_0(sK2)) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f202,f197])).

fof(f197,plain,
    ( sP0(sK2,k2_tarski(sK3,sK3),sK4)
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f186,f122])).

fof(f122,plain,
    ( r2_hidden(sK4,k1_orders_2(sK2,k2_tarski(sK3,sK3)))
    | ~ spl8_2
    | ~ spl8_4 ),
    inference(backward_demodulation,[],[f92,f111])).

fof(f92,plain,
    ( r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f91])).

fof(f186,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_orders_2(sK2,k2_tarski(sK3,sK3)))
        | sP0(sK2,k2_tarski(sK3,sK3),X1) )
    | spl8_3
    | ~ spl8_4 ),
    inference(subsumption_resolution,[],[f184,f163])).

fof(f184,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_orders_2(sK2,k2_tarski(sK3,sK3)))
        | sP0(sK2,k2_tarski(sK3,sK3),X1)
        | ~ sP1(X1,k2_tarski(sK3,sK3),sK2) )
    | spl8_3
    | ~ spl8_4 ),
    inference(superposition,[],[f65,f177])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | sP0(X2,X1,X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f202,plain,
    ( ! [X1] :
        ( r2_orders_2(sK2,X1,sK4)
        | ~ r2_hidden(X1,k2_tarski(sK3,sK3))
        | ~ m1_subset_1(X1,u1_struct_0(sK2))
        | ~ sP0(sK2,k2_tarski(sK3,sK3),sK4) )
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(superposition,[],[f69,f200])).

fof(f200,plain,
    ( sK4 = sK7(sK2,k2_tarski(sK3,sK3),sK4)
    | ~ spl8_2
    | spl8_3
    | ~ spl8_4 ),
    inference(resolution,[],[f197,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ sP0(X0,X1,X2)
      | sK7(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X0,X6,sK7(X0,X1,X2))
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f121,plain,(
    ~ spl8_3 ),
    inference(avatar_contradiction_clause,[],[f120])).

fof(f120,plain,
    ( $false
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f119,f46])).

fof(f119,plain,
    ( v2_struct_0(sK2)
    | ~ spl8_3 ),
    inference(subsumption_resolution,[],[f118,f97])).

fof(f97,plain,(
    l1_struct_0(sK2) ),
    inference(resolution,[],[f56,f50])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f118,plain,
    ( ~ l1_struct_0(sK2)
    | v2_struct_0(sK2)
    | ~ spl8_3 ),
    inference(resolution,[],[f107,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f107,plain,
    ( v1_xboole_0(u1_struct_0(sK2))
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f112,plain,
    ( spl8_3
    | spl8_4 ),
    inference(avatar_split_clause,[],[f100,f109,f105])).

fof(f100,plain,
    ( k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)
    | v1_xboole_0(u1_struct_0(sK2)) ),
    inference(resolution,[],[f75,f51])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f59,f55])).

% (31604)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f59,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f95,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f53,f91,f87])).

fof(f53,plain,
    ( r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
    | r2_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f94,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f54,f91,f87])).

fof(f54,plain,
    ( ~ r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))
    | ~ r2_orders_2(sK2,sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:39:21 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.22/0.50  % (31589)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (31589)Refutation found. Thanks to Tanya!
% 0.22/0.52  % SZS status Theorem for theBenchmark
% 0.22/0.52  % (31605)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.52  % (31597)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.52  % (31588)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.52  % (31586)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.26/0.53  % SZS output start Proof for theBenchmark
% 1.26/0.53  fof(f318,plain,(
% 1.26/0.53    $false),
% 1.26/0.53    inference(avatar_sat_refutation,[],[f94,f95,f112,f121,f299,f317])).
% 1.26/0.53  fof(f317,plain,(
% 1.26/0.53    ~spl8_1 | spl8_2 | spl8_3 | ~spl8_4),
% 1.26/0.53    inference(avatar_contradiction_clause,[],[f316])).
% 1.26/0.53  fof(f316,plain,(
% 1.26/0.53    $false | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f315,f52])).
% 1.26/0.53  fof(f52,plain,(
% 1.26/0.53    m1_subset_1(sK4,u1_struct_0(sK2))),
% 1.26/0.53    inference(cnf_transformation,[],[f34])).
% 1.26/0.53  fof(f34,plain,(
% 1.26/0.53    (((~r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | ~r2_orders_2(sK2,sK3,sK4)) & (r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | r2_orders_2(sK2,sK3,sK4)) & m1_subset_1(sK4,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2)),
% 1.26/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f30,f33,f32,f31])).
% 1.26/0.53  fof(f31,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) | ~r2_orders_2(sK2,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) | r2_orders_2(sK2,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) & l1_orders_2(sK2) & v5_orders_2(sK2) & v4_orders_2(sK2) & v3_orders_2(sK2) & ~v2_struct_0(sK2))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f32,plain,(
% 1.26/0.53    ? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) | ~r2_orders_2(sK2,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),X1))) | r2_orders_2(sK2,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(X1,u1_struct_0(sK2))) => (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | ~r2_orders_2(sK2,sK3,X2)) & (r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | r2_orders_2(sK2,sK3,X2)) & m1_subset_1(X2,u1_struct_0(sK2))) & m1_subset_1(sK3,u1_struct_0(sK2)))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f33,plain,(
% 1.26/0.53    ? [X2] : ((~r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | ~r2_orders_2(sK2,sK3,X2)) & (r2_hidden(X2,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | r2_orders_2(sK2,sK3,X2)) & m1_subset_1(X2,u1_struct_0(sK2))) => ((~r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | ~r2_orders_2(sK2,sK3,sK4)) & (r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | r2_orders_2(sK2,sK3,sK4)) & m1_subset_1(sK4,u1_struct_0(sK2)))),
% 1.26/0.53    introduced(choice_axiom,[])).
% 1.26/0.53  fof(f30,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.26/0.53    inference(flattening,[],[f29])).
% 1.26/0.53  fof(f29,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.26/0.53    inference(nnf_transformation,[],[f13])).
% 1.26/0.53  fof(f13,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.26/0.53    inference(flattening,[],[f12])).
% 1.26/0.53  fof(f12,plain,(
% 1.26/0.53    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f11])).
% 1.26/0.53  fof(f11,negated_conjecture,(
% 1.26/0.53    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 1.26/0.53    inference(negated_conjecture,[],[f10])).
% 1.26/0.53  fof(f10,conjecture,(
% 1.26/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).
% 1.26/0.53  fof(f315,plain,(
% 1.26/0.53    ~m1_subset_1(sK4,u1_struct_0(sK2)) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f314,f301])).
% 1.26/0.53  fof(f301,plain,(
% 1.26/0.53    ~sP0(sK2,k2_tarski(sK3,sK3),sK4) | (spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(resolution,[],[f300,f185])).
% 1.26/0.53  fof(f185,plain,(
% 1.26/0.53    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK2,k2_tarski(sK3,sK3))) | ~sP0(sK2,k2_tarski(sK3,sK3),X0)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f183,f163])).
% 1.26/0.53  fof(f163,plain,(
% 1.26/0.53    ( ! [X3] : (sP1(X3,k2_tarski(sK3,sK3),sK2)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f162,f46])).
% 1.26/0.53  fof(f46,plain,(
% 1.26/0.53    ~v2_struct_0(sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f34])).
% 1.26/0.53  fof(f162,plain,(
% 1.26/0.53    ( ! [X3] : (sP1(X3,k2_tarski(sK3,sK3),sK2) | v2_struct_0(sK2)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f161,f47])).
% 1.26/0.53  fof(f47,plain,(
% 1.26/0.53    v3_orders_2(sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f34])).
% 1.26/0.53  fof(f161,plain,(
% 1.26/0.53    ( ! [X3] : (sP1(X3,k2_tarski(sK3,sK3),sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f160,f48])).
% 1.26/0.53  fof(f48,plain,(
% 1.26/0.53    v4_orders_2(sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f34])).
% 1.26/0.53  fof(f160,plain,(
% 1.26/0.53    ( ! [X3] : (sP1(X3,k2_tarski(sK3,sK3),sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f159,f49])).
% 1.26/0.53  fof(f49,plain,(
% 1.26/0.53    v5_orders_2(sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f34])).
% 1.26/0.53  fof(f159,plain,(
% 1.26/0.53    ( ! [X3] : (sP1(X3,k2_tarski(sK3,sK3),sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f157,f50])).
% 1.26/0.53  fof(f50,plain,(
% 1.26/0.53    l1_orders_2(sK2)),
% 1.26/0.53    inference(cnf_transformation,[],[f34])).
% 1.26/0.53  fof(f157,plain,(
% 1.26/0.53    ( ! [X3] : (sP1(X3,k2_tarski(sK3,sK3),sK2) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(resolution,[],[f73,f125])).
% 1.26/0.53  fof(f125,plain,(
% 1.26/0.53    m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f124,f106])).
% 1.26/0.53  fof(f106,plain,(
% 1.26/0.53    ~v1_xboole_0(u1_struct_0(sK2)) | spl8_3),
% 1.26/0.53    inference(avatar_component_clause,[],[f105])).
% 1.26/0.53  fof(f105,plain,(
% 1.26/0.53    spl8_3 <=> v1_xboole_0(u1_struct_0(sK2))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 1.26/0.53  fof(f124,plain,(
% 1.26/0.53    m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | v1_xboole_0(u1_struct_0(sK2)) | ~spl8_4),
% 1.26/0.53    inference(subsumption_resolution,[],[f123,f51])).
% 1.26/0.53  fof(f51,plain,(
% 1.26/0.53    m1_subset_1(sK3,u1_struct_0(sK2))),
% 1.26/0.53    inference(cnf_transformation,[],[f34])).
% 1.26/0.53  fof(f123,plain,(
% 1.26/0.53    m1_subset_1(k2_tarski(sK3,sK3),k1_zfmisc_1(u1_struct_0(sK2))) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | v1_xboole_0(u1_struct_0(sK2)) | ~spl8_4),
% 1.26/0.53    inference(superposition,[],[f60,f111])).
% 1.26/0.53  fof(f111,plain,(
% 1.26/0.53    k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) | ~spl8_4),
% 1.26/0.53    inference(avatar_component_clause,[],[f109])).
% 1.26/0.53  fof(f109,plain,(
% 1.26/0.53    spl8_4 <=> k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3)),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 1.26/0.53  fof(f60,plain,(
% 1.26/0.53    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f22])).
% 1.26/0.53  fof(f22,plain,(
% 1.26/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.26/0.53    inference(flattening,[],[f21])).
% 1.26/0.53  fof(f21,plain,(
% 1.26/0.53    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f6])).
% 1.26/0.53  fof(f6,axiom,(
% 1.26/0.53    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.26/0.53  fof(f73,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP1(X0,X2,X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f28])).
% 1.26/0.53  fof(f28,plain,(
% 1.26/0.53    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.26/0.53    inference(definition_folding,[],[f24,f27,f26])).
% 1.26/0.53  fof(f26,plain,(
% 1.26/0.53    ! [X1,X2,X0] : (sP0(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 1.26/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.26/0.53  fof(f27,plain,(
% 1.26/0.53    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> sP0(X1,X2,X0)) | ~sP1(X0,X2,X1))),
% 1.26/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 1.26/0.53  fof(f24,plain,(
% 1.26/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 1.26/0.53    inference(flattening,[],[f23])).
% 1.26/0.53  fof(f23,plain,(
% 1.26/0.53    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 1.26/0.53    inference(ennf_transformation,[],[f8])).
% 1.26/0.53  fof(f8,axiom,(
% 1.26/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 1.26/0.53  fof(f183,plain,(
% 1.26/0.53    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK2,k2_tarski(sK3,sK3))) | ~sP0(sK2,k2_tarski(sK3,sK3),X0) | ~sP1(X0,k2_tarski(sK3,sK3),sK2)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(superposition,[],[f66,f177])).
% 1.26/0.53  fof(f177,plain,(
% 1.26/0.53    k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3)) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f176,f46])).
% 1.26/0.53  fof(f176,plain,(
% 1.26/0.53    k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3)) | v2_struct_0(sK2) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f175,f47])).
% 1.26/0.53  fof(f175,plain,(
% 1.26/0.53    k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3)) | ~v3_orders_2(sK2) | v2_struct_0(sK2) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f174,f48])).
% 1.26/0.53  fof(f174,plain,(
% 1.26/0.53    k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3)) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f173,f49])).
% 1.26/0.53  fof(f173,plain,(
% 1.26/0.53    k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3)) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(subsumption_resolution,[],[f171,f50])).
% 1.26/0.53  fof(f171,plain,(
% 1.26/0.53    k1_orders_2(sK2,k2_tarski(sK3,sK3)) = a_2_0_orders_2(sK2,k2_tarski(sK3,sK3)) | ~l1_orders_2(sK2) | ~v5_orders_2(sK2) | ~v4_orders_2(sK2) | ~v3_orders_2(sK2) | v2_struct_0(sK2) | (spl8_3 | ~spl8_4)),
% 1.26/0.53    inference(resolution,[],[f58,f125])).
% 1.26/0.53  fof(f58,plain,(
% 1.26/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f18])).
% 1.26/0.53  fof(f18,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.26/0.53    inference(flattening,[],[f17])).
% 1.26/0.53  fof(f17,plain,(
% 1.26/0.53    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.26/0.53    inference(ennf_transformation,[],[f5])).
% 1.26/0.53  fof(f5,axiom,(
% 1.26/0.53    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 1.26/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 1.26/0.53  fof(f66,plain,(
% 1.26/0.53    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.26/0.53    inference(cnf_transformation,[],[f40])).
% 1.26/0.53  fof(f40,plain,(
% 1.26/0.53    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP0(X2,X1,X0)) & (sP0(X2,X1,X0) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)))) | ~sP1(X0,X1,X2))),
% 1.26/0.53    inference(rectify,[],[f39])).
% 1.26/0.53  fof(f39,plain,(
% 1.26/0.53    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~sP0(X1,X2,X0)) & (sP0(X1,X2,X0) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~sP1(X0,X2,X1))),
% 1.26/0.53    inference(nnf_transformation,[],[f27])).
% 1.26/0.53  fof(f300,plain,(
% 1.26/0.53    ~r2_hidden(sK4,k1_orders_2(sK2,k2_tarski(sK3,sK3))) | (spl8_2 | ~spl8_4)),
% 1.26/0.53    inference(forward_demodulation,[],[f93,f111])).
% 1.26/0.53  fof(f93,plain,(
% 1.26/0.53    ~r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | spl8_2),
% 1.26/0.53    inference(avatar_component_clause,[],[f91])).
% 1.26/0.53  fof(f91,plain,(
% 1.26/0.53    spl8_2 <=> r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3)))),
% 1.26/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 1.26/0.54  fof(f314,plain,(
% 1.26/0.54    sP0(sK2,k2_tarski(sK3,sK3),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | (~spl8_1 | spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f312,f88])).
% 1.26/0.54  fof(f88,plain,(
% 1.26/0.54    r2_orders_2(sK2,sK3,sK4) | ~spl8_1),
% 1.26/0.54    inference(avatar_component_clause,[],[f87])).
% 1.26/0.54  fof(f87,plain,(
% 1.26/0.54    spl8_1 <=> r2_orders_2(sK2,sK3,sK4)),
% 1.26/0.54    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 1.26/0.54  fof(f312,plain,(
% 1.26/0.54    ~r2_orders_2(sK2,sK3,sK4) | sP0(sK2,k2_tarski(sK3,sK3),sK4) | ~m1_subset_1(sK4,u1_struct_0(sK2)) | (spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(superposition,[],[f83,f308])).
% 1.26/0.54  fof(f308,plain,(
% 1.26/0.54    sK3 = sK6(sK2,k2_tarski(sK3,sK3),sK4) | (spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f305,f52])).
% 1.26/0.54  fof(f305,plain,(
% 1.26/0.54    ~m1_subset_1(sK4,u1_struct_0(sK2)) | sK3 = sK6(sK2,k2_tarski(sK3,sK3),sK4) | (spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(resolution,[],[f301,f146])).
% 1.26/0.54  fof(f146,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (sP0(X0,k2_tarski(X1,X1),X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | sK6(X0,k2_tarski(X1,X1),X2) = X1) )),
% 1.26/0.54    inference(resolution,[],[f84,f82])).
% 1.26/0.54  fof(f82,plain,(
% 1.26/0.54    ( ! [X0,X3] : (~r2_hidden(X3,k2_tarski(X0,X0)) | X0 = X3) )),
% 1.26/0.54    inference(equality_resolution,[],[f79])).
% 1.26/0.54  fof(f79,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k2_tarski(X0,X0) != X1) )),
% 1.26/0.54    inference(definition_unfolding,[],[f61,f55])).
% 1.26/0.54  fof(f55,plain,(
% 1.26/0.54    ( ! [X0] : (k1_tarski(X0) = k2_tarski(X0,X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f2])).
% 1.26/0.54  fof(f2,axiom,(
% 1.26/0.54    ! [X0] : k1_tarski(X0) = k2_tarski(X0,X0)),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 1.26/0.54  fof(f61,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (X0 = X3 | ~r2_hidden(X3,X1) | k1_tarski(X0) != X1) )),
% 1.26/0.54    inference(cnf_transformation,[],[f38])).
% 1.26/0.54  fof(f38,plain,(
% 1.26/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f36,f37])).
% 1.26/0.54  fof(f37,plain,(
% 1.26/0.54    ! [X1,X0] : (? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1))) => ((sK5(X0,X1) != X0 | ~r2_hidden(sK5(X0,X1),X1)) & (sK5(X0,X1) = X0 | r2_hidden(sK5(X0,X1),X1))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f36,plain,(
% 1.26/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X3] : ((r2_hidden(X3,X1) | X0 != X3) & (X0 = X3 | ~r2_hidden(X3,X1))) | k1_tarski(X0) != X1))),
% 1.26/0.54    inference(rectify,[],[f35])).
% 1.26/0.54  fof(f35,plain,(
% 1.26/0.54    ! [X0,X1] : ((k1_tarski(X0) = X1 | ? [X2] : ((X0 != X2 | ~r2_hidden(X2,X1)) & (X0 = X2 | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | X0 != X2) & (X0 = X2 | ~r2_hidden(X2,X1))) | k1_tarski(X0) != X1))),
% 1.26/0.54    inference(nnf_transformation,[],[f1])).
% 1.26/0.54  fof(f1,axiom,(
% 1.26/0.54    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 1.26/0.54  fof(f84,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (r2_hidden(sK6(X0,X1,X3),X1) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.26/0.54    inference(equality_resolution,[],[f71])).
% 1.26/0.54  fof(f71,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | r2_hidden(sK6(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f45])).
% 1.26/0.54  fof(f45,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,sK6(X0,X1,X3),X3) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,X6,sK7(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.26/0.54    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f42,f44,f43])).
% 1.26/0.54  fof(f43,plain,(
% 1.26/0.54    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,sK6(X0,X1,X3),X3) & r2_hidden(sK6(X0,X1,X3),X1) & m1_subset_1(sK6(X0,X1,X3),u1_struct_0(X0))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f44,plain,(
% 1.26/0.54    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,X6,sK7(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK7(X0,X1,X2) = X2 & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X0))))),
% 1.26/0.54    introduced(choice_axiom,[])).
% 1.26/0.54  fof(f42,plain,(
% 1.26/0.54    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP0(X0,X1,X2)))),
% 1.26/0.54    inference(rectify,[],[f41])).
% 1.26/0.54  fof(f41,plain,(
% 1.26/0.54    ! [X1,X2,X0] : ((sP0(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP0(X1,X2,X0)))),
% 1.26/0.54    inference(nnf_transformation,[],[f26])).
% 1.26/0.54  fof(f83,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (~r2_orders_2(X0,sK6(X0,X1,X3),X3) | sP0(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.26/0.54    inference(equality_resolution,[],[f72])).
% 1.26/0.54  fof(f72,plain,(
% 1.26/0.54    ( ! [X2,X0,X3,X1] : (sP0(X0,X1,X2) | ~r2_orders_2(X0,sK6(X0,X1,X3),X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 1.26/0.54    inference(cnf_transformation,[],[f45])).
% 1.26/0.54  fof(f299,plain,(
% 1.26/0.54    spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f298])).
% 1.26/0.54  fof(f298,plain,(
% 1.26/0.54    $false | (spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f297,f51])).
% 1.26/0.54  fof(f297,plain,(
% 1.26/0.54    ~m1_subset_1(sK3,u1_struct_0(sK2)) | (spl8_1 | ~spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f292,f89])).
% 1.26/0.54  fof(f89,plain,(
% 1.26/0.54    ~r2_orders_2(sK2,sK3,sK4) | spl8_1),
% 1.26/0.54    inference(avatar_component_clause,[],[f87])).
% 1.26/0.54  fof(f292,plain,(
% 1.26/0.54    r2_orders_2(sK2,sK3,sK4) | ~m1_subset_1(sK3,u1_struct_0(sK2)) | (~spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(resolution,[],[f205,f81])).
% 1.26/0.54  fof(f81,plain,(
% 1.26/0.54    ( ! [X3] : (r2_hidden(X3,k2_tarski(X3,X3))) )),
% 1.26/0.54    inference(equality_resolution,[],[f80])).
% 1.26/0.54  fof(f80,plain,(
% 1.26/0.54    ( ! [X3,X1] : (r2_hidden(X3,X1) | k2_tarski(X3,X3) != X1) )),
% 1.26/0.54    inference(equality_resolution,[],[f78])).
% 1.26/0.54  fof(f78,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k2_tarski(X0,X0) != X1) )),
% 1.26/0.54    inference(definition_unfolding,[],[f62,f55])).
% 1.26/0.54  fof(f62,plain,(
% 1.26/0.54    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | X0 != X3 | k1_tarski(X0) != X1) )),
% 1.26/0.54    inference(cnf_transformation,[],[f38])).
% 1.26/0.54  fof(f205,plain,(
% 1.26/0.54    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK3,sK3)) | r2_orders_2(sK2,X1,sK4) | ~m1_subset_1(X1,u1_struct_0(sK2))) ) | (~spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f202,f197])).
% 1.26/0.54  fof(f197,plain,(
% 1.26/0.54    sP0(sK2,k2_tarski(sK3,sK3),sK4) | (~spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(resolution,[],[f186,f122])).
% 1.26/0.54  fof(f122,plain,(
% 1.26/0.54    r2_hidden(sK4,k1_orders_2(sK2,k2_tarski(sK3,sK3))) | (~spl8_2 | ~spl8_4)),
% 1.26/0.54    inference(backward_demodulation,[],[f92,f111])).
% 1.26/0.54  fof(f92,plain,(
% 1.26/0.54    r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | ~spl8_2),
% 1.26/0.54    inference(avatar_component_clause,[],[f91])).
% 1.26/0.54  fof(f186,plain,(
% 1.26/0.54    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK2,k2_tarski(sK3,sK3))) | sP0(sK2,k2_tarski(sK3,sK3),X1)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(subsumption_resolution,[],[f184,f163])).
% 1.26/0.54  fof(f184,plain,(
% 1.26/0.54    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK2,k2_tarski(sK3,sK3))) | sP0(sK2,k2_tarski(sK3,sK3),X1) | ~sP1(X1,k2_tarski(sK3,sK3),sK2)) ) | (spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(superposition,[],[f65,f177])).
% 1.26/0.54  fof(f65,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(X2,X1)) | sP0(X2,X1,X0) | ~sP1(X0,X1,X2)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f40])).
% 1.26/0.54  fof(f202,plain,(
% 1.26/0.54    ( ! [X1] : (r2_orders_2(sK2,X1,sK4) | ~r2_hidden(X1,k2_tarski(sK3,sK3)) | ~m1_subset_1(X1,u1_struct_0(sK2)) | ~sP0(sK2,k2_tarski(sK3,sK3),sK4)) ) | (~spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(superposition,[],[f69,f200])).
% 1.26/0.54  fof(f200,plain,(
% 1.26/0.54    sK4 = sK7(sK2,k2_tarski(sK3,sK3),sK4) | (~spl8_2 | spl8_3 | ~spl8_4)),
% 1.26/0.54    inference(resolution,[],[f197,f68])).
% 1.26/0.54  fof(f68,plain,(
% 1.26/0.54    ( ! [X2,X0,X1] : (~sP0(X0,X1,X2) | sK7(X0,X1,X2) = X2) )),
% 1.26/0.54    inference(cnf_transformation,[],[f45])).
% 1.26/0.54  fof(f69,plain,(
% 1.26/0.54    ( ! [X6,X2,X0,X1] : (r2_orders_2(X0,X6,sK7(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP0(X0,X1,X2)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f45])).
% 1.26/0.54  fof(f121,plain,(
% 1.26/0.54    ~spl8_3),
% 1.26/0.54    inference(avatar_contradiction_clause,[],[f120])).
% 1.26/0.54  fof(f120,plain,(
% 1.26/0.54    $false | ~spl8_3),
% 1.26/0.54    inference(subsumption_resolution,[],[f119,f46])).
% 1.26/0.54  fof(f119,plain,(
% 1.26/0.54    v2_struct_0(sK2) | ~spl8_3),
% 1.26/0.54    inference(subsumption_resolution,[],[f118,f97])).
% 1.26/0.54  fof(f97,plain,(
% 1.26/0.54    l1_struct_0(sK2)),
% 1.26/0.54    inference(resolution,[],[f56,f50])).
% 1.26/0.54  fof(f56,plain,(
% 1.26/0.54    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f14])).
% 1.26/0.54  fof(f14,plain,(
% 1.26/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 1.26/0.54    inference(ennf_transformation,[],[f7])).
% 1.26/0.54  fof(f7,axiom,(
% 1.26/0.54    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 1.26/0.54  fof(f118,plain,(
% 1.26/0.54    ~l1_struct_0(sK2) | v2_struct_0(sK2) | ~spl8_3),
% 1.26/0.54    inference(resolution,[],[f107,f57])).
% 1.26/0.54  fof(f57,plain,(
% 1.26/0.54    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f16])).
% 1.26/0.54  fof(f16,plain,(
% 1.26/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.26/0.54    inference(flattening,[],[f15])).
% 1.26/0.54  fof(f15,plain,(
% 1.26/0.54    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f4])).
% 1.26/0.54  fof(f4,axiom,(
% 1.26/0.54    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.26/0.54  fof(f107,plain,(
% 1.26/0.54    v1_xboole_0(u1_struct_0(sK2)) | ~spl8_3),
% 1.26/0.54    inference(avatar_component_clause,[],[f105])).
% 1.26/0.54  fof(f112,plain,(
% 1.26/0.54    spl8_3 | spl8_4),
% 1.26/0.54    inference(avatar_split_clause,[],[f100,f109,f105])).
% 1.26/0.54  fof(f100,plain,(
% 1.26/0.54    k6_domain_1(u1_struct_0(sK2),sK3) = k2_tarski(sK3,sK3) | v1_xboole_0(u1_struct_0(sK2))),
% 1.26/0.54    inference(resolution,[],[f75,f51])).
% 1.26/0.54  fof(f75,plain,(
% 1.26/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(definition_unfolding,[],[f59,f55])).
% 1.26/0.54  % (31604)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.26/0.54  fof(f59,plain,(
% 1.26/0.54    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.26/0.54    inference(cnf_transformation,[],[f20])).
% 1.26/0.54  fof(f20,plain,(
% 1.26/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.26/0.54    inference(flattening,[],[f19])).
% 1.26/0.54  fof(f19,plain,(
% 1.26/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.26/0.54    inference(ennf_transformation,[],[f9])).
% 1.26/0.54  fof(f9,axiom,(
% 1.26/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.26/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.26/0.54  fof(f95,plain,(
% 1.26/0.54    spl8_1 | spl8_2),
% 1.26/0.54    inference(avatar_split_clause,[],[f53,f91,f87])).
% 1.26/0.54  fof(f53,plain,(
% 1.26/0.54    r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | r2_orders_2(sK2,sK3,sK4)),
% 1.26/0.54    inference(cnf_transformation,[],[f34])).
% 1.26/0.54  fof(f94,plain,(
% 1.26/0.54    ~spl8_1 | ~spl8_2),
% 1.26/0.54    inference(avatar_split_clause,[],[f54,f91,f87])).
% 1.26/0.54  fof(f54,plain,(
% 1.26/0.54    ~r2_hidden(sK4,k1_orders_2(sK2,k6_domain_1(u1_struct_0(sK2),sK3))) | ~r2_orders_2(sK2,sK3,sK4)),
% 1.26/0.54    inference(cnf_transformation,[],[f34])).
% 1.26/0.54  % SZS output end Proof for theBenchmark
% 1.26/0.54  % (31589)------------------------------
% 1.26/0.54  % (31589)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.26/0.54  % (31589)Termination reason: Refutation
% 1.26/0.54  
% 1.26/0.54  % (31589)Memory used [KB]: 10874
% 1.26/0.54  % (31589)Time elapsed: 0.090 s
% 1.26/0.54  % (31589)------------------------------
% 1.26/0.54  % (31589)------------------------------
% 1.26/0.54  % (31582)Success in time 0.167 s
%------------------------------------------------------------------------------
