%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  171 (1056 expanded)
%              Number of leaves         :   26 ( 339 expanded)
%              Depth                    :   27
%              Number of atoms          :  869 (8818 expanded)
%              Number of equality atoms :   96 ( 244 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f783,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f118,f141,f205,f349,f782])).

fof(f782,plain,
    ( ~ spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f781])).

fof(f781,plain,
    ( $false
    | ~ spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f780,f68])).

fof(f68,plain,(
    m1_subset_1(sK6,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f42,plain,
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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

fof(f780,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f779,f351])).

fof(f351,plain,
    ( ~ sP1(sK4,k2_tarski(sK5,sK5),sK6)
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f350,f315])).

fof(f315,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
        | ~ sP1(sK4,k2_tarski(sK5,sK5),X0) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f313,f237])).

fof(f237,plain,
    ( ! [X0] : sP2(X0,k2_tarski(sK5,sK5),sK4)
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f236,f62])).

fof(f62,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f236,plain,
    ( ! [X0] :
        ( sP2(X0,k2_tarski(sK5,sK5),sK4)
        | v2_struct_0(sK4) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f235,f63])).

fof(f63,plain,(
    v3_orders_2(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f235,plain,
    ( ! [X0] :
        ( sP2(X0,k2_tarski(sK5,sK5),sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f234,f64])).

fof(f64,plain,(
    v4_orders_2(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f234,plain,
    ( ! [X0] :
        ( sP2(X0,k2_tarski(sK5,sK5),sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f233,f65])).

fof(f65,plain,(
    v5_orders_2(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f233,plain,
    ( ! [X0] :
        ( sP2(X0,k2_tarski(sK5,sK5),sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f224,f66])).

fof(f66,plain,(
    l1_orders_2(sK4) ),
    inference(cnf_transformation,[],[f43])).

fof(f224,plain,
    ( ! [X0] :
        ( sP2(X0,k2_tarski(sK5,sK5),sK4)
        | ~ l1_orders_2(sK4)
        | ~ v5_orders_2(sK4)
        | ~ v4_orders_2(sK4)
        | ~ v3_orders_2(sK4)
        | v2_struct_0(sK4) )
    | spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f222,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sP2(X0,X2,X1)
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( sP2(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(definition_folding,[],[f27,f34,f33])).

fof(f33,plain,(
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

fof(f34,plain,(
    ! [X0,X2,X1] :
      ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      <=> sP1(X1,X2,X0) )
      | ~ sP2(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f222,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f221,f135])).

fof(f135,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK4))
    | spl11_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl11_3
  <=> v1_xboole_0(u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).

fof(f221,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f218,f67])).

fof(f67,plain,(
    m1_subset_1(sK5,u1_struct_0(sK4)) ),
    inference(cnf_transformation,[],[f43])).

fof(f218,plain,
    ( m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4)))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | v1_xboole_0(u1_struct_0(sK4))
    | ~ spl11_4 ),
    inference(superposition,[],[f82,f140])).

fof(f140,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
    | ~ spl11_4 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl11_4
  <=> k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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

fof(f313,plain,
    ( ! [X0] :
        ( r2_hidden(X0,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
        | ~ sP1(sK4,k2_tarski(sK5,sK5),X0)
        | ~ sP2(X0,k2_tarski(sK5,sK5),sK4) )
    | spl11_3
    | ~ spl11_4 ),
    inference(superposition,[],[f84,f232])).

fof(f232,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f231,f62])).

fof(f231,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | v2_struct_0(sK4)
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f230,f63])).

fof(f230,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f229,f64])).

fof(f229,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f228,f65])).

fof(f228,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f223,f66])).

fof(f223,plain,
    ( k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5))
    | ~ l1_orders_2(sK4)
    | ~ v5_orders_2(sK4)
    | ~ v4_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4)
    | spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f222,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

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
    inference(flattening,[],[f16])).

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

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | ~ sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X2,X1))
          | ~ sP1(X2,X1,X0) )
        & ( sP1(X2,X1,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X2,X1)) ) )
      | ~ sP2(X0,X1,X2) ) ),
    inference(rectify,[],[f49])).

fof(f49,plain,(
    ! [X0,X2,X1] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ~ sP1(X1,X2,X0) )
        & ( sP1(X1,X2,X0)
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ sP2(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f350,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
    | spl11_2
    | ~ spl11_4 ),
    inference(forward_demodulation,[],[f116,f140])).

fof(f116,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | spl11_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl11_2
  <=> r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).

fof(f779,plain,
    ( sP1(sK4,k2_tarski(sK5,sK5),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | ~ spl11_1
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f755,f111])).

fof(f111,plain,
    ( r2_orders_2(sK4,sK5,sK6)
    | ~ spl11_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl11_1
  <=> r2_orders_2(sK4,sK5,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).

fof(f755,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | sP1(sK4,k2_tarski(sK5,sK5),sK6)
    | ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(superposition,[],[f103,f737])).

fof(f737,plain,
    ( sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6)
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f736,f68])).

fof(f736,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6)
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(duplicate_literal_removal,[],[f725])).

fof(f725,plain,
    ( ~ m1_subset_1(sK6,u1_struct_0(sK4))
    | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6)
    | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6)
    | spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f165,f351])).

fof(f165,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,k2_tarski(X1,X2),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | sK8(X0,k2_tarski(X1,X2),X3) = X1
      | sK8(X0,k2_tarski(X1,X2),X3) = X2 ) ),
    inference(resolution,[],[f104,f149])).

fof(f149,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k2_tarski(X0,X2))
      | X0 = X1
      | X1 = X2 ) ),
    inference(resolution,[],[f93,f108])).

fof(f108,plain,(
    ! [X0,X1] : sP3(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( sP3(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP3(X1,X0,X2) )
      & ( sP3(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP3(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f36])).

fof(f36,plain,(
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

fof(f93,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ sP3(X0,X1,X2)
      | X1 = X4
      | ~ r2_hidden(X4,X2)
      | X0 = X4 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f58,f59])).

fof(f59,plain,(
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

fof(f58,plain,(
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
    inference(rectify,[],[f57])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f104,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(sK8(X0,X1,X3),X1)
      | sP1(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | r2_hidden(sK8(X0,X1,X3),X1)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f52,f54,f53])).

fof(f53,plain,(
    ! [X3,X1,X0] :
      ( ? [X4] :
          ( ~ r2_orders_2(X0,X4,X3)
          & r2_hidden(X4,X1)
          & m1_subset_1(X4,u1_struct_0(X0)) )
     => ( ~ r2_orders_2(X0,sK8(X0,X1,X3),X3)
        & r2_hidden(sK8(X0,X1,X3),X1)
        & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,(
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

fof(f52,plain,(
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
    inference(rectify,[],[f51])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f103,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_orders_2(X0,sK8(X0,X1,X3),X3)
      | sP1(X0,X1,X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(equality_resolution,[],[f90])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( sP1(X0,X1,X2)
      | ~ r2_orders_2(X0,sK8(X0,X1,X3),X3)
      | X2 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f349,plain,
    ( spl11_1
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(avatar_contradiction_clause,[],[f348])).

fof(f348,plain,
    ( $false
    | spl11_1
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f343,f112])).

fof(f112,plain,
    ( ~ r2_orders_2(sK4,sK5,sK6)
    | spl11_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f343,plain,
    ( r2_orders_2(sK4,sK5,sK6)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f341,f122])).

fof(f122,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X0,X1)) ),
    inference(resolution,[],[f107,f108])).

fof(f107,plain,(
    ! [X4,X2,X0] :
      ( ~ sP3(X0,X4,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f94])).

fof(f94,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X1 != X4
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f341,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | r2_orders_2(sK4,X1,sK6) )
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f340,f220])).

fof(f220,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK5,sK5))
        | m1_subset_1(X0,u1_struct_0(sK4)) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f219,f67])).

fof(f219,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK5,sK5))
        | m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f217,f135])).

fof(f217,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_tarski(sK5,sK5))
        | v1_xboole_0(u1_struct_0(sK4))
        | m1_subset_1(X0,u1_struct_0(sK4))
        | ~ m1_subset_1(sK5,u1_struct_0(sK4)) )
    | ~ spl11_4 ),
    inference(superposition,[],[f124,f140])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k6_domain_1(X1,X0))
      | v1_xboole_0(X1)
      | m1_subset_1(X2,X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(resolution,[],[f82,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
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

fof(f340,plain,
    ( ! [X1] :
        ( r2_orders_2(sK4,X1,sK6)
        | ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK4)) )
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f337,f323])).

fof(f323,plain,
    ( sP1(sK4,k2_tarski(sK5,sK5),sK6)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f316,f216])).

fof(f216,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
    | ~ spl11_2
    | ~ spl11_4 ),
    inference(backward_demodulation,[],[f115,f140])).

fof(f115,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | ~ spl11_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f316,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
        | sP1(sK4,k2_tarski(sK5,sK5),X1) )
    | spl11_3
    | ~ spl11_4 ),
    inference(subsumption_resolution,[],[f314,f237])).

fof(f314,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_orders_2(sK4,k2_tarski(sK5,sK5)))
        | sP1(sK4,k2_tarski(sK5,sK5),X1)
        | ~ sP2(X1,k2_tarski(sK5,sK5),sK4) )
    | spl11_3
    | ~ spl11_4 ),
    inference(superposition,[],[f83,f232])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,a_2_0_orders_2(X2,X1))
      | sP1(X2,X1,X0)
      | ~ sP2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f337,plain,
    ( ! [X1] :
        ( r2_orders_2(sK4,X1,sK6)
        | ~ r2_hidden(X1,k2_tarski(sK5,sK5))
        | ~ m1_subset_1(X1,u1_struct_0(sK4))
        | ~ sP1(sK4,k2_tarski(sK5,sK5),sK6) )
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(superposition,[],[f87,f334])).

fof(f334,plain,
    ( sK6 = sK9(sK4,k2_tarski(sK5,sK5),sK6)
    | ~ spl11_2
    | spl11_3
    | ~ spl11_4 ),
    inference(resolution,[],[f323,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ sP1(X0,X1,X2)
      | sK9(X0,X1,X2) = X2 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f87,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X0,X6,sK9(X0,X1,X2))
      | ~ r2_hidden(X6,X1)
      | ~ m1_subset_1(X6,u1_struct_0(X0))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f205,plain,(
    ~ spl11_3 ),
    inference(avatar_contradiction_clause,[],[f204])).

fof(f204,plain,
    ( $false
    | ~ spl11_3 ),
    inference(subsumption_resolution,[],[f203,f136])).

fof(f136,plain,
    ( v1_xboole_0(u1_struct_0(sK4))
    | ~ spl11_3 ),
    inference(avatar_component_clause,[],[f134])).

fof(f203,plain,(
    ~ v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f187,f163])).

fof(f163,plain,(
    ! [X4,X5,X3] :
      ( ~ sP0(X4,X5,X3)
      | ~ v1_xboole_0(u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f162])).

fof(f162,plain,(
    ! [X4,X5,X3] :
      ( ~ v1_xboole_0(u1_struct_0(X3))
      | ~ sP0(X4,X5,X3)
      | ~ sP0(X4,X5,X3) ) ),
    inference(resolution,[],[f127,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,sK7(X0,X1,X2))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,sK7(X0,X1,X2))
        & r2_hidden(X1,sK7(X0,X1,X2))
        & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
        & v6_orders_2(sK7(X0,X1,X2),X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).

fof(f46,plain,(
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

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r2_hidden(X0,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
          & v6_orders_2(X3,X2) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X2,X3)
          & r2_hidden(X1,X3)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
          & v6_orders_2(X3,X0) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f127,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r2_hidden(X7,sK7(X4,X5,X6))
      | ~ v1_xboole_0(u1_struct_0(X6))
      | ~ sP0(X4,X5,X6) ) ),
    inference(resolution,[],[f75,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f187,plain,(
    sP0(sK5,sK5,sK4) ),
    inference(subsumption_resolution,[],[f186,f63])).

fof(f186,plain,
    ( sP0(sK5,sK5,sK4)
    | ~ v3_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f185,f66])).

fof(f185,plain,
    ( sP0(sK5,sK5,sK4)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(subsumption_resolution,[],[f184,f67])).

fof(f184,plain,
    ( sP0(sK5,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(duplicate_literal_removal,[],[f181])).

fof(f181,plain,
    ( sP0(sK5,sK5,sK4)
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ m1_subset_1(sK5,u1_struct_0(sK4))
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4) ),
    inference(resolution,[],[f79,f157])).

fof(f157,plain,(
    r1_orders_2(sK4,sK5,sK5) ),
    inference(subsumption_resolution,[],[f156,f62])).

fof(f156,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f155,f63])).

fof(f155,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(subsumption_resolution,[],[f152,f66])).

fof(f152,plain,
    ( r1_orders_2(sK4,sK5,sK5)
    | ~ l1_orders_2(sK4)
    | ~ v3_orders_2(sK4)
    | v2_struct_0(sK4) ),
    inference(resolution,[],[f73,f67])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | r1_orders_2(X0,X1,X1)
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,X1,X1)
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
         => r1_orders_2(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_orders_2(X0,X1,X2)
      | sP0(X2,X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
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
    inference(rectify,[],[f32])).

fof(f32,plain,(
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
    inference(definition_folding,[],[f21,f31])).

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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(rectify,[],[f10])).

fof(f10,axiom,(
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

fof(f141,plain,
    ( spl11_3
    | spl11_4 ),
    inference(avatar_split_clause,[],[f128,f138,f134])).

fof(f128,plain,
    ( k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)
    | v1_xboole_0(u1_struct_0(sK4)) ),
    inference(resolution,[],[f102,f67])).

fof(f102,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f81,f71])).

fof(f71,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f81,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
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

fof(f118,plain,
    ( spl11_1
    | spl11_2 ),
    inference(avatar_split_clause,[],[f69,f114,f110])).

fof(f69,plain,
    ( r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f117,plain,
    ( ~ spl11_1
    | ~ spl11_2 ),
    inference(avatar_split_clause,[],[f70,f114,f110])).

fof(f70,plain,
    ( ~ r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))
    | ~ r2_orders_2(sK4,sK5,sK6) ),
    inference(cnf_transformation,[],[f43])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:59:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (8178)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (8194)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.52  % (8186)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.52  % (8183)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (8187)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.54  % (8201)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.54  % (8194)Refutation not found, incomplete strategy% (8194)------------------------------
% 0.22/0.54  % (8194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8194)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8194)Memory used [KB]: 10746
% 0.22/0.54  % (8194)Time elapsed: 0.124 s
% 0.22/0.54  % (8194)------------------------------
% 0.22/0.54  % (8194)------------------------------
% 0.22/0.54  % (8207)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.54  % (8180)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (8179)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.54  % (8206)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.54  % (8193)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.54  % (8207)Refutation not found, incomplete strategy% (8207)------------------------------
% 0.22/0.54  % (8207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (8207)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (8207)Memory used [KB]: 1663
% 0.22/0.54  % (8207)Time elapsed: 0.129 s
% 0.22/0.54  % (8207)------------------------------
% 0.22/0.54  % (8207)------------------------------
% 0.22/0.54  % (8189)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.55  % (8182)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (8188)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (8188)Refutation not found, incomplete strategy% (8188)------------------------------
% 0.22/0.55  % (8188)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8188)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8188)Memory used [KB]: 10746
% 0.22/0.55  % (8188)Time elapsed: 0.134 s
% 0.22/0.55  % (8188)------------------------------
% 0.22/0.55  % (8188)------------------------------
% 0.22/0.55  % (8182)Refutation not found, incomplete strategy% (8182)------------------------------
% 0.22/0.55  % (8182)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (8182)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (8182)Memory used [KB]: 1918
% 0.22/0.55  % (8182)Time elapsed: 0.139 s
% 0.22/0.55  % (8182)------------------------------
% 0.22/0.55  % (8182)------------------------------
% 0.22/0.55  % (8203)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (8185)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (8199)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.55  % (8204)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (8198)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.55  % (8205)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (8195)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (8181)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.56  % (8196)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (8191)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (8190)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.56  % (8202)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.57  % (8197)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.57  % (8200)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (8184)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.57  % (8206)Refutation not found, incomplete strategy% (8206)------------------------------
% 0.22/0.57  % (8206)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (8206)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (8206)Memory used [KB]: 10746
% 0.22/0.57  % (8206)Time elapsed: 0.158 s
% 0.22/0.57  % (8206)------------------------------
% 0.22/0.57  % (8206)------------------------------
% 0.22/0.58  % (8192)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.59  % (8192)Refutation not found, incomplete strategy% (8192)------------------------------
% 0.22/0.59  % (8192)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.59  % (8192)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.59  
% 0.22/0.59  % (8192)Memory used [KB]: 1791
% 0.22/0.59  % (8192)Time elapsed: 0.163 s
% 0.22/0.59  % (8192)------------------------------
% 0.22/0.59  % (8192)------------------------------
% 0.22/0.62  % (8184)Refutation found. Thanks to Tanya!
% 0.22/0.62  % SZS status Theorem for theBenchmark
% 0.22/0.62  % SZS output start Proof for theBenchmark
% 0.22/0.62  fof(f783,plain,(
% 0.22/0.62    $false),
% 0.22/0.62    inference(avatar_sat_refutation,[],[f117,f118,f141,f205,f349,f782])).
% 0.22/0.62  fof(f782,plain,(
% 0.22/0.62    ~spl11_1 | spl11_2 | spl11_3 | ~spl11_4),
% 0.22/0.62    inference(avatar_contradiction_clause,[],[f781])).
% 0.22/0.62  fof(f781,plain,(
% 0.22/0.62    $false | (~spl11_1 | spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(subsumption_resolution,[],[f780,f68])).
% 0.22/0.62  fof(f68,plain,(
% 0.22/0.62    m1_subset_1(sK6,u1_struct_0(sK4))),
% 0.22/0.62    inference(cnf_transformation,[],[f43])).
% 0.22/0.62  fof(f43,plain,(
% 0.22/0.62    (((~r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,sK6)) & (r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,sK6)) & m1_subset_1(sK6,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4)),
% 0.22/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f39,f42,f41,f40])).
% 0.22/0.62  fof(f40,plain,(
% 0.22/0.62    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1))) | ~r2_orders_2(sK4,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1))) | r2_orders_2(sK4,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) & l1_orders_2(sK4) & v5_orders_2(sK4) & v4_orders_2(sK4) & v3_orders_2(sK4) & ~v2_struct_0(sK4))),
% 0.22/0.62    introduced(choice_axiom,[])).
% 0.22/0.62  fof(f41,plain,(
% 0.22/0.62    ? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1))) | ~r2_orders_2(sK4,X1,X2)) & (r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),X1))) | r2_orders_2(sK4,X1,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(X1,u1_struct_0(sK4))) => (? [X2] : ((~r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,X2)) & (r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) & m1_subset_1(sK5,u1_struct_0(sK4)))),
% 0.22/0.62    introduced(choice_axiom,[])).
% 0.22/0.62  fof(f42,plain,(
% 0.22/0.62    ? [X2] : ((~r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,X2)) & (r2_hidden(X2,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,X2)) & m1_subset_1(X2,u1_struct_0(sK4))) => ((~r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,sK6)) & (r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,sK6)) & m1_subset_1(sK6,u1_struct_0(sK4)))),
% 0.22/0.62    introduced(choice_axiom,[])).
% 0.22/0.62  fof(f39,plain,(
% 0.22/0.62    ? [X0] : (? [X1] : (? [X2] : ((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.62    inference(flattening,[],[f38])).
% 0.22/0.62  fof(f38,plain,(
% 0.22/0.62    ? [X0] : (? [X1] : (? [X2] : (((~r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | ~r2_orders_2(X0,X1,X2)) & (r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) | r2_orders_2(X0,X1,X2))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.62    inference(nnf_transformation,[],[f15])).
% 0.22/0.62  fof(f15,plain,(
% 0.22/0.62    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.62    inference(flattening,[],[f14])).
% 0.22/0.62  fof(f14,plain,(
% 0.22/0.62    ? [X0] : (? [X1] : (? [X2] : ((r2_orders_2(X0,X1,X2) <~> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.62    inference(ennf_transformation,[],[f12])).
% 0.22/0.62  fof(f12,negated_conjecture,(
% 0.22/0.62    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 0.22/0.62    inference(negated_conjecture,[],[f11])).
% 0.22/0.62  fof(f11,conjecture,(
% 0.22/0.62    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r2_orders_2(X0,X1,X2) <=> r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))))),
% 0.22/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_orders_2)).
% 0.22/0.62  fof(f780,plain,(
% 0.22/0.62    ~m1_subset_1(sK6,u1_struct_0(sK4)) | (~spl11_1 | spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(subsumption_resolution,[],[f779,f351])).
% 0.22/0.62  fof(f351,plain,(
% 0.22/0.62    ~sP1(sK4,k2_tarski(sK5,sK5),sK6) | (spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(resolution,[],[f350,f315])).
% 0.22/0.62  fof(f315,plain,(
% 0.22/0.62    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | ~sP1(sK4,k2_tarski(sK5,sK5),X0)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(subsumption_resolution,[],[f313,f237])).
% 0.22/0.62  fof(f237,plain,(
% 0.22/0.62    ( ! [X0] : (sP2(X0,k2_tarski(sK5,sK5),sK4)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(subsumption_resolution,[],[f236,f62])).
% 0.22/0.62  fof(f62,plain,(
% 0.22/0.62    ~v2_struct_0(sK4)),
% 0.22/0.62    inference(cnf_transformation,[],[f43])).
% 0.22/0.62  fof(f236,plain,(
% 0.22/0.62    ( ! [X0] : (sP2(X0,k2_tarski(sK5,sK5),sK4) | v2_struct_0(sK4)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(subsumption_resolution,[],[f235,f63])).
% 0.22/0.62  fof(f63,plain,(
% 0.22/0.62    v3_orders_2(sK4)),
% 0.22/0.62    inference(cnf_transformation,[],[f43])).
% 0.22/0.62  fof(f235,plain,(
% 0.22/0.62    ( ! [X0] : (sP2(X0,k2_tarski(sK5,sK5),sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(subsumption_resolution,[],[f234,f64])).
% 0.22/0.62  fof(f64,plain,(
% 0.22/0.62    v4_orders_2(sK4)),
% 0.22/0.62    inference(cnf_transformation,[],[f43])).
% 0.22/0.62  fof(f234,plain,(
% 0.22/0.62    ( ! [X0] : (sP2(X0,k2_tarski(sK5,sK5),sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(subsumption_resolution,[],[f233,f65])).
% 0.22/0.62  fof(f65,plain,(
% 0.22/0.62    v5_orders_2(sK4)),
% 0.22/0.62    inference(cnf_transformation,[],[f43])).
% 0.22/0.62  fof(f233,plain,(
% 0.22/0.62    ( ! [X0] : (sP2(X0,k2_tarski(sK5,sK5),sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(subsumption_resolution,[],[f224,f66])).
% 0.22/0.62  fof(f66,plain,(
% 0.22/0.62    l1_orders_2(sK4)),
% 0.22/0.62    inference(cnf_transformation,[],[f43])).
% 0.22/0.62  fof(f224,plain,(
% 0.22/0.62    ( ! [X0] : (sP2(X0,k2_tarski(sK5,sK5),sK4) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(resolution,[],[f222,f91])).
% 0.22/0.62  fof(f91,plain,(
% 0.22/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | sP2(X0,X2,X1) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)) )),
% 0.22/0.62    inference(cnf_transformation,[],[f35])).
% 0.22/0.62  fof(f35,plain,(
% 0.22/0.62    ! [X0,X1,X2] : (sP2(X0,X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.62    inference(definition_folding,[],[f27,f34,f33])).
% 0.22/0.62  fof(f33,plain,(
% 0.22/0.62    ! [X1,X2,X0] : (sP1(X1,X2,X0) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))))),
% 0.22/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.22/0.62  fof(f34,plain,(
% 0.22/0.62    ! [X0,X2,X1] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> sP1(X1,X2,X0)) | ~sP2(X0,X2,X1))),
% 0.22/0.62    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.22/0.62  fof(f27,plain,(
% 0.22/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1))),
% 0.22/0.62    inference(flattening,[],[f26])).
% 0.22/0.62  fof(f26,plain,(
% 0.22/0.62    ! [X0,X1,X2] : ((r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : ((r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2)) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1)))),
% 0.22/0.62    inference(ennf_transformation,[],[f7])).
% 0.22/0.62  fof(f7,axiom,(
% 0.22/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) & l1_orders_2(X1) & v5_orders_2(X1) & v4_orders_2(X1) & v3_orders_2(X1) & ~v2_struct_0(X1)) => (r2_hidden(X0,a_2_0_orders_2(X1,X2)) <=> ? [X3] : (! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => (r2_hidden(X4,X2) => r2_orders_2(X1,X4,X3))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1)))))),
% 0.22/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fraenkel_a_2_0_orders_2)).
% 0.22/0.62  fof(f222,plain,(
% 0.22/0.62    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | (spl11_3 | ~spl11_4)),
% 0.22/0.62    inference(subsumption_resolution,[],[f221,f135])).
% 0.22/0.62  fof(f135,plain,(
% 0.22/0.62    ~v1_xboole_0(u1_struct_0(sK4)) | spl11_3),
% 0.22/0.62    inference(avatar_component_clause,[],[f134])).
% 0.22/0.62  fof(f134,plain,(
% 0.22/0.62    spl11_3 <=> v1_xboole_0(u1_struct_0(sK4))),
% 0.22/0.62    introduced(avatar_definition,[new_symbols(naming,[spl11_3])])).
% 0.22/0.62  fof(f221,plain,(
% 0.22/0.62    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | v1_xboole_0(u1_struct_0(sK4)) | ~spl11_4),
% 0.22/0.62    inference(subsumption_resolution,[],[f218,f67])).
% 0.22/0.62  fof(f67,plain,(
% 0.22/0.62    m1_subset_1(sK5,u1_struct_0(sK4))),
% 0.22/0.62    inference(cnf_transformation,[],[f43])).
% 0.22/0.63  fof(f218,plain,(
% 0.22/0.63    m1_subset_1(k2_tarski(sK5,sK5),k1_zfmisc_1(u1_struct_0(sK4))) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | v1_xboole_0(u1_struct_0(sK4)) | ~spl11_4),
% 0.22/0.63    inference(superposition,[],[f82,f140])).
% 0.22/0.63  fof(f140,plain,(
% 0.22/0.63    k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) | ~spl11_4),
% 0.22/0.63    inference(avatar_component_clause,[],[f138])).
% 0.22/0.63  fof(f138,plain,(
% 0.22/0.63    spl11_4 <=> k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5)),
% 0.22/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_4])])).
% 0.22/0.63  fof(f82,plain,(
% 0.22/0.63    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f25])).
% 0.22/0.63  fof(f25,plain,(
% 0.22/0.63    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.63    inference(flattening,[],[f24])).
% 0.22/0.63  fof(f24,plain,(
% 0.22/0.63    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.63    inference(ennf_transformation,[],[f6])).
% 0.22/0.63  fof(f6,axiom,(
% 0.22/0.63    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.22/0.63  fof(f313,plain,(
% 0.22/0.63    ( ! [X0] : (r2_hidden(X0,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | ~sP1(sK4,k2_tarski(sK5,sK5),X0) | ~sP2(X0,k2_tarski(sK5,sK5),sK4)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(superposition,[],[f84,f232])).
% 0.22/0.63  fof(f232,plain,(
% 0.22/0.63    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f231,f62])).
% 0.22/0.63  fof(f231,plain,(
% 0.22/0.63    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | v2_struct_0(sK4) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f230,f63])).
% 0.22/0.63  fof(f230,plain,(
% 0.22/0.63    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f229,f64])).
% 0.22/0.63  fof(f229,plain,(
% 0.22/0.63    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f228,f65])).
% 0.22/0.63  fof(f228,plain,(
% 0.22/0.63    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f223,f66])).
% 0.22/0.63  fof(f223,plain,(
% 0.22/0.63    k1_orders_2(sK4,k2_tarski(sK5,sK5)) = a_2_0_orders_2(sK4,k2_tarski(sK5,sK5)) | ~l1_orders_2(sK4) | ~v5_orders_2(sK4) | ~v4_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(resolution,[],[f222,f72])).
% 0.22/0.63  fof(f72,plain,(
% 0.22/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f17])).
% 0.22/0.63  fof(f17,plain,(
% 0.22/0.63    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.63    inference(flattening,[],[f16])).
% 0.22/0.63  fof(f16,plain,(
% 0.22/0.63    ! [X0] : (! [X1] : (k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.63    inference(ennf_transformation,[],[f5])).
% 0.22/0.63  fof(f5,axiom,(
% 0.22/0.63    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)))),
% 0.22/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d12_orders_2)).
% 0.22/0.63  fof(f84,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f50])).
% 0.22/0.63  fof(f50,plain,(
% 0.22/0.63    ! [X0,X1,X2] : (((r2_hidden(X0,a_2_0_orders_2(X2,X1)) | ~sP1(X2,X1,X0)) & (sP1(X2,X1,X0) | ~r2_hidden(X0,a_2_0_orders_2(X2,X1)))) | ~sP2(X0,X1,X2))),
% 0.22/0.63    inference(rectify,[],[f49])).
% 0.22/0.63  fof(f49,plain,(
% 0.22/0.63    ! [X0,X2,X1] : (((r2_hidden(X0,a_2_0_orders_2(X1,X2)) | ~sP1(X1,X2,X0)) & (sP1(X1,X2,X0) | ~r2_hidden(X0,a_2_0_orders_2(X1,X2)))) | ~sP2(X0,X2,X1))),
% 0.22/0.63    inference(nnf_transformation,[],[f34])).
% 0.22/0.63  fof(f350,plain,(
% 0.22/0.63    ~r2_hidden(sK6,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | (spl11_2 | ~spl11_4)),
% 0.22/0.63    inference(forward_demodulation,[],[f116,f140])).
% 0.22/0.63  fof(f116,plain,(
% 0.22/0.63    ~r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | spl11_2),
% 0.22/0.63    inference(avatar_component_clause,[],[f114])).
% 0.22/0.63  fof(f114,plain,(
% 0.22/0.63    spl11_2 <=> r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5)))),
% 0.22/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_2])])).
% 0.22/0.63  fof(f779,plain,(
% 0.22/0.63    sP1(sK4,k2_tarski(sK5,sK5),sK6) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | (~spl11_1 | spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f755,f111])).
% 0.22/0.63  fof(f111,plain,(
% 0.22/0.63    r2_orders_2(sK4,sK5,sK6) | ~spl11_1),
% 0.22/0.63    inference(avatar_component_clause,[],[f110])).
% 0.22/0.63  fof(f110,plain,(
% 0.22/0.63    spl11_1 <=> r2_orders_2(sK4,sK5,sK6)),
% 0.22/0.63    introduced(avatar_definition,[new_symbols(naming,[spl11_1])])).
% 0.22/0.63  fof(f755,plain,(
% 0.22/0.63    ~r2_orders_2(sK4,sK5,sK6) | sP1(sK4,k2_tarski(sK5,sK5),sK6) | ~m1_subset_1(sK6,u1_struct_0(sK4)) | (spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(superposition,[],[f103,f737])).
% 0.22/0.63  fof(f737,plain,(
% 0.22/0.63    sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6) | (spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f736,f68])).
% 0.22/0.63  fof(f736,plain,(
% 0.22/0.63    ~m1_subset_1(sK6,u1_struct_0(sK4)) | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6) | (spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(duplicate_literal_removal,[],[f725])).
% 0.22/0.63  fof(f725,plain,(
% 0.22/0.63    ~m1_subset_1(sK6,u1_struct_0(sK4)) | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6) | sK5 = sK8(sK4,k2_tarski(sK5,sK5),sK6) | (spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(resolution,[],[f165,f351])).
% 0.22/0.63  fof(f165,plain,(
% 0.22/0.63    ( ! [X2,X0,X3,X1] : (sP1(X0,k2_tarski(X1,X2),X3) | ~m1_subset_1(X3,u1_struct_0(X0)) | sK8(X0,k2_tarski(X1,X2),X3) = X1 | sK8(X0,k2_tarski(X1,X2),X3) = X2) )),
% 0.22/0.63    inference(resolution,[],[f104,f149])).
% 0.22/0.63  fof(f149,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X1,k2_tarski(X0,X2)) | X0 = X1 | X1 = X2) )),
% 0.22/0.63    inference(resolution,[],[f93,f108])).
% 0.22/0.63  fof(f108,plain,(
% 0.22/0.63    ( ! [X0,X1] : (sP3(X1,X0,k2_tarski(X0,X1))) )),
% 0.22/0.63    inference(equality_resolution,[],[f99])).
% 0.22/0.63  fof(f99,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (sP3(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 0.22/0.63    inference(cnf_transformation,[],[f61])).
% 0.22/0.63  fof(f61,plain,(
% 0.22/0.63    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP3(X1,X0,X2)) & (sP3(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 0.22/0.63    inference(nnf_transformation,[],[f37])).
% 0.22/0.63  fof(f37,plain,(
% 0.22/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP3(X1,X0,X2))),
% 0.22/0.63    inference(definition_folding,[],[f1,f36])).
% 0.22/0.63  fof(f36,plain,(
% 0.22/0.63    ! [X1,X0,X2] : (sP3(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.22/0.63  fof(f1,axiom,(
% 0.22/0.63    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 0.22/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).
% 0.22/0.63  fof(f93,plain,(
% 0.22/0.63    ( ! [X4,X2,X0,X1] : (~sP3(X0,X1,X2) | X1 = X4 | ~r2_hidden(X4,X2) | X0 = X4) )),
% 0.22/0.63    inference(cnf_transformation,[],[f60])).
% 0.22/0.63  fof(f60,plain,(
% 0.22/0.63    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | (((sK10(X0,X1,X2) != X0 & sK10(X0,X1,X2) != X1) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sK10(X0,X1,X2) = X0 | sK10(X0,X1,X2) = X1 | r2_hidden(sK10(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.22/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10])],[f58,f59])).
% 0.22/0.63  fof(f59,plain,(
% 0.22/0.63    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK10(X0,X1,X2) != X0 & sK10(X0,X1,X2) != X1) | ~r2_hidden(sK10(X0,X1,X2),X2)) & (sK10(X0,X1,X2) = X0 | sK10(X0,X1,X2) = X1 | r2_hidden(sK10(X0,X1,X2),X2))))),
% 0.22/0.63    introduced(choice_axiom,[])).
% 0.22/0.63  fof(f58,plain,(
% 0.22/0.63    ! [X0,X1,X2] : ((sP3(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP3(X0,X1,X2)))),
% 0.22/0.63    inference(rectify,[],[f57])).
% 0.22/0.63  fof(f57,plain,(
% 0.22/0.63    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP3(X1,X0,X2)))),
% 0.22/0.63    inference(flattening,[],[f56])).
% 0.22/0.63  fof(f56,plain,(
% 0.22/0.63    ! [X1,X0,X2] : ((sP3(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP3(X1,X0,X2)))),
% 0.22/0.63    inference(nnf_transformation,[],[f36])).
% 0.22/0.63  fof(f104,plain,(
% 0.22/0.63    ( ! [X0,X3,X1] : (r2_hidden(sK8(X0,X1,X3),X1) | sP1(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.63    inference(equality_resolution,[],[f89])).
% 0.22/0.63  fof(f89,plain,(
% 0.22/0.63    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2) | r2_hidden(sK8(X0,X1,X3),X1) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.63    inference(cnf_transformation,[],[f55])).
% 0.22/0.63  fof(f55,plain,(
% 0.22/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : ((~r2_orders_2(X0,sK8(X0,X1,X3),X3) & r2_hidden(sK8(X0,X1,X3),X1) & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & ((! [X6] : (r2_orders_2(X0,X6,sK9(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))) | ~sP1(X0,X1,X2)))),
% 0.22/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9])],[f52,f54,f53])).
% 0.22/0.63  fof(f53,plain,(
% 0.22/0.63    ! [X3,X1,X0] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) => (~r2_orders_2(X0,sK8(X0,X1,X3),X3) & r2_hidden(sK8(X0,X1,X3),X1) & m1_subset_1(sK8(X0,X1,X3),u1_struct_0(X0))))),
% 0.22/0.63    introduced(choice_axiom,[])).
% 0.22/0.63  fof(f54,plain,(
% 0.22/0.63    ! [X2,X1,X0] : (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) => (! [X6] : (r2_orders_2(X0,X6,sK9(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & sK9(X0,X1,X2) = X2 & m1_subset_1(sK9(X0,X1,X2),u1_struct_0(X0))))),
% 0.22/0.63    introduced(choice_axiom,[])).
% 0.22/0.63  fof(f52,plain,(
% 0.22/0.63    ! [X0,X1,X2] : ((sP1(X0,X1,X2) | ! [X3] : (? [X4] : (~r2_orders_2(X0,X4,X3) & r2_hidden(X4,X1) & m1_subset_1(X4,u1_struct_0(X0))) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0)))) & (? [X5] : (! [X6] : (r2_orders_2(X0,X6,X5) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0))) & X2 = X5 & m1_subset_1(X5,u1_struct_0(X0))) | ~sP1(X0,X1,X2)))),
% 0.22/0.63    inference(rectify,[],[f51])).
% 0.22/0.63  fof(f51,plain,(
% 0.22/0.63    ! [X1,X2,X0] : ((sP1(X1,X2,X0) | ! [X3] : (? [X4] : (~r2_orders_2(X1,X4,X3) & r2_hidden(X4,X2) & m1_subset_1(X4,u1_struct_0(X1))) | X0 != X3 | ~m1_subset_1(X3,u1_struct_0(X1)))) & (? [X3] : (! [X4] : (r2_orders_2(X1,X4,X3) | ~r2_hidden(X4,X2) | ~m1_subset_1(X4,u1_struct_0(X1))) & X0 = X3 & m1_subset_1(X3,u1_struct_0(X1))) | ~sP1(X1,X2,X0)))),
% 0.22/0.63    inference(nnf_transformation,[],[f33])).
% 0.22/0.63  fof(f103,plain,(
% 0.22/0.63    ( ! [X0,X3,X1] : (~r2_orders_2(X0,sK8(X0,X1,X3),X3) | sP1(X0,X1,X3) | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.63    inference(equality_resolution,[],[f90])).
% 0.22/0.63  fof(f90,plain,(
% 0.22/0.63    ( ! [X2,X0,X3,X1] : (sP1(X0,X1,X2) | ~r2_orders_2(X0,sK8(X0,X1,X3),X3) | X2 != X3 | ~m1_subset_1(X3,u1_struct_0(X0))) )),
% 0.22/0.63    inference(cnf_transformation,[],[f55])).
% 0.22/0.63  fof(f349,plain,(
% 0.22/0.63    spl11_1 | ~spl11_2 | spl11_3 | ~spl11_4),
% 0.22/0.63    inference(avatar_contradiction_clause,[],[f348])).
% 0.22/0.63  fof(f348,plain,(
% 0.22/0.63    $false | (spl11_1 | ~spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f343,f112])).
% 0.22/0.63  fof(f112,plain,(
% 0.22/0.63    ~r2_orders_2(sK4,sK5,sK6) | spl11_1),
% 0.22/0.63    inference(avatar_component_clause,[],[f110])).
% 0.22/0.63  fof(f343,plain,(
% 0.22/0.63    r2_orders_2(sK4,sK5,sK6) | (~spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(resolution,[],[f341,f122])).
% 0.22/0.63  fof(f122,plain,(
% 0.22/0.63    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X0,X1))) )),
% 0.22/0.63    inference(resolution,[],[f107,f108])).
% 0.22/0.63  fof(f107,plain,(
% 0.22/0.63    ( ! [X4,X2,X0] : (~sP3(X0,X4,X2) | r2_hidden(X4,X2)) )),
% 0.22/0.63    inference(equality_resolution,[],[f94])).
% 0.22/0.63  fof(f94,plain,(
% 0.22/0.63    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X1 != X4 | ~sP3(X0,X1,X2)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f60])).
% 0.22/0.63  fof(f341,plain,(
% 0.22/0.63    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK5,sK5)) | r2_orders_2(sK4,X1,sK6)) ) | (~spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f340,f220])).
% 0.22/0.63  fof(f220,plain,(
% 0.22/0.63    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK5,sK5)) | m1_subset_1(X0,u1_struct_0(sK4))) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f219,f67])).
% 0.22/0.63  fof(f219,plain,(
% 0.22/0.63    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK5,sK5)) | m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f217,f135])).
% 0.22/0.63  fof(f217,plain,(
% 0.22/0.63    ( ! [X0] : (~r2_hidden(X0,k2_tarski(sK5,sK5)) | v1_xboole_0(u1_struct_0(sK4)) | m1_subset_1(X0,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK4))) ) | ~spl11_4),
% 0.22/0.63    inference(superposition,[],[f124,f140])).
% 0.22/0.63  fof(f124,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X2,k6_domain_1(X1,X0)) | v1_xboole_0(X1) | m1_subset_1(X2,X1) | ~m1_subset_1(X0,X1)) )),
% 0.22/0.63    inference(resolution,[],[f82,f92])).
% 0.22/0.63  fof(f92,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f29])).
% 0.22/0.63  fof(f29,plain,(
% 0.22/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.63    inference(flattening,[],[f28])).
% 0.22/0.63  fof(f28,plain,(
% 0.22/0.63    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.63    inference(ennf_transformation,[],[f3])).
% 0.22/0.63  fof(f3,axiom,(
% 0.22/0.63    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.63  fof(f340,plain,(
% 0.22/0.63    ( ! [X1] : (r2_orders_2(sK4,X1,sK6) | ~r2_hidden(X1,k2_tarski(sK5,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK4))) ) | (~spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f337,f323])).
% 0.22/0.63  fof(f323,plain,(
% 0.22/0.63    sP1(sK4,k2_tarski(sK5,sK5),sK6) | (~spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(resolution,[],[f316,f216])).
% 0.22/0.63  fof(f216,plain,(
% 0.22/0.63    r2_hidden(sK6,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | (~spl11_2 | ~spl11_4)),
% 0.22/0.63    inference(backward_demodulation,[],[f115,f140])).
% 0.22/0.63  fof(f115,plain,(
% 0.22/0.63    r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~spl11_2),
% 0.22/0.63    inference(avatar_component_clause,[],[f114])).
% 0.22/0.63  fof(f316,plain,(
% 0.22/0.63    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | sP1(sK4,k2_tarski(sK5,sK5),X1)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f314,f237])).
% 0.22/0.63  fof(f314,plain,(
% 0.22/0.63    ( ! [X1] : (~r2_hidden(X1,k1_orders_2(sK4,k2_tarski(sK5,sK5))) | sP1(sK4,k2_tarski(sK5,sK5),X1) | ~sP2(X1,k2_tarski(sK5,sK5),sK4)) ) | (spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(superposition,[],[f83,f232])).
% 0.22/0.63  fof(f83,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (~r2_hidden(X0,a_2_0_orders_2(X2,X1)) | sP1(X2,X1,X0) | ~sP2(X0,X1,X2)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f50])).
% 0.22/0.63  fof(f337,plain,(
% 0.22/0.63    ( ! [X1] : (r2_orders_2(sK4,X1,sK6) | ~r2_hidden(X1,k2_tarski(sK5,sK5)) | ~m1_subset_1(X1,u1_struct_0(sK4)) | ~sP1(sK4,k2_tarski(sK5,sK5),sK6)) ) | (~spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(superposition,[],[f87,f334])).
% 0.22/0.63  fof(f334,plain,(
% 0.22/0.63    sK6 = sK9(sK4,k2_tarski(sK5,sK5),sK6) | (~spl11_2 | spl11_3 | ~spl11_4)),
% 0.22/0.63    inference(resolution,[],[f323,f86])).
% 0.22/0.63  fof(f86,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (~sP1(X0,X1,X2) | sK9(X0,X1,X2) = X2) )),
% 0.22/0.63    inference(cnf_transformation,[],[f55])).
% 0.22/0.63  fof(f87,plain,(
% 0.22/0.63    ( ! [X6,X2,X0,X1] : (r2_orders_2(X0,X6,sK9(X0,X1,X2)) | ~r2_hidden(X6,X1) | ~m1_subset_1(X6,u1_struct_0(X0)) | ~sP1(X0,X1,X2)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f55])).
% 0.22/0.63  fof(f205,plain,(
% 0.22/0.63    ~spl11_3),
% 0.22/0.63    inference(avatar_contradiction_clause,[],[f204])).
% 0.22/0.63  fof(f204,plain,(
% 0.22/0.63    $false | ~spl11_3),
% 0.22/0.63    inference(subsumption_resolution,[],[f203,f136])).
% 0.22/0.63  fof(f136,plain,(
% 0.22/0.63    v1_xboole_0(u1_struct_0(sK4)) | ~spl11_3),
% 0.22/0.63    inference(avatar_component_clause,[],[f134])).
% 0.22/0.63  fof(f203,plain,(
% 0.22/0.63    ~v1_xboole_0(u1_struct_0(sK4))),
% 0.22/0.63    inference(resolution,[],[f187,f163])).
% 0.22/0.63  fof(f163,plain,(
% 0.22/0.63    ( ! [X4,X5,X3] : (~sP0(X4,X5,X3) | ~v1_xboole_0(u1_struct_0(X3))) )),
% 0.22/0.63    inference(duplicate_literal_removal,[],[f162])).
% 0.22/0.63  fof(f162,plain,(
% 0.22/0.63    ( ! [X4,X5,X3] : (~v1_xboole_0(u1_struct_0(X3)) | ~sP0(X4,X5,X3) | ~sP0(X4,X5,X3)) )),
% 0.22/0.63    inference(resolution,[],[f127,f77])).
% 0.22/0.63  fof(f77,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (r2_hidden(X0,sK7(X0,X1,X2)) | ~sP0(X0,X1,X2)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f47])).
% 0.22/0.63  fof(f47,plain,(
% 0.22/0.63    ! [X0,X1,X2] : ((r2_hidden(X0,sK7(X0,X1,X2)) & r2_hidden(X1,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK7(X0,X1,X2),X2)) | ~sP0(X0,X1,X2))),
% 0.22/0.63    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f45,f46])).
% 0.22/0.63  fof(f46,plain,(
% 0.22/0.63    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) => (r2_hidden(X0,sK7(X0,X1,X2)) & r2_hidden(X1,sK7(X0,X1,X2)) & m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(sK7(X0,X1,X2),X2)))),
% 0.22/0.63    introduced(choice_axiom,[])).
% 0.22/0.63  fof(f45,plain,(
% 0.22/0.63    ! [X0,X1,X2] : (? [X3] : (r2_hidden(X0,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) & v6_orders_2(X3,X2)) | ~sP0(X0,X1,X2))),
% 0.22/0.63    inference(rectify,[],[f44])).
% 0.22/0.63  fof(f44,plain,(
% 0.22/0.63    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | ~sP0(X2,X1,X0))),
% 0.22/0.63    inference(nnf_transformation,[],[f31])).
% 0.22/0.63  fof(f31,plain,(
% 0.22/0.63    ! [X2,X1,X0] : (? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | ~sP0(X2,X1,X0))),
% 0.22/0.63    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.22/0.63  fof(f127,plain,(
% 0.22/0.63    ( ! [X6,X4,X7,X5] : (~r2_hidden(X7,sK7(X4,X5,X6)) | ~v1_xboole_0(u1_struct_0(X6)) | ~sP0(X4,X5,X6)) )),
% 0.22/0.63    inference(resolution,[],[f75,f101])).
% 0.22/0.63  fof(f101,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f30])).
% 0.22/0.63  fof(f30,plain,(
% 0.22/0.63    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.63    inference(ennf_transformation,[],[f4])).
% 0.22/0.63  fof(f4,axiom,(
% 0.22/0.63    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.22/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.22/0.63  fof(f75,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (m1_subset_1(sK7(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X2))) | ~sP0(X0,X1,X2)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f47])).
% 0.22/0.63  fof(f187,plain,(
% 0.22/0.63    sP0(sK5,sK5,sK4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f186,f63])).
% 0.22/0.63  fof(f186,plain,(
% 0.22/0.63    sP0(sK5,sK5,sK4) | ~v3_orders_2(sK4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f185,f66])).
% 0.22/0.63  fof(f185,plain,(
% 0.22/0.63    sP0(sK5,sK5,sK4) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f184,f67])).
% 0.22/0.63  fof(f184,plain,(
% 0.22/0.63    sP0(sK5,sK5,sK4) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4)),
% 0.22/0.63    inference(duplicate_literal_removal,[],[f181])).
% 0.22/0.63  fof(f181,plain,(
% 0.22/0.63    sP0(sK5,sK5,sK4) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~m1_subset_1(sK5,u1_struct_0(sK4)) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4)),
% 0.22/0.63    inference(resolution,[],[f79,f157])).
% 0.22/0.63  fof(f157,plain,(
% 0.22/0.63    r1_orders_2(sK4,sK5,sK5)),
% 0.22/0.63    inference(subsumption_resolution,[],[f156,f62])).
% 0.22/0.63  fof(f156,plain,(
% 0.22/0.63    r1_orders_2(sK4,sK5,sK5) | v2_struct_0(sK4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f155,f63])).
% 0.22/0.63  fof(f155,plain,(
% 0.22/0.63    r1_orders_2(sK4,sK5,sK5) | ~v3_orders_2(sK4) | v2_struct_0(sK4)),
% 0.22/0.63    inference(subsumption_resolution,[],[f152,f66])).
% 0.22/0.63  fof(f152,plain,(
% 0.22/0.63    r1_orders_2(sK4,sK5,sK5) | ~l1_orders_2(sK4) | ~v3_orders_2(sK4) | v2_struct_0(sK4)),
% 0.22/0.63    inference(resolution,[],[f73,f67])).
% 0.22/0.63  fof(f73,plain,(
% 0.22/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | r1_orders_2(X0,X1,X1) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f19])).
% 0.22/0.63  fof(f19,plain,(
% 0.22/0.63    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.63    inference(flattening,[],[f18])).
% 0.22/0.63  fof(f18,plain,(
% 0.22/0.63    ! [X0] : (! [X1] : (r1_orders_2(X0,X1,X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.63    inference(ennf_transformation,[],[f9])).
% 0.22/0.63  fof(f9,axiom,(
% 0.22/0.63    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,X1,X1)))),
% 0.22/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_orders_2)).
% 0.22/0.63  fof(f79,plain,(
% 0.22/0.63    ( ! [X2,X0,X1] : (~r1_orders_2(X0,X1,X2) | sP0(X2,X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f48])).
% 0.22/0.63  fof(f48,plain,(
% 0.22/0.63    ! [X0] : (! [X1] : (! [X2] : (((sP0(X2,X1,X0) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X3] : (~r2_hidden(X2,X3) | ~r2_hidden(X1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X3,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.63    inference(rectify,[],[f32])).
% 0.22/0.63  fof(f32,plain,(
% 0.22/0.63    ! [X0] : (! [X1] : (! [X2] : (((sP0(X2,X1,X0) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.63    inference(definition_folding,[],[f21,f31])).
% 0.22/0.63  fof(f21,plain,(
% 0.22/0.63    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0))),
% 0.22/0.63    inference(flattening,[],[f20])).
% 0.22/0.63  fof(f20,plain,(
% 0.22/0.63    ! [X0] : (! [X1] : (! [X2] : (((? [X3] : ((r2_hidden(X2,X3) & r2_hidden(X1,X3)) & (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0))) | (~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2) | ! [X4] : (~r2_hidden(X2,X4) | ~r2_hidden(X1,X4) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~v6_orders_2(X4,X0)))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0)))),
% 0.22/0.63    inference(ennf_transformation,[],[f13])).
% 0.22/0.63  fof(f13,plain,(
% 0.22/0.63    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X4] : (r2_hidden(X2,X4) & r2_hidden(X1,X4) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X4,X0)))))))),
% 0.22/0.63    inference(rectify,[],[f10])).
% 0.22/0.63  fof(f10,axiom,(
% 0.22/0.63    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)) => ~(r2_hidden(X2,X3) & r2_hidden(X1,X3))) & (r1_orders_2(X0,X2,X1) | r1_orders_2(X0,X1,X2))) & ~(~r1_orders_2(X0,X2,X1) & ~r1_orders_2(X0,X1,X2) & ? [X3] : (r2_hidden(X2,X3) & r2_hidden(X1,X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(X3,X0)))))))),
% 0.22/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_orders_2)).
% 0.22/0.63  fof(f141,plain,(
% 0.22/0.63    spl11_3 | spl11_4),
% 0.22/0.63    inference(avatar_split_clause,[],[f128,f138,f134])).
% 0.22/0.63  fof(f128,plain,(
% 0.22/0.63    k6_domain_1(u1_struct_0(sK4),sK5) = k2_tarski(sK5,sK5) | v1_xboole_0(u1_struct_0(sK4))),
% 0.22/0.63    inference(resolution,[],[f102,f67])).
% 0.22/0.63  fof(f102,plain,(
% 0.22/0.63    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 0.22/0.63    inference(definition_unfolding,[],[f81,f71])).
% 0.22/0.63  fof(f71,plain,(
% 0.22/0.63    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f2])).
% 0.22/0.63  fof(f2,axiom,(
% 0.22/0.63    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.22/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.22/0.63  fof(f81,plain,(
% 0.22/0.63    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.22/0.63    inference(cnf_transformation,[],[f23])).
% 0.22/0.63  fof(f23,plain,(
% 0.22/0.63    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.22/0.63    inference(flattening,[],[f22])).
% 0.22/0.63  fof(f22,plain,(
% 0.22/0.63    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.22/0.63    inference(ennf_transformation,[],[f8])).
% 0.22/0.63  fof(f8,axiom,(
% 0.22/0.63    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.22/0.63    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.22/0.63  fof(f118,plain,(
% 0.22/0.63    spl11_1 | spl11_2),
% 0.22/0.63    inference(avatar_split_clause,[],[f69,f114,f110])).
% 0.22/0.63  fof(f69,plain,(
% 0.22/0.63    r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | r2_orders_2(sK4,sK5,sK6)),
% 0.22/0.63    inference(cnf_transformation,[],[f43])).
% 0.22/0.63  fof(f117,plain,(
% 0.22/0.63    ~spl11_1 | ~spl11_2),
% 0.22/0.63    inference(avatar_split_clause,[],[f70,f114,f110])).
% 0.22/0.63  fof(f70,plain,(
% 0.22/0.63    ~r2_hidden(sK6,k1_orders_2(sK4,k6_domain_1(u1_struct_0(sK4),sK5))) | ~r2_orders_2(sK4,sK5,sK6)),
% 0.22/0.63    inference(cnf_transformation,[],[f43])).
% 0.22/0.63  % SZS output end Proof for theBenchmark
% 0.22/0.63  % (8184)------------------------------
% 0.22/0.63  % (8184)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.63  % (8184)Termination reason: Refutation
% 0.22/0.63  
% 0.22/0.63  % (8184)Memory used [KB]: 11257
% 0.22/0.63  % (8184)Time elapsed: 0.183 s
% 0.22/0.63  % (8184)------------------------------
% 0.22/0.63  % (8184)------------------------------
% 1.91/0.64  % (8177)Success in time 0.266 s
%------------------------------------------------------------------------------
