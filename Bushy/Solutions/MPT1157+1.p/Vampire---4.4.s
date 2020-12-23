%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t51_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:22 EDT 2019

% Result     : Theorem 3.57s
% Output     : Refutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 759 expanded)
%              Number of leaves         :   30 ( 246 expanded)
%              Depth                    :   25
%              Number of atoms          :  871 (6282 expanded)
%              Number of equality atoms :   65 ( 164 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f60898,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f147,f197,f363,f366,f903,f59403,f59542,f60325,f60880,f60897])).

fof(f60897,plain,
    ( spl10_23
    | ~ spl10_26
    | spl10_4121 ),
    inference(avatar_contradiction_clause,[],[f60896])).

fof(f60896,plain,
    ( $false
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_4121 ),
    inference(subsumption_resolution,[],[f60895,f85])).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | ~ r2_orders_2(sK0,sK1,sK2) )
    & ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      | r2_orders_2(sK0,sK1,sK2) )
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f61,f64,f63,f62])).

fof(f62,plain,
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
              ( ( ~ r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | ~ r2_orders_2(sK0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
                | r2_orders_2(sK0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK1)))
              | ~ r2_orders_2(X0,sK1,X2) )
            & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK1)))
              | r2_orders_2(X0,sK1,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            | ~ r2_orders_2(X0,X1,X2) )
          & ( r2_hidden(X2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            | r2_orders_2(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_hidden(sK2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | ~ r2_orders_2(X0,X1,sK2) )
        & ( r2_hidden(sK2,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
          | r2_orders_2(X0,X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
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
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',t51_orders_2)).

fof(f60895,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_4121 ),
    inference(subsumption_resolution,[],[f60894,f86])).

fof(f86,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f60894,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_4121 ),
    inference(subsumption_resolution,[],[f60893,f87])).

fof(f87,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f60893,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_4121 ),
    inference(subsumption_resolution,[],[f60892,f88])).

fof(f88,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f60892,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_4121 ),
    inference(subsumption_resolution,[],[f60891,f89])).

fof(f89,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f60891,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_4121 ),
    inference(subsumption_resolution,[],[f60890,f2304])).

fof(f2304,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_23 ),
    inference(resolution,[],[f2303,f90])).

fof(f90,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f2303,plain,
    ( ! [X14] :
        ( ~ m1_subset_1(X14,u1_struct_0(sK0))
        | m1_subset_1(k1_tarski(X14),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl10_23 ),
    inference(resolution,[],[f412,f345])).

fof(f345,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_23 ),
    inference(avatar_component_clause,[],[f344])).

fof(f344,plain,
    ( spl10_23
  <=> ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_23])])).

fof(f412,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f410])).

fof(f410,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(superposition,[],[f105,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',redefinition_k6_domain_1)).

fof(f105,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',dt_k6_domain_1)).

fof(f60890,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_26
    | ~ spl10_4121 ),
    inference(subsumption_resolution,[],[f60889,f362])).

fof(f362,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl10_26
  <=> r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f60889,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4121 ),
    inference(superposition,[],[f59393,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',d12_orders_2)).

fof(f59393,plain,
    ( ~ r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl10_4121 ),
    inference(avatar_component_clause,[],[f59392])).

fof(f59392,plain,
    ( spl10_4121
  <=> ~ r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4121])])).

fof(f60880,plain,
    ( spl10_1
    | spl10_23
    | ~ spl10_4120 ),
    inference(avatar_contradiction_clause,[],[f60879])).

fof(f60879,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_23
    | ~ spl10_4120 ),
    inference(subsumption_resolution,[],[f60878,f128])).

fof(f128,plain,(
    ! [X3] : r2_hidden(X3,k1_tarski(X3)) ),
    inference(equality_resolution,[],[f127])).

fof(f127,plain,(
    ! [X3,X1] :
      ( r2_hidden(X3,X1)
      | k1_tarski(X3) != X1 ) ),
    inference(equality_resolution,[],[f109])).

fof(f109,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | X0 != X3
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5])],[f72,f73])).

fof(f73,plain,(
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

fof(f72,plain,(
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
    inference(rectify,[],[f71])).

fof(f71,plain,(
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
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',d1_tarski)).

fof(f60878,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl10_1
    | ~ spl10_23
    | ~ spl10_4120 ),
    inference(subsumption_resolution,[],[f60875,f2304])).

fof(f60875,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ spl10_1
    | ~ spl10_4120 ),
    inference(resolution,[],[f60332,f59396])).

fof(f59396,plain,
    ( r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl10_4120 ),
    inference(avatar_component_clause,[],[f59395])).

fof(f59395,plain,
    ( spl10_4120
  <=> r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4120])])).

fof(f60332,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,a_2_0_orders_2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f139,f2279])).

fof(f2279,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f2278,f85])).

fof(f2278,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2277,f86])).

fof(f2277,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2276,f87])).

fof(f2276,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2275,f88])).

fof(f2275,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2266,f89])).

fof(f2266,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2265])).

fof(f2265,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X2,X0)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(superposition,[],[f2170,f117])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( sK7(X0,X1,X2) = X0
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK6(X1,X2,X3),X3)
                & r2_hidden(sK6(X1,X2,X3),X2)
                & m1_subset_1(sK6(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK7(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK7(X0,X1,X2) = X0
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7])],[f77,f79,f78])).

fof(f78,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK6(X1,X2,X3),X3)
        & r2_hidden(sK6(X1,X2,X3),X2)
        & m1_subset_1(sK6(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK7(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK7(X0,X1,X2) = X0
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X4,X3)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X6,X5)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
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
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',fraenkel_a_2_0_orders_2)).

fof(f2170,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X0,sK7(X2,sK0,X1))
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f2169,f85])).

fof(f2169,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK7(X2,sK0,X1))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2168,f86])).

fof(f2168,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK7(X2,sK0,X1))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2167,f87])).

fof(f2167,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X0,sK7(X2,sK0,X1))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2166,f89])).

fof(f2166,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | r2_orders_2(sK0,X0,sK7(X2,sK0,X1))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2149,f88])).

fof(f2149,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r2_orders_2(X1,X6,sK7(X0,X1,X2))
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f118,f123])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',t4_subset)).

fof(f118,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,X6,sK7(X0,X1,X2))
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f139,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | ~ spl10_1 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl10_1
  <=> ~ r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_1])])).

fof(f60325,plain,
    ( spl10_4120
    | ~ spl10_1
    | spl10_23
    | ~ spl10_4122 ),
    inference(avatar_split_clause,[],[f60324,f59401,f344,f138,f59395])).

fof(f59401,plain,
    ( spl10_4122
  <=> r2_hidden(sK6(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4122])])).

fof(f60324,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl10_23
    | ~ spl10_4122 ),
    inference(subsumption_resolution,[],[f60323,f85])).

fof(f60323,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_4122 ),
    inference(subsumption_resolution,[],[f60322,f86])).

fof(f60322,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_4122 ),
    inference(subsumption_resolution,[],[f60321,f87])).

fof(f60321,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_4122 ),
    inference(subsumption_resolution,[],[f60320,f88])).

fof(f60320,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_4122 ),
    inference(subsumption_resolution,[],[f60319,f89])).

fof(f60319,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_4122 ),
    inference(subsumption_resolution,[],[f60318,f2304])).

fof(f60318,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4122 ),
    inference(subsumption_resolution,[],[f60305,f91])).

fof(f91,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f60305,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4122 ),
    inference(superposition,[],[f130,f60248])).

fof(f60248,plain,
    ( sK1 = sK6(sK0,k1_tarski(sK1),sK2)
    | ~ spl10_4122 ),
    inference(resolution,[],[f59402,f129])).

fof(f129,plain,(
    ! [X0,X3] :
      ( ~ r2_hidden(X3,k1_tarski(X0))
      | X0 = X3 ) ),
    inference(equality_resolution,[],[f108])).

fof(f108,plain,(
    ! [X0,X3,X1] :
      ( X0 = X3
      | ~ r2_hidden(X3,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f59402,plain,
    ( r2_hidden(sK6(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | ~ spl10_4122 ),
    inference(avatar_component_clause,[],[f59401])).

fof(f130,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_orders_2(X1,sK6(X1,X2,X3),X3)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f121])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ r2_orders_2(X1,sK6(X1,X2,X3),X3)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f59542,plain,
    ( spl10_23
    | spl10_27
    | ~ spl10_4120 ),
    inference(avatar_contradiction_clause,[],[f59541])).

fof(f59541,plain,
    ( $false
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_4120 ),
    inference(subsumption_resolution,[],[f59540,f85])).

fof(f59540,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_4120 ),
    inference(subsumption_resolution,[],[f59539,f86])).

fof(f59539,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_4120 ),
    inference(subsumption_resolution,[],[f59538,f87])).

fof(f59538,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_4120 ),
    inference(subsumption_resolution,[],[f59537,f88])).

fof(f59537,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_4120 ),
    inference(subsumption_resolution,[],[f59536,f89])).

fof(f59536,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_4120 ),
    inference(subsumption_resolution,[],[f59535,f2304])).

fof(f59535,plain,
    ( ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_27
    | ~ spl10_4120 ),
    inference(subsumption_resolution,[],[f59513,f359])).

fof(f359,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl10_27
  <=> ~ r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f59513,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4120 ),
    inference(superposition,[],[f59396,f97])).

fof(f59403,plain,
    ( spl10_4120
    | spl10_4122
    | spl10_5 ),
    inference(avatar_split_clause,[],[f59359,f169,f59401,f59395])).

fof(f169,plain,
    ( spl10_5
  <=> u1_struct_0(sK0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f59359,plain,
    ( r2_hidden(sK6(sK0,k1_tarski(sK1),sK2),k1_tarski(sK1))
    | r2_hidden(sK2,a_2_0_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl10_5 ),
    inference(resolution,[],[f13696,f91])).

fof(f13696,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,k1_tarski(sK1),X0),k1_tarski(sK1))
        | r2_hidden(X0,a_2_0_orders_2(sK0,k1_tarski(sK1))) )
    | ~ spl10_5 ),
    inference(resolution,[],[f7834,f90])).

fof(f7834,plain,
    ( ! [X10,X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,k1_tarski(X9),X10),k1_tarski(X9))
        | r2_hidden(X10,a_2_0_orders_2(sK0,k1_tarski(X9))) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f7828,f170])).

fof(f170,plain,
    ( u1_struct_0(sK0) != o_0_0_xboole_0
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f169])).

fof(f7828,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,k1_tarski(X9),X10),k1_tarski(X9))
      | r2_hidden(X10,a_2_0_orders_2(sK0,k1_tarski(X9))) ) ),
    inference(resolution,[],[f2300,f857])).

fof(f857,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,X0,X1),X0)
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f856,f85])).

fof(f856,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f855,f86])).

fof(f855,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f854,f87])).

fof(f854,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f853,f89])).

fof(f853,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | r2_hidden(X1,a_2_0_orders_2(sK0,X0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f131,f88])).

fof(f131,plain,(
    ! [X2,X3,X1] :
      ( ~ v5_orders_2(X1)
      | r2_hidden(sK6(X1,X2,X3),X2)
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r2_hidden(X3,a_2_0_orders_2(X1,X2))
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | r2_hidden(sK6(X1,X2,X3),X2)
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f2300,plain,(
    ! [X8,X7] :
      ( m1_subset_1(k1_tarski(X7),k1_zfmisc_1(X8))
      | ~ m1_subset_1(X7,X8)
      | o_0_0_xboole_0 = X8 ) ),
    inference(resolution,[],[f412,f149])).

fof(f149,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f148,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',t6_boole)).

fof(f148,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f96,f94])).

fof(f94,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',dt_o_0_0_xboole_0)).

fof(f903,plain,
    ( spl10_5
    | ~ spl10_22 ),
    inference(avatar_contradiction_clause,[],[f902])).

fof(f902,plain,
    ( $false
    | ~ spl10_5
    | ~ spl10_22 ),
    inference(subsumption_resolution,[],[f899,f170])).

fof(f899,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl10_22 ),
    inference(resolution,[],[f348,f149])).

fof(f348,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_22 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl10_22
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_22])])).

fof(f366,plain,
    ( spl10_22
    | ~ spl10_27
    | spl10_3 ),
    inference(avatar_split_clause,[],[f365,f144,f358,f347])).

fof(f144,plain,
    ( spl10_3
  <=> ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f365,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f364,f90])).

fof(f364,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_3 ),
    inference(superposition,[],[f145,f104])).

fof(f145,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f363,plain,
    ( spl10_22
    | spl10_26
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f356,f141,f361,f347])).

fof(f141,plain,
    ( spl10_2
  <=> r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f356,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f341,f90])).

fof(f341,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_2 ),
    inference(superposition,[],[f142,f104])).

fof(f142,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl10_2 ),
    inference(avatar_component_clause,[],[f141])).

fof(f197,plain,(
    ~ spl10_4 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f195,f89])).

fof(f195,plain,
    ( ~ l1_orders_2(sK0)
    | ~ spl10_4 ),
    inference(resolution,[],[f194,f95])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',dt_l1_orders_2)).

fof(f194,plain,
    ( ~ l1_struct_0(sK0)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f193,f85])).

fof(f193,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4 ),
    inference(subsumption_resolution,[],[f192,f94])).

fof(f192,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_4 ),
    inference(superposition,[],[f98,f173])).

fof(f173,plain,
    ( u1_struct_0(sK0) = o_0_0_xboole_0
    | ~ spl10_4 ),
    inference(avatar_component_clause,[],[f172])).

fof(f172,plain,
    ( spl10_4
  <=> u1_struct_0(sK0) = o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_4])])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/orders_2__t51_orders_2.p',fc2_struct_0)).

fof(f147,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f92,f141,f135])).

fof(f135,plain,
    ( spl10_0
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f92,plain,
    ( r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f146,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f93,f144,f138])).

fof(f93,plain,
    ( ~ r2_hidden(sK2,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
