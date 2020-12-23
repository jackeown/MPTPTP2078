%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : orders_2__t52_orders_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:37:22 EDT 2019

% Result     : Theorem 4.35s
% Output     : Refutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :  180 ( 761 expanded)
%              Number of leaves         :   30 ( 244 expanded)
%              Depth                    :   25
%              Number of atoms          :  889 (6298 expanded)
%              Number of equality atoms :   65 ( 164 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f106080,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f146,f147,f197,f363,f366,f903,f105121,f105248,f105359,f105381,f106077])).

fof(f106077,plain,
    ( spl10_1
    | spl10_23
    | ~ spl10_6248 ),
    inference(avatar_contradiction_clause,[],[f106076])).

fof(f106076,plain,
    ( $false
    | ~ spl10_1
    | ~ spl10_23
    | ~ spl10_6248 ),
    inference(subsumption_resolution,[],[f106075,f128])).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',d1_tarski)).

fof(f106075,plain,
    ( ~ r2_hidden(sK2,k1_tarski(sK2))
    | ~ spl10_1
    | ~ spl10_23
    | ~ spl10_6248 ),
    inference(subsumption_resolution,[],[f106064,f2305])).

fof(f2305,plain,
    ( m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl10_23 ),
    inference(resolution,[],[f2303,f91])).

fof(f91,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      | ~ r2_orders_2(sK0,sK1,sK2) )
    & ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
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
              ( ( ~ r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
                | ~ r2_orders_2(sK0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
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
              ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | ~ r2_orders_2(X0,X1,X2) )
              & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
                | r2_orders_2(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( ( ~ r2_hidden(sK1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ r2_orders_2(X0,sK1,X2) )
            & ( r2_hidden(sK1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | r2_orders_2(X0,sK1,X2) )
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK1,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
            | ~ r2_orders_2(X0,X1,X2) )
          & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2)))
            | r2_orders_2(X0,X1,X2) )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK2)))
          | ~ r2_orders_2(X0,X1,sK2) )
        & ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),sK2)))
          | r2_orders_2(X0,X1,sK2) )
        & m1_subset_1(sK2,u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,(
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
                <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
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
              <=> r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',t52_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',redefinition_k6_domain_1)).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',dt_k6_domain_1)).

fof(f106064,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k1_tarski(sK2))
    | ~ spl10_1
    | ~ spl10_6248 ),
    inference(resolution,[],[f105114,f105374])).

fof(f105374,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,a_2_1_orders_2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X0) )
    | ~ spl10_1 ),
    inference(resolution,[],[f139,f2279])).

fof(f2279,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X0,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1) ) ),
    inference(subsumption_resolution,[],[f2278,f85])).

fof(f85,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f2278,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X0,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2277,f86])).

fof(f86,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f2277,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X0,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2276,f87])).

fof(f87,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f2276,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X0,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2275,f88])).

fof(f88,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f2275,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X0,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2266,f89])).

fof(f89,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f2266,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,X0,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
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
      ( r2_orders_2(sK0,X0,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X0,a_2_1_orders_2(sK0,X1))
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
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f80,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,X3,sK6(X1,X2,X3))
                & r2_hidden(sK6(X1,X2,X3),X2)
                & m1_subset_1(sK6(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,sK7(X0,X1,X2),X6)
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK7(X0,X1,X2) = X0
            & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
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
          ( ~ r2_orders_2(X1,X3,X4)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,X3,sK6(X1,X2,X3))
        & r2_hidden(sK6(X1,X2,X3),X2)
        & m1_subset_1(sK6(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X5,X6)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,sK7(X0,X1,X2),X6)
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK7(X0,X1,X2) = X0
        & m1_subset_1(sK7(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f77,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
          | ! [X3] :
              ( ? [X4] :
                  ( ~ r2_orders_2(X1,X3,X4)
                  & r2_hidden(X4,X2)
                  & m1_subset_1(X4,u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ? [X5] :
              ( ! [X6] :
                  ( r2_orders_2(X1,X5,X6)
                  | ~ r2_hidden(X6,X2)
                  | ~ m1_subset_1(X6,u1_struct_0(X1)) )
              & X0 = X5
              & m1_subset_1(X5,u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(rectify,[],[f76])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
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
          | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f54,plain,(
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
    inference(flattening,[],[f53])).

fof(f53,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',fraenkel_a_2_1_orders_2)).

fof(f2170,plain,(
    ! [X2,X0,X1] :
      ( r2_orders_2(sK0,sK7(X2,sK0,X1),X0)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(subsumption_resolution,[],[f2169,f85])).

fof(f2169,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK7(X2,sK0,X1),X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2168,f86])).

fof(f2168,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK7(X2,sK0,X1),X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2167,f87])).

fof(f2167,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,sK7(X2,sK0,X1),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f2166,f89])).

fof(f2166,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X2,a_2_1_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_orders_2(sK0)
      | r2_orders_2(sK0,sK7(X2,sK0,X1),X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f2149,f88])).

fof(f2149,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ v5_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | r2_orders_2(X1,sK7(X0,X1,X2),X6)
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',t4_subset)).

fof(f118,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_orders_2(X1,sK7(X0,X1,X2),X6)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_1_orders_2(X1,X2))
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

fof(f105114,plain,
    ( r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ spl10_6248 ),
    inference(avatar_component_clause,[],[f105113])).

fof(f105113,plain,
    ( spl10_6248
  <=> r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6248])])).

fof(f105381,plain,
    ( spl10_23
    | ~ spl10_26
    | spl10_6249 ),
    inference(avatar_contradiction_clause,[],[f105380])).

fof(f105380,plain,
    ( $false
    | ~ spl10_23
    | ~ spl10_26
    | ~ spl10_6249 ),
    inference(subsumption_resolution,[],[f105373,f362])).

fof(f362,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ spl10_26 ),
    inference(avatar_component_clause,[],[f361])).

fof(f361,plain,
    ( spl10_26
  <=> r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_26])])).

fof(f105373,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ spl10_23
    | ~ spl10_6249 ),
    inference(subsumption_resolution,[],[f105372,f85])).

fof(f105372,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_6249 ),
    inference(subsumption_resolution,[],[f105371,f86])).

fof(f105371,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_6249 ),
    inference(subsumption_resolution,[],[f105370,f87])).

fof(f105370,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_6249 ),
    inference(subsumption_resolution,[],[f105369,f88])).

fof(f105369,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_6249 ),
    inference(subsumption_resolution,[],[f105368,f89])).

fof(f105368,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_6249 ),
    inference(subsumption_resolution,[],[f105249,f2305])).

fof(f105249,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_6249 ),
    inference(superposition,[],[f105111,f97])).

fof(f97,plain,(
    ! [X0,X1] :
      ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
          ( k2_orders_2(X0,X1) = a_2_1_orders_2(X0,X1)
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',d13_orders_2)).

fof(f105111,plain,
    ( ~ r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ spl10_6249 ),
    inference(avatar_component_clause,[],[f105110])).

fof(f105110,plain,
    ( spl10_6249
  <=> ~ r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6249])])).

fof(f105359,plain,
    ( ~ spl10_0
    | spl10_23
    | spl10_6249
    | ~ spl10_6250 ),
    inference(avatar_contradiction_clause,[],[f105358])).

fof(f105358,plain,
    ( $false
    | ~ spl10_0
    | ~ spl10_23
    | ~ spl10_6249
    | ~ spl10_6250 ),
    inference(subsumption_resolution,[],[f105357,f85])).

fof(f105357,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_23
    | ~ spl10_6249
    | ~ spl10_6250 ),
    inference(subsumption_resolution,[],[f105356,f86])).

fof(f105356,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_23
    | ~ spl10_6249
    | ~ spl10_6250 ),
    inference(subsumption_resolution,[],[f105355,f87])).

fof(f105355,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_23
    | ~ spl10_6249
    | ~ spl10_6250 ),
    inference(subsumption_resolution,[],[f105354,f88])).

fof(f105354,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_23
    | ~ spl10_6249
    | ~ spl10_6250 ),
    inference(subsumption_resolution,[],[f105353,f89])).

fof(f105353,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_23
    | ~ spl10_6249
    | ~ spl10_6250 ),
    inference(subsumption_resolution,[],[f105352,f2305])).

fof(f105352,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_6249
    | ~ spl10_6250 ),
    inference(subsumption_resolution,[],[f105351,f90])).

fof(f90,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f65])).

fof(f105351,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_6249
    | ~ spl10_6250 ),
    inference(subsumption_resolution,[],[f105350,f105111])).

fof(f105350,plain,
    ( r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_0
    | ~ spl10_6250 ),
    inference(subsumption_resolution,[],[f105347,f136])).

fof(f136,plain,
    ( r2_orders_2(sK0,sK1,sK2)
    | ~ spl10_0 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl10_0
  <=> r2_orders_2(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_0])])).

fof(f105347,plain,
    ( ~ r2_orders_2(sK0,sK1,sK2)
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_6250 ),
    inference(superposition,[],[f130,f105296])).

fof(f105296,plain,
    ( sK2 = sK6(sK0,k1_tarski(sK2),sK1)
    | ~ spl10_6250 ),
    inference(resolution,[],[f105120,f129])).

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

fof(f105120,plain,
    ( r2_hidden(sK6(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2))
    | ~ spl10_6250 ),
    inference(avatar_component_clause,[],[f105119])).

fof(f105119,plain,
    ( spl10_6250
  <=> r2_hidden(sK6(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_6250])])).

fof(f130,plain,(
    ! [X2,X3,X1] :
      ( ~ r2_orders_2(X1,X3,sK6(X1,X2,X3))
      | r2_hidden(X3,a_2_1_orders_2(X1,X2))
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
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
      | ~ r2_orders_2(X1,X3,sK6(X1,X2,X3))
      | X0 != X3
      | ~ m1_subset_1(X3,u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f105248,plain,
    ( spl10_23
    | spl10_27
    | ~ spl10_6248 ),
    inference(avatar_contradiction_clause,[],[f105247])).

fof(f105247,plain,
    ( $false
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_6248 ),
    inference(subsumption_resolution,[],[f105246,f85])).

fof(f105246,plain,
    ( v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_6248 ),
    inference(subsumption_resolution,[],[f105245,f86])).

fof(f105245,plain,
    ( ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_6248 ),
    inference(subsumption_resolution,[],[f105244,f87])).

fof(f105244,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_6248 ),
    inference(subsumption_resolution,[],[f105243,f88])).

fof(f105243,plain,
    ( ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_6248 ),
    inference(subsumption_resolution,[],[f105242,f89])).

fof(f105242,plain,
    ( ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_23
    | ~ spl10_27
    | ~ spl10_6248 ),
    inference(subsumption_resolution,[],[f105241,f2305])).

fof(f105241,plain,
    ( ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_27
    | ~ spl10_6248 ),
    inference(subsumption_resolution,[],[f105225,f359])).

fof(f359,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ spl10_27 ),
    inference(avatar_component_clause,[],[f358])).

fof(f358,plain,
    ( spl10_27
  <=> ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_27])])).

fof(f105225,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(k1_tarski(sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl10_6248 ),
    inference(superposition,[],[f105114,f97])).

fof(f105121,plain,
    ( spl10_6248
    | spl10_6250
    | spl10_5 ),
    inference(avatar_split_clause,[],[f105090,f169,f105119,f105113])).

fof(f169,plain,
    ( spl10_5
  <=> u1_struct_0(sK0) != o_0_0_xboole_0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_5])])).

fof(f105090,plain,
    ( r2_hidden(sK6(sK0,k1_tarski(sK2),sK1),k1_tarski(sK2))
    | r2_hidden(sK1,a_2_1_orders_2(sK0,k1_tarski(sK2)))
    | ~ spl10_5 ),
    inference(resolution,[],[f13677,f90])).

fof(f13677,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,k1_tarski(sK2),X1),k1_tarski(sK2))
        | r2_hidden(X1,a_2_1_orders_2(sK0,k1_tarski(sK2))) )
    | ~ spl10_5 ),
    inference(resolution,[],[f7827,f91])).

fof(f7827,plain,
    ( ! [X10,X9] :
        ( ~ m1_subset_1(X9,u1_struct_0(sK0))
        | ~ m1_subset_1(X10,u1_struct_0(sK0))
        | r2_hidden(sK6(sK0,k1_tarski(X9),X10),k1_tarski(X9))
        | r2_hidden(X10,a_2_1_orders_2(sK0,k1_tarski(X9))) )
    | ~ spl10_5 ),
    inference(subsumption_resolution,[],[f7821,f170])).

fof(f170,plain,
    ( u1_struct_0(sK0) != o_0_0_xboole_0
    | ~ spl10_5 ),
    inference(avatar_component_clause,[],[f169])).

fof(f7821,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,u1_struct_0(sK0))
      | u1_struct_0(sK0) = o_0_0_xboole_0
      | ~ m1_subset_1(X10,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,k1_tarski(X9),X10),k1_tarski(X9))
      | r2_hidden(X10,a_2_1_orders_2(sK0,k1_tarski(X9))) ) ),
    inference(resolution,[],[f2300,f857])).

fof(f857,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | r2_hidden(sK6(sK0,X0,X1),X0)
      | r2_hidden(X1,a_2_1_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f856,f85])).

fof(f856,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f855,f86])).

fof(f855,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f854,f87])).

fof(f854,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK6(sK0,X0,X1),X0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
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
      | r2_hidden(X1,a_2_1_orders_2(sK0,X0))
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
      | r2_hidden(X3,a_2_1_orders_2(X1,X2))
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(equality_resolution,[],[f120])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,a_2_1_orders_2(X1,X2))
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',t6_boole)).

fof(f148,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f96,f94])).

fof(f94,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',dt_o_0_0_xboole_0)).

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
  <=> ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_3])])).

fof(f365,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_3 ),
    inference(subsumption_resolution,[],[f364,f91])).

fof(f364,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_3 ),
    inference(superposition,[],[f145,f104])).

fof(f145,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl10_3 ),
    inference(avatar_component_clause,[],[f144])).

fof(f363,plain,
    ( spl10_22
    | spl10_26
    | ~ spl10_2 ),
    inference(avatar_split_clause,[],[f356,f141,f361,f347])).

fof(f141,plain,
    ( spl10_2
  <=> r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl10_2])])).

fof(f356,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_2 ),
    inference(subsumption_resolution,[],[f341,f91])).

fof(f341,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK2)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl10_2 ),
    inference(superposition,[],[f142,f104])).

fof(f142,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
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
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',dt_l1_orders_2)).

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
    file('/export/starexec/sandbox2/benchmark/orders_2__t52_orders_2.p',fc2_struct_0)).

fof(f147,plain,
    ( spl10_0
    | spl10_2 ),
    inference(avatar_split_clause,[],[f92,f141,f135])).

fof(f92,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f146,plain,
    ( ~ spl10_1
    | ~ spl10_3 ),
    inference(avatar_split_clause,[],[f93,f144,f138])).

fof(f93,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ r2_orders_2(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
