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
% DateTime   : Thu Dec  3 13:10:00 EST 2020

% Result     : Theorem 1.15s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 211 expanded)
%              Number of leaves         :   16 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  416 (1238 expanded)
%              Number of equality atoms :   60 (  66 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f192,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f78,f143,f157,f191])).

fof(f191,plain,
    ( ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f190])).

fof(f190,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f189,f40])).

fof(f40,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_orders_2(sK1)
    & v5_orders_2(sK1)
    & v4_orders_2(sK1)
    & v3_orders_2(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_orders_2(sK1)
      & v5_orders_2(sK1)
      & v4_orders_2(sK1)
      & v3_orders_2(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1)))
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
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
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).

fof(f189,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f187,f64])).

fof(f64,plain,(
    ! [X0,X1] : r2_hidden(X0,k2_tarski(X1,X0)) ),
    inference(resolution,[],[f59,f61])).

fof(f61,plain,(
    ! [X0,X1] : sP0(X1,X0,k2_tarski(X0,X1)) ),
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( sP0(X1,X0,X2)
      | k2_tarski(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( k2_tarski(X0,X1) = X2
        | ~ sP0(X1,X0,X2) )
      & ( sP0(X1,X0,X2)
        | k2_tarski(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> sP0(X1,X0,X2) ) ),
    inference(definition_folding,[],[f1,f24])).

fof(f24,plain,(
    ! [X1,X0,X2] :
      ( sP0(X1,X0,X2)
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_tarski(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( X1 = X3
            | X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

fof(f59,plain,(
    ! [X4,X2,X1] :
      ( ~ sP0(X4,X1,X2)
      | r2_hidden(X4,X2) ) ),
    inference(equality_resolution,[],[f51])).

fof(f51,plain,(
    ! [X4,X2,X0,X1] :
      ( r2_hidden(X4,X2)
      | X0 != X4
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
        | ( ( ( sK3(X0,X1,X2) != X0
              & sK3(X0,X1,X2) != X1 )
            | ~ r2_hidden(sK3(X0,X1,X2),X2) )
          & ( sK3(X0,X1,X2) = X0
            | sK3(X0,X1,X2) = X1
            | r2_hidden(sK3(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ( X0 != X4
                & X1 != X4 ) )
            & ( X0 = X4
              | X1 = X4
              | ~ r2_hidden(X4,X2) ) )
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).

fof(f32,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ( X0 != X3
              & X1 != X3 )
            | ~ r2_hidden(X3,X2) )
          & ( X0 = X3
            | X1 = X3
            | r2_hidden(X3,X2) ) )
     => ( ( ( sK3(X0,X1,X2) != X0
            & sK3(X0,X1,X2) != X1 )
          | ~ r2_hidden(sK3(X0,X1,X2),X2) )
        & ( sK3(X0,X1,X2) = X0
          | sK3(X0,X1,X2) = X1
          | r2_hidden(sK3(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( sP0(X0,X1,X2)
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
        | ~ sP0(X0,X1,X2) ) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(flattening,[],[f29])).

% (521)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
fof(f29,plain,(
    ! [X1,X0,X2] :
      ( ( sP0(X1,X0,X2)
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
        | ~ sP0(X1,X0,X2) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f187,plain,
    ( ~ r2_hidden(sK2,k2_tarski(sK2,sK2))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f183,f79])).

fof(f79,plain,
    ( r2_hidden(sK2,k2_orders_2(sK1,k2_tarski(sK2,sK2)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f41,f77])).

fof(f77,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f75])).

fof(f75,plain,
    ( spl4_2
  <=> k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f41,plain,(
    r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) ),
    inference(cnf_transformation,[],[f28])).

fof(f183,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2)))
        | ~ r2_hidden(X1,k2_tarski(sK2,sK2))
        | ~ m1_subset_1(X1,u1_struct_0(sK1)) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f182,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f182,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK2,sK2))
        | ~ r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | v2_struct_0(sK1) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f181,f36])).

fof(f36,plain,(
    v3_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f181,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK2,sK2))
        | ~ r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f180,f37])).

fof(f37,plain,(
    v4_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f180,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK2,sK2))
        | ~ r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f179,f38])).

fof(f38,plain,(
    v5_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f179,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK2,sK2))
        | ~ r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ v5_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f175,f39])).

fof(f39,plain,(
    l1_orders_2(sK1) ),
    inference(cnf_transformation,[],[f28])).

fof(f175,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_tarski(sK2,sK2))
        | ~ r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK1))
        | ~ l1_orders_2(sK1)
        | ~ v5_orders_2(sK1)
        | ~ v4_orders_2(sK1)
        | ~ v3_orders_2(sK1)
        | v2_struct_0(sK1) )
    | ~ spl4_3 ),
    inference(resolution,[],[f85,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k2_orders_2(X0,X2))
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
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( ! [X2] :
              ( ~ r2_hidden(X1,k2_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( r2_hidden(X1,k2_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).

fof(f85,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl4_3
  <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f157,plain,
    ( spl4_1
    | spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f81,f75,f83,f71])).

fof(f71,plain,
    ( spl4_1
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f81,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f80,f40])).

fof(f80,plain,
    ( m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_2 ),
    inference(superposition,[],[f47,f77])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
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

fof(f143,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f142])).

fof(f142,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f141,f40])).

fof(f141,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f140,f39])).

fof(f140,plain,
    ( ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f139,f73])).

fof(f73,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f71])).

fof(f139,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f138,f35])).

fof(f138,plain,
    ( v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f137,f36])).

fof(f137,plain,
    ( ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f136,f37])).

fof(f136,plain,
    ( ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f134,f38])).

fof(f134,plain,
    ( ~ v5_orders_2(sK1)
    | ~ v4_orders_2(sK1)
    | ~ v3_orders_2(sK1)
    | v2_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1))
    | ~ l1_orders_2(sK1)
    | ~ m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(resolution,[],[f132,f41])).

fof(f132,plain,(
    ! [X4,X5,X3] :
      ( ~ r2_hidden(X4,k2_orders_2(X3,k6_domain_1(u1_struct_0(X3),X5)))
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_xboole_0(u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ m1_subset_1(X5,u1_struct_0(X3)) ) ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,(
    ! [X4,X5,X3] :
      ( ~ l1_orders_2(X3)
      | ~ v5_orders_2(X3)
      | ~ v4_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3)
      | ~ v1_xboole_0(u1_struct_0(X3))
      | ~ r2_hidden(X4,k2_orders_2(X3,k6_domain_1(u1_struct_0(X3),X5)))
      | ~ m1_subset_1(X5,u1_struct_0(X3))
      | ~ l1_orders_2(X3)
      | ~ v3_orders_2(X3)
      | v2_struct_0(X3) ) ),
    inference(resolution,[],[f114,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ v1_xboole_0(u1_struct_0(X1))
      | ~ r2_hidden(X2,k2_orders_2(X1,X0)) ) ),
    inference(resolution,[],[f48,f57])).

fof(f57,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f78,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f68,f75,f71])).

fof(f68,plain,
    ( k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)
    | v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f58,f40])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k2_tarski(X1,X1)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f46,f42])).

fof(f42,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
% 0.14/0.35  % DateTime   : Tue Dec  1 13:04:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.15/0.54  % (484)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.15/0.55  % (484)Refutation found. Thanks to Tanya!
% 1.15/0.55  % SZS status Theorem for theBenchmark
% 1.47/0.56  % (507)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.47/0.56  % (486)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.47/0.56  % (513)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.47/0.56  % (481)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.47/0.56  % (499)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.47/0.57  % (507)Refutation not found, incomplete strategy% (507)------------------------------
% 1.47/0.57  % (507)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (507)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.57  
% 1.47/0.57  % (507)Memory used [KB]: 10618
% 1.47/0.57  % (507)Time elapsed: 0.143 s
% 1.47/0.57  % (507)------------------------------
% 1.47/0.57  % (507)------------------------------
% 1.47/0.57  % (508)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.47/0.57  % (517)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.47/0.57  % (483)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.47/0.57  % SZS output start Proof for theBenchmark
% 1.47/0.57  fof(f192,plain,(
% 1.47/0.57    $false),
% 1.47/0.57    inference(avatar_sat_refutation,[],[f78,f143,f157,f191])).
% 1.47/0.57  fof(f191,plain,(
% 1.47/0.57    ~spl4_2 | ~spl4_3),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f190])).
% 1.47/0.57  fof(f190,plain,(
% 1.47/0.57    $false | (~spl4_2 | ~spl4_3)),
% 1.47/0.57    inference(subsumption_resolution,[],[f189,f40])).
% 1.47/0.57  fof(f40,plain,(
% 1.47/0.57    m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f28,plain,(
% 1.47/0.57    (r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1)),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f12,f27,f26])).
% 1.47/0.57  fof(f26,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_orders_2(sK1) & v5_orders_2(sK1) & v4_orders_2(sK1) & v3_orders_2(sK1) & ~v2_struct_0(sK1))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f27,plain,(
% 1.47/0.57    ? [X1] : (r2_hidden(X1,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),X1))) & m1_subset_1(X1,u1_struct_0(sK1))) => (r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2))) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f12,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f11])).
% 1.47/0.57  fof(f11,plain,(
% 1.47/0.57    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f10])).
% 1.47/0.57  fof(f10,negated_conjecture,(
% 1.47/0.57    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.47/0.57    inference(negated_conjecture,[],[f9])).
% 1.47/0.57  fof(f9,conjecture,(
% 1.47/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_orders_2)).
% 1.47/0.57  fof(f189,plain,(
% 1.47/0.57    ~m1_subset_1(sK2,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_3)),
% 1.47/0.57    inference(subsumption_resolution,[],[f187,f64])).
% 1.47/0.57  fof(f64,plain,(
% 1.47/0.57    ( ! [X0,X1] : (r2_hidden(X0,k2_tarski(X1,X0))) )),
% 1.47/0.57    inference(resolution,[],[f59,f61])).
% 1.47/0.57  fof(f61,plain,(
% 1.47/0.57    ( ! [X0,X1] : (sP0(X1,X0,k2_tarski(X0,X1))) )),
% 1.47/0.57    inference(equality_resolution,[],[f55])).
% 1.47/0.57  fof(f55,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2) )),
% 1.47/0.57    inference(cnf_transformation,[],[f34])).
% 1.47/0.57  fof(f34,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((k2_tarski(X0,X1) = X2 | ~sP0(X1,X0,X2)) & (sP0(X1,X0,X2) | k2_tarski(X0,X1) != X2))),
% 1.47/0.57    inference(nnf_transformation,[],[f25])).
% 1.47/0.57  fof(f25,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> sP0(X1,X0,X2))),
% 1.47/0.57    inference(definition_folding,[],[f1,f24])).
% 1.47/0.57  fof(f24,plain,(
% 1.47/0.57    ! [X1,X0,X2] : (sP0(X1,X0,X2) <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.47/0.57    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.47/0.57  fof(f1,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : (k2_tarski(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (X1 = X3 | X0 = X3)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).
% 1.47/0.57  fof(f59,plain,(
% 1.47/0.57    ( ! [X4,X2,X1] : (~sP0(X4,X1,X2) | r2_hidden(X4,X2)) )),
% 1.47/0.57    inference(equality_resolution,[],[f51])).
% 1.47/0.57  fof(f51,plain,(
% 1.47/0.57    ( ! [X4,X2,X0,X1] : (r2_hidden(X4,X2) | X0 != X4 | ~sP0(X0,X1,X2)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f33])).
% 1.47/0.57  fof(f33,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | (((sK3(X0,X1,X2) != X0 & sK3(X0,X1,X2) != X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X0 | sK3(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.47/0.57    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f31,f32])).
% 1.47/0.57  fof(f32,plain,(
% 1.47/0.57    ! [X2,X1,X0] : (? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2))) => (((sK3(X0,X1,X2) != X0 & sK3(X0,X1,X2) != X1) | ~r2_hidden(sK3(X0,X1,X2),X2)) & (sK3(X0,X1,X2) = X0 | sK3(X0,X1,X2) = X1 | r2_hidden(sK3(X0,X1,X2),X2))))),
% 1.47/0.57    introduced(choice_axiom,[])).
% 1.47/0.57  fof(f31,plain,(
% 1.47/0.57    ! [X0,X1,X2] : ((sP0(X0,X1,X2) | ? [X3] : (((X0 != X3 & X1 != X3) | ~r2_hidden(X3,X2)) & (X0 = X3 | X1 = X3 | r2_hidden(X3,X2)))) & (! [X4] : ((r2_hidden(X4,X2) | (X0 != X4 & X1 != X4)) & (X0 = X4 | X1 = X4 | ~r2_hidden(X4,X2))) | ~sP0(X0,X1,X2)))),
% 1.47/0.57    inference(rectify,[],[f30])).
% 1.47/0.57  fof(f30,plain,(
% 1.47/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & (X1 = X3 | X0 = X3 | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & (X1 = X3 | X0 = X3 | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.47/0.57    inference(flattening,[],[f29])).
% 1.47/0.57  % (521)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.47/0.57  fof(f29,plain,(
% 1.47/0.57    ! [X1,X0,X2] : ((sP0(X1,X0,X2) | ? [X3] : (((X1 != X3 & X0 != X3) | ~r2_hidden(X3,X2)) & ((X1 = X3 | X0 = X3) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | (X1 != X3 & X0 != X3)) & ((X1 = X3 | X0 = X3) | ~r2_hidden(X3,X2))) | ~sP0(X1,X0,X2)))),
% 1.47/0.57    inference(nnf_transformation,[],[f24])).
% 1.47/0.57  fof(f187,plain,(
% 1.47/0.57    ~r2_hidden(sK2,k2_tarski(sK2,sK2)) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | (~spl4_2 | ~spl4_3)),
% 1.47/0.57    inference(resolution,[],[f183,f79])).
% 1.47/0.57  fof(f79,plain,(
% 1.47/0.57    r2_hidden(sK2,k2_orders_2(sK1,k2_tarski(sK2,sK2))) | ~spl4_2),
% 1.47/0.57    inference(backward_demodulation,[],[f41,f77])).
% 1.47/0.57  fof(f77,plain,(
% 1.47/0.57    k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) | ~spl4_2),
% 1.47/0.57    inference(avatar_component_clause,[],[f75])).
% 1.47/0.57  fof(f75,plain,(
% 1.47/0.57    spl4_2 <=> k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2)),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.47/0.57  fof(f41,plain,(
% 1.47/0.57    r2_hidden(sK2,k2_orders_2(sK1,k6_domain_1(u1_struct_0(sK1),sK2)))),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f183,plain,(
% 1.47/0.57    ( ! [X1] : (~r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2))) | ~r2_hidden(X1,k2_tarski(sK2,sK2)) | ~m1_subset_1(X1,u1_struct_0(sK1))) ) | ~spl4_3),
% 1.47/0.57    inference(subsumption_resolution,[],[f182,f35])).
% 1.47/0.57  fof(f35,plain,(
% 1.47/0.57    ~v2_struct_0(sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f182,plain,(
% 1.47/0.57    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK2,sK2)) | ~r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | v2_struct_0(sK1)) ) | ~spl4_3),
% 1.47/0.57    inference(subsumption_resolution,[],[f181,f36])).
% 1.47/0.57  fof(f36,plain,(
% 1.47/0.57    v3_orders_2(sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f181,plain,(
% 1.47/0.57    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK2,sK2)) | ~r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v3_orders_2(sK1) | v2_struct_0(sK1)) ) | ~spl4_3),
% 1.47/0.57    inference(subsumption_resolution,[],[f180,f37])).
% 1.47/0.57  fof(f37,plain,(
% 1.47/0.57    v4_orders_2(sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f180,plain,(
% 1.47/0.57    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK2,sK2)) | ~r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)) ) | ~spl4_3),
% 1.47/0.57    inference(subsumption_resolution,[],[f179,f38])).
% 1.47/0.57  fof(f38,plain,(
% 1.47/0.57    v5_orders_2(sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f179,plain,(
% 1.47/0.57    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK2,sK2)) | ~r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~v5_orders_2(sK1) | ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)) ) | ~spl4_3),
% 1.47/0.57    inference(subsumption_resolution,[],[f175,f39])).
% 1.47/0.57  fof(f39,plain,(
% 1.47/0.57    l1_orders_2(sK1)),
% 1.47/0.57    inference(cnf_transformation,[],[f28])).
% 1.47/0.57  fof(f175,plain,(
% 1.47/0.57    ( ! [X1] : (~r2_hidden(X1,k2_tarski(sK2,sK2)) | ~r2_hidden(X1,k2_orders_2(sK1,k2_tarski(sK2,sK2))) | ~m1_subset_1(X1,u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~v5_orders_2(sK1) | ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1)) ) | ~spl4_3),
% 1.47/0.57    inference(resolution,[],[f85,f43])).
% 1.47/0.57  fof(f43,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k2_orders_2(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f14])).
% 1.47/0.57  fof(f14,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f13])).
% 1.47/0.57  fof(f13,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f8])).
% 1.47/0.57  fof(f8,axiom,(
% 1.47/0.57    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_orders_2)).
% 1.47/0.57  fof(f85,plain,(
% 1.47/0.57    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~spl4_3),
% 1.47/0.57    inference(avatar_component_clause,[],[f83])).
% 1.47/0.57  fof(f83,plain,(
% 1.47/0.57    spl4_3 <=> m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.47/0.57  fof(f157,plain,(
% 1.47/0.57    spl4_1 | spl4_3 | ~spl4_2),
% 1.47/0.57    inference(avatar_split_clause,[],[f81,f75,f83,f71])).
% 1.47/0.57  fof(f71,plain,(
% 1.47/0.57    spl4_1 <=> v1_xboole_0(u1_struct_0(sK1))),
% 1.47/0.57    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.47/0.57  fof(f81,plain,(
% 1.47/0.57    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | v1_xboole_0(u1_struct_0(sK1)) | ~spl4_2),
% 1.47/0.57    inference(subsumption_resolution,[],[f80,f40])).
% 1.47/0.57  fof(f80,plain,(
% 1.47/0.57    m1_subset_1(k2_tarski(sK2,sK2),k1_zfmisc_1(u1_struct_0(sK1))) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | v1_xboole_0(u1_struct_0(sK1)) | ~spl4_2),
% 1.47/0.57    inference(superposition,[],[f47,f77])).
% 1.47/0.57  fof(f47,plain,(
% 1.47/0.57    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f20])).
% 1.47/0.57  fof(f20,plain,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f19])).
% 1.47/0.57  fof(f19,plain,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f5])).
% 1.47/0.57  fof(f5,axiom,(
% 1.47/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 1.47/0.57  fof(f143,plain,(
% 1.47/0.57    ~spl4_1),
% 1.47/0.57    inference(avatar_contradiction_clause,[],[f142])).
% 1.47/0.57  fof(f142,plain,(
% 1.47/0.57    $false | ~spl4_1),
% 1.47/0.57    inference(subsumption_resolution,[],[f141,f40])).
% 1.47/0.57  fof(f141,plain,(
% 1.47/0.57    ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl4_1),
% 1.47/0.57    inference(subsumption_resolution,[],[f140,f39])).
% 1.47/0.57  fof(f140,plain,(
% 1.47/0.57    ~l1_orders_2(sK1) | ~m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl4_1),
% 1.47/0.57    inference(subsumption_resolution,[],[f139,f73])).
% 1.47/0.57  fof(f73,plain,(
% 1.47/0.57    v1_xboole_0(u1_struct_0(sK1)) | ~spl4_1),
% 1.47/0.57    inference(avatar_component_clause,[],[f71])).
% 1.47/0.57  fof(f139,plain,(
% 1.47/0.57    ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.47/0.57    inference(subsumption_resolution,[],[f138,f35])).
% 1.47/0.57  fof(f138,plain,(
% 1.47/0.57    v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.47/0.57    inference(subsumption_resolution,[],[f137,f36])).
% 1.47/0.57  fof(f137,plain,(
% 1.47/0.57    ~v3_orders_2(sK1) | v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.47/0.57    inference(subsumption_resolution,[],[f136,f37])).
% 1.47/0.57  fof(f136,plain,(
% 1.47/0.57    ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.47/0.57    inference(subsumption_resolution,[],[f134,f38])).
% 1.47/0.57  fof(f134,plain,(
% 1.47/0.57    ~v5_orders_2(sK1) | ~v4_orders_2(sK1) | ~v3_orders_2(sK1) | v2_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1)) | ~l1_orders_2(sK1) | ~m1_subset_1(sK2,u1_struct_0(sK1))),
% 1.47/0.57    inference(resolution,[],[f132,f41])).
% 1.47/0.57  fof(f132,plain,(
% 1.47/0.57    ( ! [X4,X5,X3] : (~r2_hidden(X4,k2_orders_2(X3,k6_domain_1(u1_struct_0(X3),X5))) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3) | ~v1_xboole_0(u1_struct_0(X3)) | ~l1_orders_2(X3) | ~m1_subset_1(X5,u1_struct_0(X3))) )),
% 1.47/0.57    inference(duplicate_literal_removal,[],[f129])).
% 1.47/0.57  fof(f129,plain,(
% 1.47/0.57    ( ! [X4,X5,X3] : (~l1_orders_2(X3) | ~v5_orders_2(X3) | ~v4_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3) | ~v1_xboole_0(u1_struct_0(X3)) | ~r2_hidden(X4,k2_orders_2(X3,k6_domain_1(u1_struct_0(X3),X5))) | ~m1_subset_1(X5,u1_struct_0(X3)) | ~l1_orders_2(X3) | ~v3_orders_2(X3) | v2_struct_0(X3)) )),
% 1.47/0.57    inference(resolution,[],[f114,f45])).
% 1.47/0.57  fof(f45,plain,(
% 1.47/0.57    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f16])).
% 1.47/0.57  fof(f16,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f15])).
% 1.47/0.57  fof(f15,plain,(
% 1.47/0.57    ! [X0] : (! [X1] : ((m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f7])).
% 1.47/0.57  fof(f7,axiom,(
% 1.47/0.57    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_orders_2)).
% 1.47/0.57  fof(f114,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~v1_xboole_0(u1_struct_0(X1)) | ~r2_hidden(X2,k2_orders_2(X1,X0))) )),
% 1.47/0.57    inference(resolution,[],[f48,f57])).
% 1.47/0.57  fof(f57,plain,(
% 1.47/0.57    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2) | ~r2_hidden(X0,X1)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f23])).
% 1.47/0.57  fof(f23,plain,(
% 1.47/0.57    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 1.47/0.57    inference(ennf_transformation,[],[f3])).
% 1.47/0.57  fof(f3,axiom,(
% 1.47/0.57    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 1.47/0.57  fof(f48,plain,(
% 1.47/0.57    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f22])).
% 1.47/0.57  fof(f22,plain,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 1.47/0.57    inference(flattening,[],[f21])).
% 1.47/0.57  fof(f21,plain,(
% 1.47/0.57    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f4])).
% 1.47/0.57  fof(f4,axiom,(
% 1.47/0.57    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 1.47/0.57  fof(f78,plain,(
% 1.47/0.57    spl4_1 | spl4_2),
% 1.47/0.57    inference(avatar_split_clause,[],[f68,f75,f71])).
% 1.47/0.57  fof(f68,plain,(
% 1.47/0.57    k6_domain_1(u1_struct_0(sK1),sK2) = k2_tarski(sK2,sK2) | v1_xboole_0(u1_struct_0(sK1))),
% 1.47/0.57    inference(resolution,[],[f58,f40])).
% 1.47/0.57  fof(f58,plain,(
% 1.47/0.57    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k2_tarski(X1,X1) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(definition_unfolding,[],[f46,f42])).
% 1.47/0.57  fof(f42,plain,(
% 1.47/0.57    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f2])).
% 1.47/0.57  fof(f2,axiom,(
% 1.47/0.57    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).
% 1.47/0.57  fof(f46,plain,(
% 1.47/0.57    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 1.47/0.57    inference(cnf_transformation,[],[f18])).
% 1.47/0.57  fof(f18,plain,(
% 1.47/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.47/0.57    inference(flattening,[],[f17])).
% 1.47/0.57  fof(f17,plain,(
% 1.47/0.57    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.47/0.57    inference(ennf_transformation,[],[f6])).
% 1.47/0.57  fof(f6,axiom,(
% 1.47/0.57    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.47/0.57    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.47/0.57  % SZS output end Proof for theBenchmark
% 1.47/0.57  % (484)------------------------------
% 1.47/0.57  % (484)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (484)Termination reason: Refutation
% 1.47/0.57  
% 1.47/0.57  % (484)Memory used [KB]: 10746
% 1.47/0.57  % (484)Time elapsed: 0.120 s
% 1.47/0.57  % (484)------------------------------
% 1.47/0.57  % (484)------------------------------
% 1.47/0.58  % (477)Success in time 0.205 s
%------------------------------------------------------------------------------
