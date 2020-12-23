%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:58 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 354 expanded)
%              Number of leaves         :   12 (  76 expanded)
%              Depth                    :   18
%              Number of atoms          :  338 (1498 expanded)
%              Number of equality atoms :   23 (  85 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f356,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f314,f355])).

fof(f355,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f354])).

fof(f354,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f353,f319])).

fof(f319,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f26,f65])).

fof(f65,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_1
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f26,plain,(
    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
          ( r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
           => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
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
         => ~ r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).

fof(f353,plain,
    ( ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f352,f49])).

fof(f49,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( X0 != X2
      | r2_hidden(X2,X1)
      | k1_tarski(X0) != X1 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_tarski(X0) = X1
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
        <=> X0 = X2 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

fof(f352,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl4_1 ),
    inference(resolution,[],[f341,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k1_tarski(sK1))
        | ~ r2_hidden(X0,k2_orders_2(sK0,k1_tarski(sK1))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f340,f325])).

fof(f325,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f324,f27])).

% (15384)Refutation not found, incomplete strategy% (15384)------------------------------
% (15384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (15384)Termination reason: Refutation not found, incomplete strategy

% (15384)Memory used [KB]: 10490
% (15384)Time elapsed: 0.117 s
% (15384)------------------------------
% (15384)------------------------------
fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f324,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f323,f25])).

fof(f323,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f322,f31])).

fof(f31,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f322,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f321,f28])).

fof(f28,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f321,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(superposition,[],[f34,f65])).

fof(f34,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

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

fof(f340,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f339,f27])).

fof(f339,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f338,f30])).

fof(f30,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f338,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f337,f29])).

fof(f29,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f337,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f336,f28])).

fof(f336,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k2_orders_2(sK0,X1)) ) ),
    inference(resolution,[],[f33,f31])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k2_orders_2(X0,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).

fof(f314,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f313])).

fof(f313,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f295,f311])).

fof(f311,plain,
    ( ! [X2] : ~ r2_hidden(X2,k2_orders_2(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(resolution,[],[f307,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f307,plain,
    ( v1_xboole_0(k2_orders_2(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(resolution,[],[f304,f300])).

fof(f300,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f299,f77])).

fof(f77,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f25,f73])).

fof(f73,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f69,f32])).

fof(f32,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f69,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f67,plain,
    ( spl4_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f299,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0))
    | ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(superposition,[],[f117,f291])).

fof(f291,plain,
    ( k1_xboole_0 = k6_domain_1(k1_xboole_0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f287,f32])).

fof(f287,plain,
    ( v1_xboole_0(k6_domain_1(k1_xboole_0,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f77,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | v1_xboole_0(k6_domain_1(k1_xboole_0,X0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f117,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f75,f51])).

fof(f51,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

fof(f75,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f71,f73])).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f69,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f117,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f116,f27])).

fof(f116,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f115,f31])).

fof(f115,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_xboole_0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f114,f28])).

fof(f114,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_xboole_0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f34,f73])).

fof(f304,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(k2_orders_2(sK0,X0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f259,f79])).

fof(f259,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f258,f27])).

fof(f258,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f257,f31])).

fof(f257,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f256,f30])).

fof(f256,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f255,f29])).

fof(f255,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f254,f28])).

fof(f254,plain,
    ( ! [X0] :
        ( m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f39,f73])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).

fof(f295,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f78,f291])).

fof(f78,plain,
    ( r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f26,f73])).

fof(f70,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f61,f67,f63])).

fof(f61,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f38,f25])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:21:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.45  % (15389)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.19/0.48  % (15392)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.19/0.48  % (15391)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.48  % (15406)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.48  % (15393)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.19/0.48  % (15399)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.48  % (15396)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.19/0.48  % (15387)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.19/0.49  % (15386)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.49  % (15389)Refutation not found, incomplete strategy% (15389)------------------------------
% 0.19/0.49  % (15389)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (15389)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.49  
% 0.19/0.49  % (15389)Memory used [KB]: 6140
% 0.19/0.49  % (15389)Time elapsed: 0.095 s
% 0.19/0.49  % (15389)------------------------------
% 0.19/0.49  % (15389)------------------------------
% 0.19/0.49  % (15398)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.49  % (15397)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.19/0.49  % (15385)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.19/0.49  % (15408)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.19/0.49  % (15405)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.19/0.49  % (15403)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.19/0.49  % (15390)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.49  % (15395)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.19/0.49  % (15400)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.49  % (15406)Refutation found. Thanks to Tanya!
% 0.19/0.49  % SZS status Theorem for theBenchmark
% 0.19/0.50  % (15394)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.19/0.50  % (15384)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.19/0.50  % (15388)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.50  % (15401)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 0.19/0.50  % (15402)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.19/0.50  % (15397)Refutation not found, incomplete strategy% (15397)------------------------------
% 0.19/0.50  % (15397)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (15397)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (15397)Memory used [KB]: 6140
% 0.19/0.50  % (15397)Time elapsed: 0.087 s
% 0.19/0.50  % (15397)------------------------------
% 0.19/0.50  % (15397)------------------------------
% 0.19/0.50  % (15404)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.19/0.50  % (15409)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.19/0.51  % (15385)Refutation not found, incomplete strategy% (15385)------------------------------
% 0.19/0.51  % (15385)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (15385)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (15385)Memory used [KB]: 10618
% 0.19/0.51  % (15385)Time elapsed: 0.109 s
% 0.19/0.51  % (15385)------------------------------
% 0.19/0.51  % (15385)------------------------------
% 0.19/0.51  % SZS output start Proof for theBenchmark
% 0.19/0.51  fof(f356,plain,(
% 0.19/0.51    $false),
% 0.19/0.51    inference(avatar_sat_refutation,[],[f70,f314,f355])).
% 0.19/0.51  fof(f355,plain,(
% 0.19/0.51    ~spl4_1),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f354])).
% 0.19/0.51  fof(f354,plain,(
% 0.19/0.51    $false | ~spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f353,f319])).
% 0.19/0.51  fof(f319,plain,(
% 0.19/0.51    r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK1))) | ~spl4_1),
% 0.19/0.51    inference(backward_demodulation,[],[f26,f65])).
% 0.19/0.51  fof(f65,plain,(
% 0.19/0.51    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl4_1),
% 0.19/0.51    inference(avatar_component_clause,[],[f63])).
% 0.19/0.51  fof(f63,plain,(
% 0.19/0.51    spl4_1 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.19/0.51  fof(f26,plain,(
% 0.19/0.51    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f14,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f13])).
% 0.19/0.51  fof(f13,plain,(
% 0.19/0.51    ? [X0] : (? [X1] : (r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f11])).
% 0.19/0.51  fof(f11,negated_conjecture,(
% 0.19/0.51    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.19/0.51    inference(negated_conjecture,[],[f10])).
% 0.19/0.51  fof(f10,conjecture,(
% 0.19/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k2_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_orders_2)).
% 0.19/0.51  fof(f353,plain,(
% 0.19/0.51    ~r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK1))) | ~spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f352,f49])).
% 0.19/0.51  fof(f49,plain,(
% 0.19/0.51    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.19/0.51    inference(equality_resolution,[],[f48])).
% 0.19/0.51  fof(f48,plain,(
% 0.19/0.51    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.19/0.51    inference(equality_resolution,[],[f40])).
% 0.19/0.51  fof(f40,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.19/0.51    inference(cnf_transformation,[],[f3])).
% 0.19/0.51  fof(f3,axiom,(
% 0.19/0.51    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.19/0.51  fof(f352,plain,(
% 0.19/0.51    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK1,k2_orders_2(sK0,k1_tarski(sK1))) | ~spl4_1),
% 0.19/0.51    inference(resolution,[],[f341,f25])).
% 0.19/0.51  fof(f25,plain,(
% 0.19/0.51    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f341,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tarski(sK1)) | ~r2_hidden(X0,k2_orders_2(sK0,k1_tarski(sK1)))) ) | ~spl4_1),
% 0.19/0.51    inference(resolution,[],[f340,f325])).
% 0.19/0.51  fof(f325,plain,(
% 0.19/0.51    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f324,f27])).
% 0.19/0.51  % (15384)Refutation not found, incomplete strategy% (15384)------------------------------
% 0.19/0.51  % (15384)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (15384)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.51  
% 0.19/0.51  % (15384)Memory used [KB]: 10490
% 0.19/0.51  % (15384)Time elapsed: 0.117 s
% 0.19/0.51  % (15384)------------------------------
% 0.19/0.51  % (15384)------------------------------
% 0.19/0.51  fof(f27,plain,(
% 0.19/0.51    ~v2_struct_0(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f324,plain,(
% 0.19/0.51    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f323,f25])).
% 0.19/0.51  fof(f323,plain,(
% 0.19/0.51    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f322,f31])).
% 0.19/0.51  fof(f31,plain,(
% 0.19/0.51    l1_orders_2(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f322,plain,(
% 0.19/0.51    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_1),
% 0.19/0.51    inference(subsumption_resolution,[],[f321,f28])).
% 0.19/0.51  fof(f28,plain,(
% 0.19/0.51    v3_orders_2(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f321,plain,(
% 0.19/0.51    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_1),
% 0.19/0.51    inference(superposition,[],[f34,f65])).
% 0.19/0.51  fof(f34,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f19])).
% 0.19/0.51  fof(f19,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f18])).
% 0.19/0.51  fof(f18,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f12])).
% 0.19/0.51  fof(f12,plain,(
% 0.19/0.51    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.51    inference(pure_predicate_removal,[],[f8])).
% 0.19/0.51  fof(f8,axiom,(
% 0.19/0.51    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 0.19/0.51  fof(f340,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_orders_2(sK0,X1))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f339,f27])).
% 0.19/0.51  fof(f339,plain,(
% 0.19/0.51    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_orders_2(sK0,X1))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f338,f30])).
% 0.19/0.51  fof(f30,plain,(
% 0.19/0.51    v5_orders_2(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f338,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_orders_2(sK0,X1))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f337,f29])).
% 0.19/0.51  fof(f29,plain,(
% 0.19/0.51    v4_orders_2(sK0)),
% 0.19/0.51    inference(cnf_transformation,[],[f14])).
% 0.19/0.51  fof(f337,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_orders_2(sK0,X1))) )),
% 0.19/0.51    inference(subsumption_resolution,[],[f336,f28])).
% 0.19/0.51  fof(f336,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k2_orders_2(sK0,X1))) )),
% 0.19/0.51    inference(resolution,[],[f33,f31])).
% 0.19/0.51  fof(f33,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k2_orders_2(X0,X2))) )),
% 0.19/0.51    inference(cnf_transformation,[],[f17])).
% 0.19/0.51  fof(f17,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f16])).
% 0.19/0.51  fof(f16,plain,(
% 0.19/0.51    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k2_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f9])).
% 0.19/0.51  fof(f9,axiom,(
% 0.19/0.51    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k2_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_orders_2)).
% 0.19/0.51  fof(f314,plain,(
% 0.19/0.51    ~spl4_2),
% 0.19/0.51    inference(avatar_contradiction_clause,[],[f313])).
% 0.19/0.51  fof(f313,plain,(
% 0.19/0.51    $false | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f295,f311])).
% 0.19/0.51  fof(f311,plain,(
% 0.19/0.51    ( ! [X2] : (~r2_hidden(X2,k2_orders_2(sK0,k1_xboole_0))) ) | ~spl4_2),
% 0.19/0.51    inference(resolution,[],[f307,f36])).
% 0.19/0.51  fof(f36,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f1])).
% 0.19/0.51  fof(f1,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.19/0.51  fof(f307,plain,(
% 0.19/0.51    v1_xboole_0(k2_orders_2(sK0,k1_xboole_0)) | ~spl4_2),
% 0.19/0.51    inference(resolution,[],[f304,f300])).
% 0.19/0.51  fof(f300,plain,(
% 0.19/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f299,f77])).
% 0.19/0.51  fof(f77,plain,(
% 0.19/0.51    m1_subset_1(sK1,k1_xboole_0) | ~spl4_2),
% 0.19/0.51    inference(backward_demodulation,[],[f25,f73])).
% 0.19/0.51  fof(f73,plain,(
% 0.19/0.51    k1_xboole_0 = u1_struct_0(sK0) | ~spl4_2),
% 0.19/0.51    inference(resolution,[],[f69,f32])).
% 0.19/0.51  fof(f32,plain,(
% 0.19/0.51    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.19/0.51    inference(cnf_transformation,[],[f15])).
% 0.19/0.51  fof(f15,plain,(
% 0.19/0.51    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f2])).
% 0.19/0.51  fof(f2,axiom,(
% 0.19/0.51    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 0.19/0.51  fof(f69,plain,(
% 0.19/0.51    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_2),
% 0.19/0.51    inference(avatar_component_clause,[],[f67])).
% 0.19/0.51  fof(f67,plain,(
% 0.19/0.51    spl4_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.19/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.19/0.51  fof(f299,plain,(
% 0.19/0.51    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(sK1,k1_xboole_0) | ~spl4_2),
% 0.19/0.51    inference(superposition,[],[f117,f291])).
% 0.19/0.51  fof(f291,plain,(
% 0.19/0.51    k1_xboole_0 = k6_domain_1(k1_xboole_0,sK1) | ~spl4_2),
% 0.19/0.51    inference(resolution,[],[f287,f32])).
% 0.19/0.51  fof(f287,plain,(
% 0.19/0.51    v1_xboole_0(k6_domain_1(k1_xboole_0,sK1)) | ~spl4_2),
% 0.19/0.51    inference(resolution,[],[f77,f118])).
% 0.19/0.51  fof(f118,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0) | v1_xboole_0(k6_domain_1(k1_xboole_0,X0))) ) | ~spl4_2),
% 0.19/0.51    inference(resolution,[],[f117,f79])).
% 0.19/0.51  fof(f79,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl4_2),
% 0.19/0.51    inference(forward_demodulation,[],[f75,f51])).
% 0.19/0.51  fof(f51,plain,(
% 0.19/0.51    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.19/0.51    inference(equality_resolution,[],[f45])).
% 0.19/0.51  fof(f45,plain,(
% 0.19/0.51    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f4])).
% 0.19/0.51  fof(f4,axiom,(
% 0.19/0.51    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.19/0.51  fof(f75,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl4_2),
% 0.19/0.51    inference(backward_demodulation,[],[f71,f73])).
% 0.19/0.51  fof(f71,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | v1_xboole_0(X0)) ) | ~spl4_2),
% 0.19/0.51    inference(resolution,[],[f69,f37])).
% 0.19/0.51  fof(f37,plain,(
% 0.19/0.51    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f20])).
% 0.19/0.51  fof(f20,plain,(
% 0.19/0.51    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.19/0.51    inference(ennf_transformation,[],[f5])).
% 0.19/0.51  fof(f5,axiom,(
% 0.19/0.51    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.19/0.51  fof(f117,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_xboole_0)) ) | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f116,f27])).
% 0.19/0.51  fof(f116,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_xboole_0) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f115,f31])).
% 0.19/0.51  fof(f115,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_xboole_0) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f114,f28])).
% 0.19/0.51  fof(f114,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_xboole_0) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.19/0.51    inference(superposition,[],[f34,f73])).
% 0.19/0.51  fof(f304,plain,(
% 0.19/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(k2_orders_2(sK0,X0))) ) | ~spl4_2),
% 0.19/0.51    inference(resolution,[],[f259,f79])).
% 0.19/0.51  fof(f259,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f258,f27])).
% 0.19/0.51  fof(f258,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f257,f31])).
% 0.19/0.51  fof(f257,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f256,f30])).
% 0.19/0.51  fof(f256,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f255,f29])).
% 0.19/0.51  fof(f255,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.19/0.51    inference(subsumption_resolution,[],[f254,f28])).
% 0.19/0.51  fof(f254,plain,(
% 0.19/0.51    ( ! [X0] : (m1_subset_1(k2_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.19/0.51    inference(superposition,[],[f39,f73])).
% 0.19/0.51  fof(f39,plain,(
% 0.19/0.51    ( ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f24])).
% 0.19/0.51  fof(f24,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.19/0.51    inference(flattening,[],[f23])).
% 0.19/0.51  fof(f23,plain,(
% 0.19/0.51    ! [X0,X1] : (m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f6])).
% 0.19/0.51  fof(f6,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k2_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_orders_2)).
% 0.19/0.51  fof(f295,plain,(
% 0.19/0.51    r2_hidden(sK1,k2_orders_2(sK0,k1_xboole_0)) | ~spl4_2),
% 0.19/0.51    inference(backward_demodulation,[],[f78,f291])).
% 0.19/0.51  fof(f78,plain,(
% 0.19/0.51    r2_hidden(sK1,k2_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1))) | ~spl4_2),
% 0.19/0.51    inference(backward_demodulation,[],[f26,f73])).
% 0.19/0.51  fof(f70,plain,(
% 0.19/0.51    spl4_1 | spl4_2),
% 0.19/0.51    inference(avatar_split_clause,[],[f61,f67,f63])).
% 0.19/0.51  fof(f61,plain,(
% 0.19/0.51    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.19/0.51    inference(resolution,[],[f38,f25])).
% 0.19/0.51  fof(f38,plain,(
% 0.19/0.51    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.19/0.51    inference(cnf_transformation,[],[f22])).
% 0.19/0.51  fof(f22,plain,(
% 0.19/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.19/0.51    inference(flattening,[],[f21])).
% 0.19/0.51  fof(f21,plain,(
% 0.19/0.51    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.19/0.51    inference(ennf_transformation,[],[f7])).
% 0.19/0.51  fof(f7,axiom,(
% 0.19/0.51    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.19/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.19/0.51  % SZS output end Proof for theBenchmark
% 0.19/0.51  % (15406)------------------------------
% 0.19/0.51  % (15406)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.51  % (15406)Termination reason: Refutation
% 0.19/0.51  
% 0.19/0.51  % (15406)Memory used [KB]: 10746
% 0.19/0.51  % (15406)Time elapsed: 0.092 s
% 0.19/0.51  % (15406)------------------------------
% 0.19/0.51  % (15406)------------------------------
% 0.19/0.51  % (15407)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.51  % (15383)Success in time 0.165 s
%------------------------------------------------------------------------------
