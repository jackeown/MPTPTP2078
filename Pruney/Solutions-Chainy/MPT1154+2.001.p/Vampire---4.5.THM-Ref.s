%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 378 expanded)
%              Number of leaves         :   13 (  84 expanded)
%              Depth                    :   19
%              Number of atoms          :  352 (1538 expanded)
%              Number of equality atoms :   25 ( 101 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f72,f207,f297])).

fof(f297,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f295,f213])).

fof(f213,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl4_1 ),
    inference(backward_demodulation,[],[f27,f67])).

fof(f67,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_1
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f27,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
          ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
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
           => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
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
         => ~ r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).

fof(f295,plain,
    ( ~ r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f294,f51])).

fof(f51,plain,(
    ! [X2] : r2_hidden(X2,k1_tarski(X2)) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X2,X1] :
      ( r2_hidden(X2,X1)
      | k1_tarski(X2) != X1 ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
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

fof(f294,plain,
    ( ~ r2_hidden(sK1,k1_tarski(sK1))
    | ~ r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1)))
    | ~ spl4_1 ),
    inference(resolution,[],[f235,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f235,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k1_tarski(sK1))
        | ~ r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1))) )
    | ~ spl4_1 ),
    inference(resolution,[],[f234,f219])).

fof(f219,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f218,f28])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f218,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f217,f26])).

fof(f217,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f216,f32])).

fof(f32,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f216,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f215,f29])).

fof(f29,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f215,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(superposition,[],[f36,f67])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))
            & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).

fof(f234,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f233,f28])).

fof(f233,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f232,f31])).

fof(f31,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f232,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f231,f30])).

fof(f30,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f231,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_orders_2(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f230,f29])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_orders_2(sK0,X1)) ) ),
    inference(resolution,[],[f35,f32])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_orders_2(X0,X2)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ~ r2_hidden(X1,k1_orders_2(X0,X2))
              | ~ r2_hidden(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
             => ~ ( r2_hidden(X1,k1_orders_2(X0,X2))
                  & r2_hidden(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).

fof(f207,plain,(
    ~ spl4_2 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f160,f204])).

fof(f204,plain,
    ( ! [X2] : ~ r2_hidden(X2,k1_orders_2(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(resolution,[],[f200,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f200,plain,
    ( v1_xboole_0(k1_orders_2(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(resolution,[],[f197,f166])).

fof(f166,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f165,f79])).

fof(f79,plain,
    ( m1_subset_1(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f26,f75])).

fof(f75,plain,
    ( k1_xboole_0 = u1_struct_0(sK0)
    | ~ spl4_2 ),
    inference(resolution,[],[f71,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f71,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl4_2
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f165,plain,
    ( m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0))
    | ~ m1_subset_1(sK1,k1_xboole_0)
    | ~ spl4_2 ),
    inference(superposition,[],[f122,f156])).

fof(f156,plain,
    ( k1_xboole_0 = k6_domain_1(k1_xboole_0,sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f153,f34])).

fof(f153,plain,
    ( v1_xboole_0(k6_domain_1(k1_xboole_0,sK1))
    | ~ spl4_2 ),
    inference(resolution,[],[f123,f79])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_xboole_0)
        | v1_xboole_0(k6_domain_1(k1_xboole_0,X0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f122,f82])).

fof(f82,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f81,f33])).

fof(f33,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

fof(f81,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f77,f53])).

fof(f53,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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

fof(f77,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f73,f75])).

fof(f73,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1)))
        | v1_xboole_0(X0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f71,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

fof(f122,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f121,f33])).

fof(f121,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f120,f28])).

fof(f120,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_xboole_0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f119,f32])).

fof(f119,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_xboole_0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f118,f29])).

fof(f118,plain,
    ( ! [X0] :
        ( m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v3_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_xboole_0)
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f36,f75])).

fof(f197,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_tarski(k1_xboole_0))
        | v1_xboole_0(k1_orders_2(sK0,X0)) )
    | ~ spl4_2 ),
    inference(resolution,[],[f196,f82])).

fof(f196,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_tarski(k1_xboole_0)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f195,f33])).

fof(f195,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_2 ),
    inference(forward_demodulation,[],[f194,f33])).

fof(f194,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f193,f28])).

fof(f193,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f192,f32])).

fof(f192,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f191,f31])).

fof(f191,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f190,f30])).

fof(f190,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f189,f29])).

fof(f189,plain,
    ( ! [X0] :
        ( m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0))
        | ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
        | v2_struct_0(sK0) )
    | ~ spl4_2 ),
    inference(superposition,[],[f41,f75])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).

fof(f160,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k1_xboole_0))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f80,f156])).

fof(f80,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1)))
    | ~ spl4_2 ),
    inference(backward_demodulation,[],[f27,f75])).

fof(f72,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f63,f69,f65])).

fof(f63,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f40,f26])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
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
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:10:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.50  % (22220)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.50  % (22221)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.51  % (22221)Refutation not found, incomplete strategy% (22221)------------------------------
% 0.20/0.51  % (22221)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (22221)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (22221)Memory used [KB]: 6140
% 0.20/0.51  % (22221)Time elapsed: 0.094 s
% 0.20/0.51  % (22221)------------------------------
% 0.20/0.51  % (22221)------------------------------
% 0.20/0.51  % (22238)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.20/0.51  % (22224)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.20/0.51  % (22236)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.51  % (22222)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.51  % (22228)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.20/0.51  % (22232)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.20/0.51  % (22234)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.20/0.51  % (22237)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.20/0.51  % (22229)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (22238)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f298,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f72,f207,f297])).
% 0.20/0.52  fof(f297,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f296])).
% 0.20/0.52  fof(f296,plain,(
% 0.20/0.52    $false | ~spl4_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f295,f213])).
% 0.20/0.52  fof(f213,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) | ~spl4_1),
% 0.20/0.52    inference(backward_demodulation,[],[f27,f67])).
% 0.20/0.52  fof(f67,plain,(
% 0.20/0.52    k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) | ~spl4_1),
% 0.20/0.52    inference(avatar_component_clause,[],[f65])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    spl4_1 <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.52    inference(negated_conjecture,[],[f11])).
% 0.20/0.52  fof(f11,conjecture,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).
% 0.20/0.52  fof(f295,plain,(
% 0.20/0.52    ~r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) | ~spl4_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f294,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X2] : (r2_hidden(X2,k1_tarski(X2))) )),
% 0.20/0.52    inference(equality_resolution,[],[f50])).
% 0.20/0.52  fof(f50,plain,(
% 0.20/0.52    ( ! [X2,X1] : (r2_hidden(X2,X1) | k1_tarski(X2) != X1) )),
% 0.20/0.52    inference(equality_resolution,[],[f42])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (X0 != X2 | r2_hidden(X2,X1) | k1_tarski(X0) != X1) )),
% 0.20/0.52    inference(cnf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_tarski(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> X0 = X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).
% 0.20/0.52  fof(f294,plain,(
% 0.20/0.52    ~r2_hidden(sK1,k1_tarski(sK1)) | ~r2_hidden(sK1,k1_orders_2(sK0,k1_tarski(sK1))) | ~spl4_1),
% 0.20/0.52    inference(resolution,[],[f235,f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f235,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,k1_tarski(sK1)) | ~r2_hidden(X0,k1_orders_2(sK0,k1_tarski(sK1)))) ) | ~spl4_1),
% 0.20/0.52    inference(resolution,[],[f234,f219])).
% 0.20/0.52  fof(f219,plain,(
% 0.20/0.52    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f218,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f217,f26])).
% 0.20/0.52  fof(f217,plain,(
% 0.20/0.52    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f216,f32])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    l1_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f216,plain,(
% 0.20/0.52    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_1),
% 0.20/0.52    inference(subsumption_resolution,[],[f215,f29])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    v3_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f215,plain,(
% 0.20/0.52    m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~spl4_1),
% 0.20/0.52    inference(superposition,[],[f36,f67])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (m1_subset_1(k6_domain_1(u1_struct_0(X0),X1),k1_zfmisc_1(u1_struct_0(X0))) & v6_orders_2(k6_domain_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_orders_2)).
% 0.20/0.52  fof(f234,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_orders_2(sK0,X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f233,f28])).
% 0.20/0.52  fof(f233,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_orders_2(sK0,X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f232,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    v5_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f232,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_orders_2(sK0,X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f231,f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    v4_orders_2(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f15])).
% 0.20/0.52  fof(f231,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_orders_2(sK0,X1))) )),
% 0.20/0.52    inference(subsumption_resolution,[],[f230,f29])).
% 0.20/0.52  fof(f230,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X0,X1) | ~r2_hidden(X0,k1_orders_2(sK0,X1))) )),
% 0.20/0.52    inference(resolution,[],[f35,f32])).
% 0.20/0.52  fof(f35,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k1_orders_2(X0,X2))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).
% 0.20/0.52  fof(f207,plain,(
% 0.20/0.52    ~spl4_2),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f206])).
% 0.20/0.52  fof(f206,plain,(
% 0.20/0.52    $false | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f160,f204])).
% 0.20/0.52  fof(f204,plain,(
% 0.20/0.52    ( ! [X2] : (~r2_hidden(X2,k1_orders_2(sK0,k1_xboole_0))) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f200,f38])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.20/0.52  fof(f200,plain,(
% 0.20/0.52    v1_xboole_0(k1_orders_2(sK0,k1_xboole_0)) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f197,f166])).
% 0.20/0.52  fof(f166,plain,(
% 0.20/0.52    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f165,f79])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    m1_subset_1(sK1,k1_xboole_0) | ~spl4_2),
% 0.20/0.52    inference(backward_demodulation,[],[f26,f75])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    k1_xboole_0 = u1_struct_0(sK0) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f71,f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f16,plain,(
% 0.20/0.52    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).
% 0.20/0.52  fof(f71,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK0)) | ~spl4_2),
% 0.20/0.52    inference(avatar_component_clause,[],[f69])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    spl4_2 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.52  fof(f165,plain,(
% 0.20/0.52    m1_subset_1(k1_xboole_0,k1_tarski(k1_xboole_0)) | ~m1_subset_1(sK1,k1_xboole_0) | ~spl4_2),
% 0.20/0.52    inference(superposition,[],[f122,f156])).
% 0.20/0.52  fof(f156,plain,(
% 0.20/0.52    k1_xboole_0 = k6_domain_1(k1_xboole_0,sK1) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f153,f34])).
% 0.20/0.52  fof(f153,plain,(
% 0.20/0.52    v1_xboole_0(k6_domain_1(k1_xboole_0,sK1)) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f123,f79])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_xboole_0) | v1_xboole_0(k6_domain_1(k1_xboole_0,X0))) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f122,f82])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f81,f33])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v1_xboole_0(X0)) ) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f77,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 0.20/0.52    inference(equality_resolution,[],[f47])).
% 0.20/0.52  fof(f47,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(X0,X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | v1_xboole_0(X0)) ) | ~spl4_2),
% 0.20/0.52    inference(backward_demodulation,[],[f73,f75])).
% 0.20/0.52  fof(f73,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),X1))) | v1_xboole_0(X0)) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f71,f39])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v1_xboole_0(X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_tarski(k1_xboole_0)) | ~m1_subset_1(X0,k1_xboole_0)) ) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f121,f33])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_xboole_0)) ) | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f120,f28])).
% 0.20/0.52  fof(f120,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_xboole_0) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f119,f32])).
% 0.20/0.52  fof(f119,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_xboole_0) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f118,f29])).
% 0.20/0.52  fof(f118,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k6_domain_1(k1_xboole_0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v3_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_xboole_0) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(superposition,[],[f36,f75])).
% 0.20/0.52  fof(f197,plain,(
% 0.20/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_tarski(k1_xboole_0)) | v1_xboole_0(k1_orders_2(sK0,X0))) ) | ~spl4_2),
% 0.20/0.52    inference(resolution,[],[f196,f82])).
% 0.20/0.52  fof(f196,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0)) | ~m1_subset_1(X0,k1_tarski(k1_xboole_0))) ) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f195,f33])).
% 0.20/0.52  fof(f195,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_tarski(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_2),
% 0.20/0.52    inference(forward_demodulation,[],[f194,f33])).
% 0.20/0.52  fof(f194,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))) ) | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f193,f28])).
% 0.20/0.52  fof(f193,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f192,f32])).
% 0.20/0.52  fof(f192,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f191,f31])).
% 0.20/0.52  fof(f191,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f190,f30])).
% 0.20/0.52  fof(f190,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(subsumption_resolution,[],[f189,f29])).
% 0.20/0.52  fof(f189,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k1_orders_2(sK0,X0),k1_zfmisc_1(k1_xboole_0)) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) | v2_struct_0(sK0)) ) | ~spl4_2),
% 0.20/0.52    inference(superposition,[],[f41,f75])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    ( ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1] : (m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_orders_2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_orders_2)).
% 0.20/0.52  fof(f160,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_orders_2(sK0,k1_xboole_0)) | ~spl4_2),
% 0.20/0.52    inference(backward_demodulation,[],[f80,f156])).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(k1_xboole_0,sK1))) | ~spl4_2),
% 0.20/0.52    inference(backward_demodulation,[],[f27,f75])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    spl4_1 | spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f63,f69,f65])).
% 0.20/0.52  fof(f63,plain,(
% 0.20/0.52    v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)),
% 0.20/0.52    inference(resolution,[],[f40,f26])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.52    inference(flattening,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (22238)------------------------------
% 0.20/0.52  % (22238)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (22238)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (22238)Memory used [KB]: 10746
% 0.20/0.52  % (22238)Time elapsed: 0.060 s
% 0.20/0.52  % (22238)------------------------------
% 0.20/0.52  % (22238)------------------------------
% 0.20/0.52  % (22215)Success in time 0.153 s
%------------------------------------------------------------------------------
