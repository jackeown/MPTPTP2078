%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1659+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:16 EST 2020

% Result     : Theorem 0.11s
% Output     : Refutation 0.11s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 217 expanded)
%              Number of leaves         :   24 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  388 ( 932 expanded)
%              Number of equality atoms :   38 ( 111 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f155,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f64,f92,f98,f101,f105,f112,f117,f120,f123,f124,f126,f135,f137,f147])).

fof(f147,plain,
    ( ~ spl2_11
    | spl2_7
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_10
    | spl2_1
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f145,f96,f71,f59,f51,f85,f132,f79,f76,f88])).

fof(f88,plain,
    ( spl2_11
  <=> r2_yellow_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f76,plain,
    ( spl2_7
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f79,plain,
    ( spl2_8
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f132,plain,
    ( spl2_14
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f85,plain,
    ( spl2_10
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f51,plain,
    ( spl2_1
  <=> sK1 = k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f59,plain,
    ( spl2_3
  <=> k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f71,plain,
    ( spl2_6
  <=> m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f96,plain,
    ( spl2_12
  <=> k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k1_tarski(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f145,plain,
    ( sK1 = k2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ r2_yellow_0(sK0,k1_tarski(sK1))
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f144,f140])).

fof(f140,plain,
    ( sK1 = k2_yellow_0(sK0,k1_tarski(sK1))
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f107,f60])).

fof(f60,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f107,plain,(
    sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(global_subsumption,[],[f34,f35,f37,f38,f106])).

fof(f106,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | sK1 = k2_yellow_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
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
          ( ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) != X1
            | ~ r2_yellow_0(X0,k6_waybel_0(X0,X1)) )
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
           => ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1
              & r2_yellow_0(X0,k6_waybel_0(X0,X1)) ) ) ) ),
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
         => ( k2_yellow_0(X0,k6_waybel_0(X0,X1)) = X1
            & r2_yellow_0(X0,k6_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_waybel_0)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( k2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1
            & k1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_yellow_0)).

fof(f38,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f35,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f144,plain,
    ( k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) = k2_yellow_0(sK0,k1_tarski(sK1))
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ r2_yellow_0(sK0,k1_tarski(sK1))
    | ~ spl2_6
    | ~ spl2_12 ),
    inference(forward_demodulation,[],[f142,f97])).

fof(f97,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k1_tarski(sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f96])).

fof(f142,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ r2_yellow_0(sK0,k1_tarski(sK1))
    | k2_yellow_0(sK0,k1_tarski(sK1)) = k2_yellow_0(sK0,k4_waybel_0(sK0,k1_tarski(sK1)))
    | ~ spl2_6 ),
    inference(resolution,[],[f72,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | ~ r2_yellow_0(X0,X1)
      | k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1))
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1))
          | ~ r2_yellow_0(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
           => k2_yellow_0(X0,X1) = k2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_waybel_0)).

fof(f72,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f137,plain,(
    spl2_14 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl2_14 ),
    inference(resolution,[],[f133,f36])).

fof(f36,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f133,plain,
    ( ~ v4_orders_2(sK0)
    | spl2_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f135,plain,
    ( ~ spl2_11
    | spl2_7
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_14
    | ~ spl2_10
    | spl2_2
    | ~ spl2_12 ),
    inference(avatar_split_clause,[],[f127,f96,f54,f85,f132,f79,f71,f76,f88])).

fof(f54,plain,
    ( spl2_2
  <=> r2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f127,plain,
    ( r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ r2_yellow_0(sK0,k1_tarski(sK1))
    | ~ spl2_12 ),
    inference(superposition,[],[f46,f97])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,k4_waybel_0(X0,X1))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ r2_yellow_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_yellow_0(X0,X1)
          <=> r2_yellow_0(X0,k4_waybel_0(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_waybel_0)).

fof(f126,plain,(
    spl2_5 ),
    inference(avatar_contradiction_clause,[],[f125])).

fof(f125,plain,
    ( $false
    | spl2_5 ),
    inference(resolution,[],[f69,f33])).

fof(f69,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl2_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f124,plain,
    ( spl2_4
    | ~ spl2_5
    | spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f122,f59,f71,f68,f62])).

fof(f62,plain,
    ( spl2_4
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f122,plain,
    ( m1_subset_1(k1_tarski(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(superposition,[],[f49,f60])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f123,plain,
    ( spl2_7
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_10
    | spl2_11
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f121,f59,f88,f85,f82,f79,f68,f76])).

fof(f82,plain,
    ( spl2_9
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f121,plain,
    ( r2_yellow_0(sK0,k1_tarski(sK1))
    | ~ v3_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ spl2_3 ),
    inference(superposition,[],[f41,f60])).

fof(f41,plain,(
    ! [X0,X1] :
      ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v3_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ( r2_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1))
            & r1_yellow_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_yellow_0)).

fof(f120,plain,(
    ~ spl2_7 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | ~ spl2_7 ),
    inference(resolution,[],[f77,f34])).

fof(f77,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f76])).

fof(f117,plain,(
    spl2_13 ),
    inference(avatar_contradiction_clause,[],[f116])).

fof(f116,plain,
    ( $false
    | spl2_13 ),
    inference(resolution,[],[f113,f38])).

fof(f113,plain,
    ( ~ l1_orders_2(sK0)
    | spl2_13 ),
    inference(resolution,[],[f111,f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f111,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_13 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl2_13
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f112,plain,
    ( spl2_7
    | ~ spl2_13
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f108,f62,f110,f76])).

fof(f108,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_4 ),
    inference(resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f63,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f62])).

fof(f105,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f104])).

fof(f104,plain,
    ( $false
    | spl2_10 ),
    inference(resolution,[],[f86,f35])).

fof(f86,plain,
    ( ~ v3_orders_2(sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f101,plain,(
    spl2_9 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl2_9 ),
    inference(resolution,[],[f83,f37])).

fof(f83,plain,
    ( ~ v5_orders_2(sK0)
    | spl2_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f98,plain,
    ( spl2_7
    | ~ spl2_8
    | spl2_12
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f94,f59,f96,f79,f76])).

fof(f94,plain,
    ( k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k1_tarski(sK1))
    | ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_3 ),
    inference(forward_demodulation,[],[f93,f60])).

fof(f93,plain,
    ( ~ l1_orders_2(sK0)
    | v2_struct_0(sK0)
    | k6_waybel_0(sK0,sK1) = k4_waybel_0(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f47,f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0)
      | k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1))
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k6_waybel_0(X0,X1) = k4_waybel_0(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_waybel_0)).

fof(f92,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f80,f38])).

fof(f80,plain,
    ( ~ l1_orders_2(sK0)
    | spl2_8 ),
    inference(avatar_component_clause,[],[f79])).

fof(f64,plain,
    ( spl2_3
    | spl2_4 ),
    inference(avatar_split_clause,[],[f57,f62,f59])).

fof(f57,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | k6_domain_1(u1_struct_0(sK0),sK1) = k1_tarski(sK1) ),
    inference(resolution,[],[f48,f33])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f56,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f32,f54,f51])).

fof(f32,plain,
    ( ~ r2_yellow_0(sK0,k6_waybel_0(sK0,sK1))
    | sK1 != k2_yellow_0(sK0,k6_waybel_0(sK0,sK1)) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
