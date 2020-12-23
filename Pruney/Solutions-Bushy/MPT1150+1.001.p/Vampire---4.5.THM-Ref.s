%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1150+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 737 expanded)
%              Number of leaves         :   21 ( 193 expanded)
%              Depth                    :   25
%              Number of atoms          :  562 (3959 expanded)
%              Number of equality atoms :   57 ( 570 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f440,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f164,f165,f356,f385,f422])).

fof(f422,plain,(
    ~ spl5_24 ),
    inference(avatar_contradiction_clause,[],[f421])).

fof(f421,plain,
    ( $false
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f420,f111])).

fof(f111,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f109,f71])).

fof(f71,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f47,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f47,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f17,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0))
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( k1_xboole_0 != k1_orders_2(X0,k2_struct_0(X0))
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k1_orders_2(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_orders_2)).

fof(f109,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0) ),
    inference(superposition,[],[f52,f107])).

fof(f107,plain,(
    k2_struct_0(sK0) = u1_struct_0(sK0) ),
    inference(resolution,[],[f71,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f52,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f420,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_24 ),
    inference(subsumption_resolution,[],[f409,f108])).

fof(f108,plain,(
    k1_xboole_0 != k1_orders_2(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f48,f107])).

fof(f48,plain,(
    k1_xboole_0 != k1_orders_2(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f35])).

fof(f409,plain,
    ( k1_xboole_0 = k1_orders_2(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_24 ),
    inference(superposition,[],[f81,f355])).

fof(f355,plain,
    ( k1_xboole_0 = a_2_0_orders_2(sK0,u1_struct_0(sK0))
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f353])).

fof(f353,plain,
    ( spl5_24
  <=> k1_xboole_0 = a_2_0_orders_2(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f81,plain,(
    ! [X0] :
      ( k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f80,f43])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f80,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f79,f44])).

fof(f44,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f78,f45])).

fof(f45,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f78,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f70,f46])).

fof(f46,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k1_orders_2(sK0,X0) = a_2_0_orders_2(sK0,X0)
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f47,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_orders_2(X0,X1) = a_2_0_orders_2(X0,X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f385,plain,
    ( spl5_24
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f384,f350,f353])).

fof(f350,plain,
    ( spl5_23
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(a_2_0_orders_2(sK0,u1_struct_0(sK0))),a_2_0_orders_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f384,plain,
    ( k1_xboole_0 = a_2_0_orders_2(sK0,u1_struct_0(sK0))
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f380,f111])).

fof(f380,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = a_2_0_orders_2(sK0,u1_struct_0(sK0))
    | ~ spl5_23 ),
    inference(resolution,[],[f373,f61])).

fof(f61,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] : m1_subset_1(sK3(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f6,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f373,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(a_2_0_orders_2(sK0,u1_struct_0(sK0))),a_2_0_orders_2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = a_2_0_orders_2(sK0,X0) )
    | ~ spl5_23 ),
    inference(resolution,[],[f357,f53])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

fof(f357,plain,
    ( ! [X0] :
        ( v1_xboole_0(a_2_0_orders_2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK3(a_2_0_orders_2(sK0,u1_struct_0(sK0))),a_2_0_orders_2(sK0,X0)) )
    | ~ spl5_23 ),
    inference(resolution,[],[f351,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f351,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK3(a_2_0_orders_2(sK0,u1_struct_0(sK0))),a_2_0_orders_2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f350])).

fof(f356,plain,
    ( spl5_23
    | spl5_24
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f348,f118,f353,f350])).

fof(f118,plain,
    ( spl5_1
  <=> sP4(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f348,plain,
    ( ! [X0] :
        ( k1_xboole_0 = a_2_0_orders_2(sK0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(a_2_0_orders_2(sK0,u1_struct_0(sK0))),a_2_0_orders_2(sK0,X0)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f347,f113])).

fof(f113,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f112,f43])).

fof(f112,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f110,f71])).

fof(f110,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | ~ l1_struct_0(sK0)
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f51,f107])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f347,plain,
    ( ! [X0] :
        ( v1_xboole_0(u1_struct_0(sK0))
        | k1_xboole_0 = a_2_0_orders_2(sK0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(a_2_0_orders_2(sK0,u1_struct_0(sK0))),a_2_0_orders_2(sK0,X0)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f344,f111])).

fof(f344,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(u1_struct_0(sK0))
        | k1_xboole_0 = a_2_0_orders_2(sK0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK3(a_2_0_orders_2(sK0,u1_struct_0(sK0))),a_2_0_orders_2(sK0,X0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f341,f116])).

fof(f116,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(duplicate_literal_removal,[],[f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) ) ),
    inference(superposition,[],[f85,f89])).

fof(f89,plain,(
    ! [X4,X3] :
      ( sK2(X3,sK0,X4) = X3
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X3,a_2_0_orders_2(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f88,f43])).

fof(f88,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_0_orders_2(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X3,sK0,X4) = X3
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f87,f44])).

fof(f87,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_0_orders_2(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X3,sK0,X4) = X3
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f86,f45])).

fof(f86,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_0_orders_2(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X3,sK0,X4) = X3
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f73,f46])).

fof(f73,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,a_2_0_orders_2(sK0,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | sK2(X3,sK0,X4) = X3
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f47,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | sK2(X0,X1,X2) = X0
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,a_2_0_orders_2(X1,X2))
          | ! [X3] :
              ( ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
                & r2_hidden(sK1(X1,X2,X3),X2)
                & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) )
              | X0 != X3
              | ~ m1_subset_1(X3,u1_struct_0(X1)) ) )
        & ( ( ! [X6] :
                ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
                | ~ r2_hidden(X6,X2)
                | ~ m1_subset_1(X6,u1_struct_0(X1)) )
            & sK2(X0,X1,X2) = X0
            & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) )
          | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2)) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f37,f39,f38])).

fof(f38,plain,(
    ! [X3,X2,X1] :
      ( ? [X4] :
          ( ~ r2_orders_2(X1,X4,X3)
          & r2_hidden(X4,X2)
          & m1_subset_1(X4,u1_struct_0(X1)) )
     => ( ~ r2_orders_2(X1,sK1(X1,X2,X3),X3)
        & r2_hidden(sK1(X1,X2,X3),X2)
        & m1_subset_1(sK1(X1,X2,X3),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X5] :
          ( ! [X6] :
              ( r2_orders_2(X1,X6,X5)
              | ~ r2_hidden(X6,X2)
              | ~ m1_subset_1(X6,u1_struct_0(X1)) )
          & X0 = X5
          & m1_subset_1(X5,u1_struct_0(X1)) )
     => ( ! [X6] :
            ( r2_orders_2(X1,X6,sK2(X0,X1,X2))
            | ~ r2_hidden(X6,X2)
            | ~ m1_subset_1(X6,u1_struct_0(X1)) )
        & sK2(X0,X1,X2) = X0
        & m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f27])).

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

fof(f85,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK2(X1,sK0,X2),u1_struct_0(sK0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f84,f43])).

fof(f84,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X2),u1_struct_0(sK0))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f83,f44])).

fof(f83,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X2),u1_struct_0(sK0))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f82,f45])).

fof(f82,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X2),u1_struct_0(sK0))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f72,f46])).

fof(f72,plain,(
    ! [X2,X1] :
      ( ~ r2_hidden(X1,a_2_0_orders_2(sK0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(sK2(X1,sK0,X2),u1_struct_0(sK0))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f47,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(sK2(X0,X1,X2),u1_struct_0(X1))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f341,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3(a_2_0_orders_2(sK0,X0)),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | k1_xboole_0 = a_2_0_orders_2(sK0,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f186,f61])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,a_2_0_orders_2(sK0,X0))
        | ~ m1_subset_1(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | k1_xboole_0 = a_2_0_orders_2(sK0,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f174,f53])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(a_2_0_orders_2(sK0,X0))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,a_2_0_orders_2(sK0,X0)) )
    | ~ spl5_1 ),
    inference(resolution,[],[f173,f62])).

fof(f173,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X1,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f172,f62])).

fof(f172,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) )
    | ~ spl5_1 ),
    inference(duplicate_literal_removal,[],[f171])).

fof(f171,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) )
    | ~ spl5_1 ),
    inference(superposition,[],[f169,f89])).

fof(f169,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(sK2(X0,sK0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f168,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f168,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2(X0,sK0,X1),u1_struct_0(sK0))
        | ~ r2_hidden(X0,a_2_0_orders_2(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2(X0,sK0,X1),X1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f167,f94])).

fof(f94,plain,(
    ! [X6,X7,X5] :
      ( r2_orders_2(sK0,X5,sK2(X7,sK0,X6))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X5,X6) ) ),
    inference(subsumption_resolution,[],[f93,f64])).

fof(f93,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X5,sK2(X7,sK0,X6)) ) ),
    inference(subsumption_resolution,[],[f92,f43])).

fof(f92,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X5,sK2(X7,sK0,X6))
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f91,f44])).

fof(f91,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X5,sK2(X7,sK0,X6))
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f90,f45])).

fof(f90,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X5,sK2(X7,sK0,X6))
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f74,f46])).

fof(f74,plain,(
    ! [X6,X7,X5] :
      ( ~ r2_hidden(X5,X6)
      | ~ m1_subset_1(X5,u1_struct_0(sK0))
      | ~ r2_hidden(X7,a_2_0_orders_2(sK0,X6))
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_orders_2(sK0,X5,sK2(X7,sK0,X6))
      | ~ v5_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v3_orders_2(sK0)
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f47,f57])).

fof(f57,plain,(
    ! [X6,X2,X0,X1] :
      ( ~ l1_orders_2(X1)
      | ~ r2_hidden(X6,X2)
      | ~ m1_subset_1(X6,u1_struct_0(X1))
      | ~ r2_hidden(X0,a_2_0_orders_2(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | r2_orders_2(X1,X6,sK2(X0,X1,X2))
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r2_orders_2(sK0,X0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_1 ),
    inference(subsumption_resolution,[],[f166,f47])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_orders_2(sK0)
        | ~ r2_orders_2(sK0,X0,X0) )
    | ~ spl5_1 ),
    inference(resolution,[],[f120,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ sP4(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ r2_orders_2(X0,X1,X1) ) ),
    inference(general_splitting,[],[f63,f68_D])).

fof(f68,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,u1_struct_0(X0))
      | sP4(X0) ) ),
    inference(cnf_transformation,[],[f68_D])).

fof(f68_D,plain,(
    ! [X0] :
      ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(X0))
    <=> ~ sP4(X0) ) ),
    introduced(general_splitting_component_introduction,[new_symbols(naming,[sP4])])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ~ r2_orders_2(X0,X1,X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_orders_2(X0) )
     => ~ r2_orders_2(X0,X1,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',irreflexivity_r2_orders_2)).

fof(f120,plain,
    ( sP4(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f118])).

fof(f165,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f129,f122,f118])).

fof(f122,plain,
    ( spl5_2
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0))
      | sP4(sK0) ) ),
    inference(resolution,[],[f116,f68])).

fof(f164,plain,(
    ~ spl5_2 ),
    inference(avatar_contradiction_clause,[],[f163])).

fof(f163,plain,
    ( $false
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f162,f111])).

fof(f162,plain,
    ( ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(subsumption_resolution,[],[f148,f108])).

fof(f148,plain,
    ( k1_xboole_0 = k1_orders_2(sK0,u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_2 ),
    inference(superposition,[],[f81,f139])).

fof(f139,plain,
    ( k1_xboole_0 = a_2_0_orders_2(sK0,u1_struct_0(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f134,f111])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = a_2_0_orders_2(sK0,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f130,f61])).

fof(f130,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,a_2_0_orders_2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = a_2_0_orders_2(sK0,X0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f125,f53])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(a_2_0_orders_2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,a_2_0_orders_2(sK0,X0)) )
    | ~ spl5_2 ),
    inference(resolution,[],[f123,f62])).

fof(f123,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,a_2_0_orders_2(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f122])).

%------------------------------------------------------------------------------
