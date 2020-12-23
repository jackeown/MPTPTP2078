%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:26 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 195 expanded)
%              Number of leaves         :   13 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  303 ( 863 expanded)
%              Number of equality atoms :   23 ( 108 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f145,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f73,f79,f102,f135])).

fof(f135,plain,(
    ~ spl4_3 ),
    inference(avatar_contradiction_clause,[],[f134])).

fof(f134,plain,
    ( $false
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f132,f78])).

fof(f78,plain,
    ( r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_3
  <=> r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f132,plain,(
    ~ r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f131,f52])).

fof(f52,plain,(
    ! [X0] : ~ r2_hidden(X0,o_0_0_xboole_0) ),
    inference(resolution,[],[f38,f29])).

fof(f29,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f131,plain,(
    ! [X0] :
      ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)
      | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) ) ),
    inference(resolution,[],[f130,f117])).

fof(f117,plain,(
    ! [X0] :
      ( m2_orders_2(X0,sK0,sK1)
      | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) ) ),
    inference(resolution,[],[f116,f22])).

fof(f22,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).

fof(f116,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | m2_orders_2(X1,sK0,X0)
      | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f115,f24])).

fof(f24,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f115,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | m2_orders_2(X1,sK0,X0)
      | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f114,f27])).

fof(f27,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | m2_orders_2(X1,sK0,X0)
      | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f113,f26])).

fof(f26,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f113,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | m2_orders_2(X1,sK0,X0)
      | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f112,f25])).

fof(f25,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f112,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | m2_orders_2(X1,sK0,X0)
      | ~ r2_hidden(X1,k4_orders_2(sK0,X0)) ) ),
    inference(resolution,[],[f44,f28])).

fof(f28,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(X3,X0,X1)
      | ~ r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( k4_orders_2(X0,X1) = X2
            <=> ! [X3] :
                  ( r2_hidden(X3,X2)
                <=> m2_orders_2(X3,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).

fof(f130,plain,(
    ! [X0] :
      ( ~ m2_orders_2(X0,sK0,sK1)
      | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) ) ),
    inference(resolution,[],[f129,f22])).

fof(f129,plain,(
    ! [X0,X1] :
      ( ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f128,f24])).

fof(f128,plain,(
    ! [X0,X1] :
      ( v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f127,f27])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f126,f26])).

fof(f126,plain,(
    ! [X0,X1] :
      ( ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(subsumption_resolution,[],[f125,f25])).

fof(f125,plain,(
    ! [X0,X1] :
      ( ~ v3_orders_2(sK0)
      | ~ v4_orders_2(sK0)
      | ~ v5_orders_2(sK0)
      | v2_struct_0(sK0)
      | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
      | ~ m2_orders_2(X1,sK0,X0)
      | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1) ) ),
    inference(resolution,[],[f32,f28])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)
              | ~ m2_orders_2(X2,X0,X1) )
          | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
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
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m2_orders_2(X2,X0,X1)
             => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).

fof(f102,plain,(
    ~ spl4_1 ),
    inference(avatar_contradiction_clause,[],[f101])).

fof(f101,plain,
    ( $false
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f100,f24])).

fof(f100,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f99,f22])).

fof(f99,plain,
    ( ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f98,f28])).

fof(f98,plain,
    ( ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f97,f27])).

fof(f97,plain,
    ( ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f96,f26])).

fof(f96,plain,
    ( ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f95,f25])).

fof(f95,plain,
    ( ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(subsumption_resolution,[],[f94,f29])).

fof(f94,plain,
    ( ~ v1_xboole_0(o_0_0_xboole_0)
    | ~ v3_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ l1_orders_2(sK0)
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ spl4_1 ),
    inference(superposition,[],[f40,f80])).

fof(f80,plain,
    ( o_0_0_xboole_0 = k4_orders_2(sK0,sK1)
    | ~ spl4_1 ),
    inference(resolution,[],[f68,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | o_0_0_xboole_0 = X0 ) ),
    inference(backward_demodulation,[],[f31,f48])).

fof(f48,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(resolution,[],[f31,f29])).

fof(f31,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f68,plain,
    ( v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f66,plain,
    ( spl4_1
  <=> v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(k4_orders_2(X0,X1))
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k4_orders_2(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).

fof(f79,plain,
    ( spl4_1
    | spl4_3
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f74,f70,f76,f66])).

fof(f70,plain,
    ( spl4_2
  <=> o_0_0_xboole_0 = sK3(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f74,plain,
    ( r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1))
    | v1_xboole_0(k4_orders_2(sK0,sK1))
    | ~ spl4_2 ),
    inference(superposition,[],[f37,f72])).

fof(f72,plain,
    ( o_0_0_xboole_0 = sK3(k4_orders_2(sK0,sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f70])).

fof(f37,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f73,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f64,f70,f66])).

fof(f64,plain,
    ( o_0_0_xboole_0 = sK3(k4_orders_2(sK0,sK1))
    | v1_xboole_0(k4_orders_2(sK0,sK1)) ),
    inference(resolution,[],[f60,f37])).

fof(f60,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,k4_orders_2(sK0,sK1))
      | o_0_0_xboole_0 = X4 ) ),
    inference(subsumption_resolution,[],[f59,f50])).

fof(f50,plain,(
    ! [X0] : r1_tarski(o_0_0_xboole_0,X0) ),
    inference(backward_demodulation,[],[f30,f48])).

fof(f30,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f59,plain,(
    ! [X4] :
      ( ~ r1_tarski(o_0_0_xboole_0,X4)
      | o_0_0_xboole_0 = X4
      | ~ r2_hidden(X4,k4_orders_2(sK0,sK1)) ) ),
    inference(resolution,[],[f43,f55])).

fof(f55,plain,(
    ! [X0] :
      ( r1_tarski(X0,o_0_0_xboole_0)
      | ~ r2_hidden(X0,k4_orders_2(sK0,sK1)) ) ),
    inference(superposition,[],[f39,f51])).

fof(f51,plain,(
    o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(backward_demodulation,[],[f23,f48])).

fof(f23,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,k3_tarski(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => r1_tarski(X0,k3_tarski(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:47:29 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.46  % (10111)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.48  % (10119)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.22/0.48  % (10101)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.49  % (10103)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.22/0.49  % (10119)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f73,f79,f102,f135])).
% 0.22/0.49  fof(f135,plain,(
% 0.22/0.49    ~spl4_3),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f134])).
% 0.22/0.49  fof(f134,plain,(
% 0.22/0.49    $false | ~spl4_3),
% 0.22/0.49    inference(subsumption_resolution,[],[f132,f78])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1)) | ~spl4_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    spl4_3 <=> r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    ~r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f131,f52])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0] : (~r2_hidden(X0,o_0_0_xboole_0)) )),
% 0.22/0.49    inference(resolution,[],[f38,f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    v1_xboole_0(o_0_0_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) )),
% 0.22/0.49    inference(resolution,[],[f130,f117])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ( ! [X0] : (m2_orders_2(X0,sK0,sK1) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) )),
% 0.22/0.49    inference(resolution,[],[f116,f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_orders_2)).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f115,f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f114,f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    v5_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f113,f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    v4_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f113,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f112,f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    v3_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(X1,sK0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,X0))) )),
% 0.22/0.49    inference(resolution,[],[f44,f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    l1_orders_2(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.22/0.49    inference(equality_resolution,[],[f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(X3,X0,X1) | ~r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d17_orders_2)).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)) )),
% 0.22/0.49    inference(resolution,[],[f129,f22])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f128,f24])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    ( ! [X0,X1] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f127,f27])).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f126,f26])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f125,f25])).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X1,sK0,X0) | r2_hidden(k1_funct_1(X0,u1_struct_0(sK0)),X1)) )),
% 0.22/0.49    inference(resolution,[],[f32,f28])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_orders_2)).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ~spl4_1),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f101])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    $false | ~spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f100,f24])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f99,f22])).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f98,f28])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f97,f27])).
% 0.22/0.49  fof(f97,plain,(
% 0.22/0.49    ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f96,f26])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f95,f25])).
% 0.22/0.49  fof(f95,plain,(
% 0.22/0.49    ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_1),
% 0.22/0.49    inference(subsumption_resolution,[],[f94,f29])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ~v1_xboole_0(o_0_0_xboole_0) | ~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | ~l1_orders_2(sK0) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~spl4_1),
% 0.22/0.49    inference(superposition,[],[f40,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    o_0_0_xboole_0 = k4_orders_2(sK0,sK1) | ~spl4_1),
% 0.22/0.49    inference(resolution,[],[f68,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | o_0_0_xboole_0 = X0) )),
% 0.22/0.49    inference(backward_demodulation,[],[f31,f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    o_0_0_xboole_0 = k1_xboole_0),
% 0.22/0.49    inference(resolution,[],[f31,f29])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    v1_xboole_0(k4_orders_2(sK0,sK1)) | ~spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f66])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl4_1 <=> v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0,X1] : (~v1_xboole_0(k4_orders_2(X0,X1)) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k4_orders_2(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_orders_2)).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    spl4_1 | spl4_3 | ~spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f74,f70,f76,f66])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    spl4_2 <=> o_0_0_xboole_0 = sK3(k4_orders_2(sK0,sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    r2_hidden(o_0_0_xboole_0,k4_orders_2(sK0,sK1)) | v1_xboole_0(k4_orders_2(sK0,sK1)) | ~spl4_2),
% 0.22/0.49    inference(superposition,[],[f37,f72])).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    o_0_0_xboole_0 = sK3(k4_orders_2(sK0,sK1)) | ~spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f70])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl4_1 | spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f64,f70,f66])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    o_0_0_xboole_0 = sK3(k4_orders_2(sK0,sK1)) | v1_xboole_0(k4_orders_2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f60,f37])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ( ! [X4] : (~r2_hidden(X4,k4_orders_2(sK0,sK1)) | o_0_0_xboole_0 = X4) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f59,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(o_0_0_xboole_0,X0)) )),
% 0.22/0.49    inference(backward_demodulation,[],[f30,f48])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ( ! [X4] : (~r1_tarski(o_0_0_xboole_0,X4) | o_0_0_xboole_0 = X4 | ~r2_hidden(X4,k4_orders_2(sK0,sK1))) )),
% 0.22/0.49    inference(resolution,[],[f43,f55])).
% 0.22/0.49  fof(f55,plain,(
% 0.22/0.49    ( ! [X0] : (r1_tarski(X0,o_0_0_xboole_0) | ~r2_hidden(X0,k4_orders_2(sK0,sK1))) )),
% 0.22/0.49    inference(superposition,[],[f39,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    o_0_0_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.49    inference(backward_demodulation,[],[f23,f48])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f13])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,k3_tarski(X1)) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_hidden(X0,X1) => r1_tarski(X0,k3_tarski(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (10119)------------------------------
% 0.22/0.49  % (10119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (10119)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (10119)Memory used [KB]: 10618
% 0.22/0.49  % (10119)Time elapsed: 0.075 s
% 0.22/0.49  % (10119)------------------------------
% 0.22/0.49  % (10119)------------------------------
% 0.22/0.49  % (10100)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.49  % (10096)Success in time 0.125 s
%------------------------------------------------------------------------------
