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
% DateTime   : Thu Dec  3 13:10:33 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 178 expanded)
%              Number of leaves         :   16 (  62 expanded)
%              Depth                    :   14
%              Number of atoms          :  397 ( 742 expanded)
%              Number of equality atoms :   11 (  36 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f137,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f97,f102,f114,f128,f136])).

fof(f136,plain,
    ( ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f135])).

fof(f135,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f134,f115])).

fof(f115,plain,
    ( ! [X0] : r1_tarski(sK3(sK0,sK1),X0)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(resolution,[],[f113,f104])).

fof(f104,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k4_orders_2(sK0,sK1))
        | r1_tarski(X1,X0) )
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f103,f27])).

fof(f27,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(k1_xboole_0,X0)
        | ~ r2_hidden(X1,k4_orders_2(sK0,sK1))
        | r1_tarski(X1,X0) )
    | ~ spl4_7 ),
    inference(superposition,[],[f35,f101])).

fof(f101,plain,
    ( k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_7
  <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k3_tarski(X0),X1)
      | ~ r2_hidden(X2,X0)
      | r1_tarski(X2,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(k3_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X2,X0)
        & r1_tarski(k3_tarski(X0),X1) )
     => r1_tarski(X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).

fof(f113,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f111,plain,
    ( spl4_8
  <=> r2_hidden(sK3(sK0,sK1),k4_orders_2(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f134,plain,
    ( ~ r1_tarski(sK3(sK0,sK1),k1_funct_1(sK1,u1_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(resolution,[],[f127,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f127,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3(sK0,sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl4_9
  <=> r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f128,plain,
    ( spl4_9
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f119,f94,f59,f54,f49,f44,f39,f125])).

fof(f39,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f44,plain,
    ( spl4_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f49,plain,
    ( spl4_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f54,plain,
    ( spl4_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f59,plain,
    ( spl4_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f94,plain,
    ( spl4_6
  <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f119,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f118,f96])).

fof(f96,plain,
    ( m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f118,plain,
    ( r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3(sK0,sK1))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f106,f72])).

fof(f72,plain,
    ( ! [X0] :
        ( m2_orders_2(sK3(sK0,X0),sK0,X0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f71,f41])).

fof(f41,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f39])).

fof(f71,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK3(sK0,X0),sK0,X0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f70,f56])).

fof(f56,plain,
    ( v5_orders_2(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f54])).

fof(f70,plain,
    ( ! [X0] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK3(sK0,X0),sK0,X0) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f69,f51])).

fof(f51,plain,
    ( v4_orders_2(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f49])).

fof(f69,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK3(sK0,X0),sK0,X0) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f63,f46])).

fof(f46,plain,
    ( v3_orders_2(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f44])).

fof(f63,plain,
    ( ! [X0] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))
        | m2_orders_2(sK3(sK0,X0),sK0,X0) )
    | ~ spl4_5 ),
    inference(resolution,[],[f61,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | m2_orders_2(sK3(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ? [X2] : m2_orders_2(X2,X0,X1)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m2_orders_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).

fof(f61,plain,
    ( l1_orders_2(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f59])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f92,f96])).

fof(f92,plain,
    ( ! [X10,X9] :
        ( ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f91,f41])).

fof(f91,plain,
    ( ! [X10,X9] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f90,f56])).

fof(f90,plain,
    ( ! [X10,X9] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f89,f51])).

fof(f89,plain,
    ( ! [X10,X9] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f68,f46])).

fof(f68,plain,
    ( ! [X10,X9] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X10,sK0,X9)
        | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10) )
    | ~ spl4_5 ),
    inference(resolution,[],[f61,f28])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X2,X0,X1)
      | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).

fof(f114,plain,
    ( spl4_8
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f108,f94,f59,f54,f49,f44,f39,f111])).

fof(f108,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_orders_2(sK0,sK1))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f107,f96])).

fof(f107,plain,
    ( r2_hidden(sK3(sK0,sK1),k4_orders_2(sK0,sK1))
    | ~ m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f105,f72])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ m2_orders_2(X0,sK0,sK1)
        | r2_hidden(X0,k4_orders_2(sK0,sK1)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6 ),
    inference(resolution,[],[f76,f96])).

fof(f76,plain,
    ( ! [X2,X1] :
        ( ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f75,f41])).

fof(f75,plain,
    ( ! [X2,X1] :
        ( v2_struct_0(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f74,f56])).

fof(f74,plain,
    ( ! [X2,X1] :
        ( ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f73,f51])).

fof(f73,plain,
    ( ! [X2,X1] :
        ( ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f64,f46])).

fof(f64,plain,
    ( ! [X2,X1] :
        ( ~ v3_orders_2(sK0)
        | ~ v4_orders_2(sK0)
        | ~ v5_orders_2(sK0)
        | v2_struct_0(sK0)
        | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0)))
        | ~ m2_orders_2(X2,sK0,X1)
        | r2_hidden(X2,k4_orders_2(sK0,X1)) )
    | ~ spl4_5 ),
    inference(resolution,[],[f61,f37])).

fof(f37,plain,(
    ! [X0,X3,X1] :
      ( ~ l1_orders_2(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,k4_orders_2(X0,X1)) ) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v3_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
      | ~ m2_orders_2(X3,X0,X1)
      | r2_hidden(X3,X2)
      | k4_orders_2(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).

fof(f102,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f21,f99])).

fof(f21,plain,(
    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1))
          & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) )
      & l1_orders_2(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
           => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))
         => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).

fof(f97,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f20,f94])).

fof(f20,plain,(
    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f62,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f26,f59])).

fof(f26,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f57,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f25,f54])).

fof(f25,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f52,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f24,f49])).

fof(f24,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f47,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f44])).

fof(f23,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f42,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f22,f39])).

fof(f22,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:44:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (19862)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.47  % (19855)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.47  % (19863)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.48  % (19855)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (19869)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.48  % (19867)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (19853)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.48  % (19856)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.48  % (19872)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.48  % (19852)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.49  % (19853)Refutation not found, incomplete strategy% (19853)------------------------------
% 0.20/0.49  % (19853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19853)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.49  
% 0.20/0.49  % (19853)Memory used [KB]: 10618
% 0.20/0.49  % (19853)Time elapsed: 0.070 s
% 0.20/0.49  % (19853)------------------------------
% 0.20/0.49  % (19853)------------------------------
% 0.20/0.49  % (19866)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f42,f47,f52,f57,f62,f97,f102,f114,f128,f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    ~spl4_7 | ~spl4_8 | ~spl4_9),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f135])).
% 0.20/0.49  fof(f135,plain,(
% 0.20/0.49    $false | (~spl4_7 | ~spl4_8 | ~spl4_9)),
% 0.20/0.49    inference(subsumption_resolution,[],[f134,f115])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(sK3(sK0,sK1),X0)) ) | (~spl4_7 | ~spl4_8)),
% 0.20/0.49    inference(resolution,[],[f113,f104])).
% 0.20/0.49  fof(f104,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X1,k4_orders_2(sK0,sK1)) | r1_tarski(X1,X0)) ) | ~spl4_7),
% 0.20/0.49    inference(subsumption_resolution,[],[f103,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(k1_xboole_0,X0) | ~r2_hidden(X1,k4_orders_2(sK0,sK1)) | r1_tarski(X1,X0)) ) | ~spl4_7),
% 0.20/0.49    inference(superposition,[],[f35,f101])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1)) | ~spl4_7),
% 0.20/0.49    inference(avatar_component_clause,[],[f99])).
% 0.20/0.49  fof(f99,plain,(
% 0.20/0.49    spl4_7 <=> k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~r1_tarski(k3_tarski(X0),X1) | ~r2_hidden(X2,X0) | r1_tarski(X2,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1))),
% 0.20/0.49    inference(flattening,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ! [X0,X1,X2] : (r1_tarski(X2,X1) | (~r2_hidden(X2,X0) | ~r1_tarski(k3_tarski(X0),X1)))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1,X2] : ((r2_hidden(X2,X0) & r1_tarski(k3_tarski(X0),X1)) => r1_tarski(X2,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_setfam_1)).
% 0.20/0.49  fof(f113,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK1),k4_orders_2(sK0,sK1)) | ~spl4_8),
% 0.20/0.49    inference(avatar_component_clause,[],[f111])).
% 0.20/0.49  fof(f111,plain,(
% 0.20/0.49    spl4_8 <=> r2_hidden(sK3(sK0,sK1),k4_orders_2(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.49  fof(f134,plain,(
% 0.20/0.49    ~r1_tarski(sK3(sK0,sK1),k1_funct_1(sK1,u1_struct_0(sK0))) | ~spl4_9),
% 0.20/0.49    inference(resolution,[],[f127,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_tarski(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3(sK0,sK1)) | ~spl4_9),
% 0.20/0.49    inference(avatar_component_clause,[],[f125])).
% 0.20/0.49  fof(f125,plain,(
% 0.20/0.49    spl4_9 <=> r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3(sK0,sK1))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.49  fof(f128,plain,(
% 0.20/0.49    spl4_9 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f119,f94,f59,f54,f49,f44,f39,f125])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    spl4_1 <=> v2_struct_0(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    spl4_2 <=> v3_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.49  fof(f49,plain,(
% 0.20/0.49    spl4_3 <=> v4_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    spl4_4 <=> v5_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.49  fof(f59,plain,(
% 0.20/0.49    spl4_5 <=> l1_orders_2(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.49  fof(f94,plain,(
% 0.20/0.49    spl4_6 <=> m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.49  fof(f119,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f118,f96])).
% 0.20/0.49  fof(f96,plain,(
% 0.20/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f94])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),sK3(sK0,sK1)) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.20/0.49    inference(resolution,[],[f106,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    ( ! [X0] : (m2_orders_2(sK3(sK0,X0),sK0,X0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f71,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ~v2_struct_0(sK0) | spl4_1),
% 0.20/0.49    inference(avatar_component_clause,[],[f39])).
% 0.20/0.49  fof(f71,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK3(sK0,X0),sK0,X0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f70,f56])).
% 0.20/0.49  fof(f56,plain,(
% 0.20/0.49    v5_orders_2(sK0) | ~spl4_4),
% 0.20/0.49    inference(avatar_component_clause,[],[f54])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK3(sK0,X0),sK0,X0)) ) | (~spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f69,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    v4_orders_2(sK0) | ~spl4_3),
% 0.20/0.49    inference(avatar_component_clause,[],[f49])).
% 0.20/0.49  fof(f69,plain,(
% 0.20/0.49    ( ! [X0] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK3(sK0,X0),sK0,X0)) ) | (~spl4_2 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f63,f46])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    v3_orders_2(sK0) | ~spl4_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f44])).
% 0.20/0.49  fof(f63,plain,(
% 0.20/0.49    ( ! [X0] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X0,k1_orders_1(u1_struct_0(sK0))) | m2_orders_2(sK3(sK0,X0),sK0,X0)) ) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f61,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | m2_orders_2(sK3(X0,X1),X0,X1)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : (? [X2] : m2_orders_2(X2,X0,X1) | (~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0,X1] : ((m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ? [X2] : m2_orders_2(X2,X0,X1))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m2_orders_2)).
% 0.20/0.49  fof(f61,plain,(
% 0.20/0.49    l1_orders_2(sK0) | ~spl4_5),
% 0.20/0.49    inference(avatar_component_clause,[],[f59])).
% 0.20/0.49  fof(f106,plain,(
% 0.20/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(k1_funct_1(sK1,u1_struct_0(sK0)),X0)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.20/0.49    inference(resolution,[],[f92,f96])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ( ! [X10,X9] : (~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f91,f41])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    ( ! [X10,X9] : (v2_struct_0(sK0) | ~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10)) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f90,f56])).
% 0.20/0.49  fof(f90,plain,(
% 0.20/0.49    ( ! [X10,X9] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10)) ) | (~spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f89,f51])).
% 0.20/0.49  fof(f89,plain,(
% 0.20/0.49    ( ! [X10,X9] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10)) ) | (~spl4_2 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f68,f46])).
% 0.20/0.49  fof(f68,plain,(
% 0.20/0.49    ( ! [X10,X9] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X9,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X10,sK0,X9) | r2_hidden(k1_funct_1(X9,u1_struct_0(sK0)),X10)) ) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f61,f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X2,X0,X1) | r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2) | ~m2_orders_2(X2,X0,X1)) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (m2_orders_2(X2,X0,X1) => r2_hidden(k1_funct_1(X1,u1_struct_0(X0)),X2))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_orders_2)).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    spl4_8 | spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f108,f94,f59,f54,f49,f44,f39,f111])).
% 0.20/0.49  fof(f108,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK1),k4_orders_2(sK0,sK1)) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.20/0.49    inference(subsumption_resolution,[],[f107,f96])).
% 0.20/0.49  fof(f107,plain,(
% 0.20/0.49    r2_hidden(sK3(sK0,sK1),k4_orders_2(sK0,sK1)) | ~m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.20/0.49    inference(resolution,[],[f105,f72])).
% 0.20/0.49  fof(f105,plain,(
% 0.20/0.49    ( ! [X0] : (~m2_orders_2(X0,sK0,sK1) | r2_hidden(X0,k4_orders_2(sK0,sK1))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6)),
% 0.20/0.49    inference(resolution,[],[f76,f96])).
% 0.20/0.49  fof(f76,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f75,f41])).
% 0.20/0.49  fof(f75,plain,(
% 0.20/0.49    ( ! [X2,X1] : (v2_struct_0(sK0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f74,f56])).
% 0.20/0.49  fof(f74,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | (~spl4_2 | ~spl4_3 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f73,f51])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | (~spl4_2 | ~spl4_5)),
% 0.20/0.49    inference(subsumption_resolution,[],[f64,f46])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~v3_orders_2(sK0) | ~v4_orders_2(sK0) | ~v5_orders_2(sK0) | v2_struct_0(sK0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(sK0))) | ~m2_orders_2(X2,sK0,X1) | r2_hidden(X2,k4_orders_2(sK0,X1))) ) | ~spl4_5),
% 0.20/0.49    inference(resolution,[],[f61,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    ( ! [X0,X3,X1] : (~l1_orders_2(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | v2_struct_0(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,k4_orders_2(X0,X1))) )),
% 0.20/0.49    inference(equality_resolution,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v3_orders_2(X0) | ~v4_orders_2(X0) | ~v5_orders_2(X0) | ~l1_orders_2(X0) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) | ~m2_orders_2(X3,X0,X1) | r2_hidden(X3,X2) | k4_orders_2(X0,X1) != X2) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1))) | ~m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => ! [X2] : (k4_orders_2(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> m2_orders_2(X3,X0,X1)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d17_orders_2)).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    spl4_7),
% 0.20/0.49    inference(avatar_split_clause,[],[f21,f99])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    k1_xboole_0 = k3_tarski(k4_orders_2(sK0,sK1))),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : (k1_xboole_0 = k3_tarski(k4_orders_2(X0,X1)) & m1_orders_1(X1,k1_orders_1(u1_struct_0(X0)))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_orders_1(X1,k1_orders_1(u1_struct_0(X0))) => k1_xboole_0 != k3_tarski(k4_orders_2(X0,X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_orders_2)).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    spl4_6),
% 0.20/0.49    inference(avatar_split_clause,[],[f20,f94])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    m1_orders_1(sK1,k1_orders_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f62,plain,(
% 0.20/0.49    spl4_5),
% 0.20/0.49    inference(avatar_split_clause,[],[f26,f59])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    l1_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    spl4_4),
% 0.20/0.49    inference(avatar_split_clause,[],[f25,f54])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    v5_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    spl4_3),
% 0.20/0.49    inference(avatar_split_clause,[],[f24,f49])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    v4_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    spl4_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f23,f44])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    v3_orders_2(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f42,plain,(
% 0.20/0.49    ~spl4_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f22,f39])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (19855)------------------------------
% 0.20/0.49  % (19855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (19855)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (19855)Memory used [KB]: 10618
% 0.20/0.49  % (19855)Time elapsed: 0.064 s
% 0.20/0.49  % (19861)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.49  % (19855)------------------------------
% 0.20/0.49  % (19855)------------------------------
% 0.20/0.49  % (19850)Success in time 0.136 s
%------------------------------------------------------------------------------
