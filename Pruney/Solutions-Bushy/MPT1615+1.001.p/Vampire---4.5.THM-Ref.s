%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1615+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:10 EST 2020

% Result     : Theorem 0.17s
% Output     : Refutation 0.17s
% Verified   : 
% Statistics : Number of formulae       :   51 (  75 expanded)
%              Number of leaves         :   13 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :  148 ( 242 expanded)
%              Number of equality atoms :   23 (  43 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f68,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f26,f31,f36,f45,f49,f53,f58,f63,f67])).

fof(f67,plain,
    ( spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(avatar_contradiction_clause,[],[f66])).

fof(f66,plain,
    ( $false
    | spl1_1
    | ~ spl1_2
    | ~ spl1_3
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f65,f35])).

fof(f35,plain,
    ( v2_pre_topc(sK0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f33])).

fof(f33,plain,
    ( spl1_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f65,plain,
    ( ~ v2_pre_topc(sK0)
    | spl1_1
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(subsumption_resolution,[],[f64,f25])).

fof(f25,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f23])).

fof(f23,plain,
    ( spl1_1
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f64,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl1_2
    | ~ spl1_9 ),
    inference(resolution,[],[f62,f30])).

fof(f30,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f28])).

fof(f28,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f62,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ v2_pre_topc(X0) )
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f61])).

fof(f61,plain,
    ( spl1_9
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f63,plain,
    ( spl1_9
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(avatar_split_clause,[],[f59,f56,f47,f61])).

fof(f47,plain,
    ( spl1_6
  <=> ! [X0] :
        ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f56,plain,
    ( spl1_8
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f59,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_6
    | ~ spl1_8 ),
    inference(resolution,[],[f57,f48])).

fof(f48,plain,
    ( ! [X0] :
        ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f47])).

fof(f57,plain,
    ( ! [X0] :
        ( ~ r2_hidden(k1_xboole_0,X0)
        | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) )
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f56])).

fof(f58,plain,
    ( spl1_8
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(avatar_split_clause,[],[f54,f51,f43,f56])).

fof(f43,plain,
    ( spl1_5
  <=> ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0)
        | v1_xboole_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f51,plain,
    ( spl1_7
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f54,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0) )
    | ~ spl1_5
    | ~ spl1_7 ),
    inference(subsumption_resolution,[],[f44,f52])).

fof(f52,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl1_7 ),
    inference(avatar_component_clause,[],[f51])).

fof(f44,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
        | ~ r2_hidden(k1_xboole_0,X0)
        | v1_xboole_0(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f43])).

fof(f53,plain,(
    spl1_7 ),
    inference(avatar_split_clause,[],[f21,f51])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f49,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f20,f47])).

fof(f20,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f45,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f19,f43])).

fof(f19,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f36,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f16,f33])).

fof(f16,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f7,f13])).

fof(f13,plain,
    ( ? [X0] :
        ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f7,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f6])).

fof(f6,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f4])).

fof(f4,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

fof(f31,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f17,f28])).

fof(f17,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f26,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f18,f23])).

fof(f18,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f14])).

%------------------------------------------------------------------------------
