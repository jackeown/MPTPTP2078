%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1615+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:26 EST 2020

% Result     : Theorem 1.73s
% Output     : Refutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of leaves         :    8 (  15 expanded)
%              Depth                    :   10
%              Number of atoms          :  103 ( 165 expanded)
%              Number of equality atoms :   18 (  33 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3381,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3340,f3344,f3348,f3380])).

fof(f3380,plain,
    ( spl17_1
    | ~ spl17_2
    | ~ spl17_3 ),
    inference(avatar_contradiction_clause,[],[f3379])).

fof(f3379,plain,
    ( $false
    | spl17_1
    | ~ spl17_2
    | ~ spl17_3 ),
    inference(subsumption_resolution,[],[f3378,f3339])).

fof(f3339,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | spl17_1 ),
    inference(avatar_component_clause,[],[f3338])).

fof(f3338,plain,
    ( spl17_1
  <=> k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_1])])).

fof(f3378,plain,
    ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ spl17_2
    | ~ spl17_3 ),
    inference(subsumption_resolution,[],[f3376,f3343])).

fof(f3343,plain,
    ( l1_pre_topc(sK0)
    | ~ spl17_2 ),
    inference(avatar_component_clause,[],[f3342])).

fof(f3342,plain,
    ( spl17_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_2])])).

fof(f3376,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    | ~ spl17_3 ),
    inference(resolution,[],[f3372,f3347])).

fof(f3347,plain,
    ( v2_pre_topc(sK0)
    | ~ spl17_3 ),
    inference(avatar_component_clause,[],[f3346])).

fof(f3346,plain,
    ( spl17_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl17_3])])).

fof(f3372,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(subsumption_resolution,[],[f3371,f3252])).

fof(f3252,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3147])).

fof(f3147,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3146])).

fof(f3146,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1792])).

fof(f1792,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ~ v1_xboole_0(u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_pre_topc)).

fof(f3371,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      | v1_xboole_0(u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f3202,f3251])).

fof(f3251,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f3145])).

fof(f3145,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f3144])).

fof(f3144,plain,(
    ! [X0] :
      ( r2_hidden(k1_xboole_0,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1851])).

fof(f1851,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => r2_hidden(k1_xboole_0,u1_pre_topc(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_pre_topc)).

fof(f3202,plain,(
    ! [X0] :
      ( ~ r2_hidden(k1_xboole_0,X0)
      | k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f3136])).

fof(f3136,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f3135])).

fof(f3135,plain,(
    ! [X0] :
      ( k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0))
      | ~ r2_hidden(k1_xboole_0,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3095])).

fof(f3095,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( r2_hidden(k1_xboole_0,X0)
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_yellow_1)).

fof(f3348,plain,(
    spl17_3 ),
    inference(avatar_split_clause,[],[f3197,f3346])).

fof(f3197,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3167])).

fof(f3167,plain,
    ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f3132,f3166])).

fof(f3166,plain,
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

fof(f3132,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f3131])).

fof(f3131,plain,(
    ? [X0] :
      ( k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(X0)))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3107])).

fof(f3107,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    inference(negated_conjecture,[],[f3106])).

fof(f3106,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_xboole_0 = k3_yellow_0(k2_yellow_1(u1_pre_topc(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_yellow_1)).

fof(f3344,plain,(
    spl17_2 ),
    inference(avatar_split_clause,[],[f3198,f3342])).

fof(f3198,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f3167])).

fof(f3340,plain,(
    ~ spl17_1 ),
    inference(avatar_split_clause,[],[f3199,f3338])).

fof(f3199,plain,(
    k1_xboole_0 != k3_yellow_0(k2_yellow_1(u1_pre_topc(sK0))) ),
    inference(cnf_transformation,[],[f3167])).
%------------------------------------------------------------------------------
