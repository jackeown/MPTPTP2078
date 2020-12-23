%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1888+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:52 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  123 ( 229 expanded)
%              Number of leaves         :   31 (  96 expanded)
%              Depth                    :   12
%              Number of atoms          :  478 (1168 expanded)
%              Number of equality atoms :   58 ( 157 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f980,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f71,f75,f79,f83,f87,f91,f95,f99,f103,f296,f303,f315,f331,f338,f958,f978])).

fof(f978,plain,
    ( spl5_2
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f972,f956,f73])).

fof(f73,plain,
    ( spl5_2
  <=> r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f956,plain,
    ( spl5_60
  <=> k1_xboole_0 = k3_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f972,plain,
    ( r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl5_60 ),
    inference(trivial_inequality_removal,[],[f961])).

% (26272)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
fof(f961,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl5_60 ),
    inference(superposition,[],[f57,f957])).

fof(f957,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f956])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
     => r1_xboole_0(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f958,plain,
    ( spl5_60
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f954,f313,f101,f81,f77,f69,f956])).

fof(f69,plain,
    ( spl5_1
  <=> k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f77,plain,
    ( spl5_3
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f81,plain,
    ( spl5_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f101,plain,
    ( spl5_9
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f313,plain,
    ( spl5_15
  <=> ! [X1,X0,X2] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f954,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(duplicate_literal_removal,[],[f950])).

fof(f950,plain,
    ( k1_xboole_0 = k3_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | k1_xboole_0 = k3_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(resolution,[],[f516,f264])).

fof(f264,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,k1_xboole_0),X1)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl5_9 ),
    inference(resolution,[],[f147,f102])).

fof(f102,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f147,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_xboole_0(X10)
      | k3_xboole_0(X8,X9) = X10
      | r2_hidden(sK4(X8,X9,X10),X9) ) ),
    inference(resolution,[],[f63,f53])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK3(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f33,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK3(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X1)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
            | ~ r2_hidden(sK4(X0,X1,X2),X0)
            | ~ r2_hidden(sK4(X0,X1,X2),X2) )
          & ( ( r2_hidden(sK4(X0,X1,X2),X1)
              & r2_hidden(sK4(X0,X1,X2),X0) )
            | r2_hidden(sK4(X0,X1,X2),X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f38,f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ~ r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X3,X2) )
          & ( ( r2_hidden(X3,X1)
              & r2_hidden(X3,X0) )
            | r2_hidden(X3,X2) ) )
     => ( ( ~ r2_hidden(sK4(X0,X1,X2),X1)
          | ~ r2_hidden(sK4(X0,X1,X2),X0)
          | ~ r2_hidden(sK4(X0,X1,X2),X2) )
        & ( ( r2_hidden(sK4(X0,X1,X2),X1)
            & r2_hidden(sK4(X0,X1,X2),X0) )
          | r2_hidden(sK4(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,X0) )
            & ( ( r2_hidden(X4,X1)
                & r2_hidden(X4,X0) )
              | ~ r2_hidden(X4,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(rectify,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k3_xboole_0(X0,X1) = X2
        | ? [X3] :
            ( ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X3,X2) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | r2_hidden(X3,X2) ) ) )
      & ( ! [X3] :
            ( ( r2_hidden(X3,X2)
              | ~ r2_hidden(X3,X1)
              | ~ r2_hidden(X3,X0) )
            & ( ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
              | ~ r2_hidden(X3,X2) ) )
        | k3_xboole_0(X0,X1) != X2 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f516,plain,
    ( ! [X9] :
        ( ~ r2_hidden(sK4(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),X9,k1_xboole_0),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | k1_xboole_0 = k3_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),X9) )
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_15 ),
    inference(resolution,[],[f388,f129])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK4(X0,X1,k1_xboole_0),X0)
        | k3_xboole_0(X0,X1) = k1_xboole_0 )
    | ~ spl5_9 ),
    inference(resolution,[],[f110,f102])).

fof(f110,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_xboole_0(X6)
      | k3_xboole_0(X4,X5) = X6
      | r2_hidden(sK4(X4,X5,X6),X4) ) ),
    inference(resolution,[],[f62,f53])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X2),X2)
      | r2_hidden(sK4(X0,X1,X2),X0)
      | k3_xboole_0(X0,X1) = X2 ) ),
    inference(cnf_transformation,[],[f40])).

fof(f388,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) )
    | spl5_1
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f356,f381])).

fof(f381,plain,
    ( ! [X1] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) )
    | spl5_1
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(superposition,[],[f70,f358])).

fof(f358,plain,
    ( ! [X0] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) )
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(duplicate_literal_removal,[],[f355])).

fof(f355,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(resolution,[],[f348,f78])).

fof(f78,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f348,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl5_3
    | ~ spl5_15 ),
    inference(resolution,[],[f314,f78])).

fof(f314,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0)) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f313])).

fof(f70,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f356,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) )
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_15 ),
    inference(resolution,[],[f348,f82])).

fof(f82,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f338,plain,
    ( ~ spl5_5
    | spl5_17 ),
    inference(avatar_split_clause,[],[f337,f329,f85])).

fof(f85,plain,
    ( spl5_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f329,plain,
    ( spl5_17
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f337,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_17 ),
    inference(resolution,[],[f330,f50])).

fof(f50,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f330,plain,
    ( ~ l1_struct_0(sK0)
    | spl5_17 ),
    inference(avatar_component_clause,[],[f329])).

fof(f331,plain,
    ( spl5_8
    | ~ spl5_17
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f320,f310,f329,f97])).

fof(f97,plain,
    ( spl5_8
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f310,plain,
    ( spl5_14
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f320,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f311,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f311,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f310])).

fof(f315,plain,
    ( spl5_14
    | spl5_15
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f307,f301,f313,f310])).

fof(f301,plain,
    ( spl5_13
  <=> ! [X3,X2,X4] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X3))
        | ~ r2_hidden(X3,k2_pre_topc(sK0,X4))
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

% (26267)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f307,plain,
    ( ! [X2,X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl5_13 ),
    inference(resolution,[],[f302,f55])).

% (26266)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f302,plain,
    ( ! [X4,X2,X3] :
        ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k2_pre_topc(sK0,X4))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X3))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X3,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2))) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f301])).

fof(f303,plain,
    ( ~ spl5_5
    | spl5_13
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f299,f294,f301,f85])).

fof(f294,plain,
    ( spl5_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f299,plain,
    ( ! [X4,X2,X3] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X3))
        | ~ r2_hidden(X3,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X3,k2_pre_topc(sK0,X4)) )
    | ~ spl5_12 ),
    inference(resolution,[],[f295,f108])).

fof(f108,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ r2_hidden(X2,k2_pre_topc(X1,X0)) ) ),
    inference(resolution,[],[f56,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f295,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( spl5_8
    | ~ spl5_7
    | ~ spl5_5
    | spl5_12
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f289,f89,f294,f85,f93,f97])).

fof(f93,plain,
    ( spl5_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f89,plain,
    ( spl5_6
  <=> v3_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f289,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X0,k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0)
        | k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)) = k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X0))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_6 ),
    inference(resolution,[],[f51,f90])).

fof(f90,plain,
    ( v3_tdlat_3(sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_tdlat_3(X0)
      | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

% (26271)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (26277)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              | ~ r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v3_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X1,k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
               => k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tex_2)).

fof(f103,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f99,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f41,f97])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
    & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
    & m1_subset_1(sK2,u1_struct_0(sK0))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v3_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f30,f29,f28])).

fof(f28,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
                & m1_subset_1(X2,u1_struct_0(X0)) )
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
              & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
              & m1_subset_1(X2,u1_struct_0(sK0)) )
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_pre_topc(sK0)
      & v3_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1))
            & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
            & m1_subset_1(X2,u1_struct_0(sK0)) )
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ? [X2] :
          ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
          & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
          & m1_subset_1(X2,u1_struct_0(sK0)) )
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X2] :
        ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1))
        & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),X2)))
        & m1_subset_1(X2,u1_struct_0(sK0)) )
   => ( k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))
      & ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)))
      & m1_subset_1(sK2,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) != k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
              & ~ r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)))
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                  | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2)) = k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1))
                | r1_xboole_0(k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X1)),k2_pre_topc(X0,k6_domain_1(u1_struct_0(X0),X2))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tex_2)).

fof(f95,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f42,f93])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f91,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f44,f85])).

fof(f44,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f83,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f45,f81])).

fof(f45,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f79,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f46,f77])).

fof(f46,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f75,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f47,f73])).

fof(f47,plain,(
    ~ r1_xboole_0(k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2))) ),
    inference(cnf_transformation,[],[f31])).

fof(f71,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f48,f69])).

fof(f48,plain,(
    k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK1)) != k2_pre_topc(sK0,k6_domain_1(u1_struct_0(sK0),sK2)) ),
    inference(cnf_transformation,[],[f31])).

%------------------------------------------------------------------------------
