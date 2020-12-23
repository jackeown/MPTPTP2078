%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:09:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 146 expanded)
%              Number of leaves         :   22 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :  282 ( 636 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
% (30760)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
fof(f254,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f95,f101,f246,f250,f253])).

fof(f253,plain,
    ( spl2_1
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(avatar_contradiction_clause,[],[f251])).

fof(f251,plain,
    ( $false
    | spl2_1
    | ~ spl2_8
    | ~ spl2_9 ),
    inference(unit_resulting_resolution,[],[f64,f100,f194,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f194,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f192])).

fof(f192,plain,
    ( spl2_9
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f100,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_8
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f64,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f250,plain,
    ( spl2_9
    | ~ spl2_6
    | spl2_13 ),
    inference(avatar_split_clause,[],[f247,f243,f87,f192])).

fof(f87,plain,
    ( spl2_6
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f243,plain,
    ( spl2_13
  <=> r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f247,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | spl2_13 ),
    inference(resolution,[],[f245,f112])).

fof(f112,plain,(
    ! [X4,X3] :
      ( r2_hidden(X3,k6_domain_1(X4,X3))
      | ~ m1_subset_1(X3,X4)
      | v1_xboole_0(X4) ) ),
    inference(superposition,[],[f104,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(definition_unfolding,[],[f46,f54])).

% (30759)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f54,plain,(
    ! [X0] : k1_tarski(X0) = k1_enumset1(X0,X0,X0) ),
    inference(definition_unfolding,[],[f53,f52])).

fof(f52,plain,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

fof(f53,plain,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

fof(f46,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f104,plain,(
    ! [X0,X1] : r2_hidden(X0,k1_enumset1(X0,X0,X1)) ),
    inference(resolution,[],[f57,f59])).

fof(f59,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_enumset1(X0,X0,X1),X2)
      | r2_hidden(X0,X2) ) ),
    inference(definition_unfolding,[],[f40,f52])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,X2)
      | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(k2_tarski(X0,X1),X2)
        | ~ r2_hidden(X1,X2)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X2)
          & r2_hidden(X0,X2) )
        | ~ r1_tarski(k2_tarski(X0,X1),X2) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k2_tarski(X0,X1),X2)
    <=> ( r2_hidden(X1,X2)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

fof(f245,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | spl2_13 ),
    inference(avatar_component_clause,[],[f243])).

fof(f246,plain,
    ( spl2_9
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_13
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f241,f92,f243,f87,f82,f77,f72,f67,f62,f192])).

fof(f67,plain,
    ( spl2_2
  <=> v3_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f72,plain,
    ( spl2_3
  <=> v4_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f77,plain,
    ( spl2_4
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f82,plain,
    ( spl2_5
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f92,plain,
    ( spl2_7
  <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f241,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_7 ),
    inference(duplicate_literal_removal,[],[f232])).

fof(f232,plain,
    ( ~ r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ l1_orders_2(sK0)
    | ~ v5_orders_2(sK0)
    | ~ v4_orders_2(sK0)
    | ~ v3_orders_2(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_7 ),
    inference(resolution,[],[f120,f94])).

fof(f94,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2)))
      | ~ r2_hidden(X0,k6_domain_1(u1_struct_0(X1),X2))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ l1_orders_2(X1)
      | ~ v5_orders_2(X1)
      | ~ v4_orders_2(X1)
      | ~ v3_orders_2(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v1_xboole_0(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f44,f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,X2)
      | ~ r2_hidden(X1,k1_orders_2(X0,X2))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_orders_2(X0)
      | ~ v5_orders_2(X0)
      | ~ v4_orders_2(X0)
      | ~ v3_orders_2(X0)
      | v2_struct_0(X0) ) ),
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

fof(f101,plain,
    ( spl2_8
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f96,f82,f98])).

fof(f96,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f48,f84])).

fof(f84,plain,
    ( l1_orders_2(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_orders_2(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).

fof(f95,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f39,f92])).

fof(f39,plain,(
    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l1_orders_2(sK0)
    & v5_orders_2(sK0)
    & v4_orders_2(sK0)
    & v3_orders_2(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_orders_2(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l1_orders_2(sK0)
      & v5_orders_2(sK0)
      & v4_orders_2(sK0)
      & v3_orders_2(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1)))
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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

fof(f90,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f38,f87])).

fof(f38,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f37,f82])).

fof(f37,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f36,f77])).

fof(f36,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f35,f72])).

fof(f35,plain,(
    v4_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f70,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f67])).

fof(f34,plain,(
    v3_orders_2(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f65,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f33,f62])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 19:48:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.53  % (30776)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.54  % (30768)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.56  % (30776)Refutation found. Thanks to Tanya!
% 0.20/0.56  % SZS status Theorem for theBenchmark
% 0.20/0.56  % SZS output start Proof for theBenchmark
% 0.20/0.56  % (30760)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.56  fof(f254,plain,(
% 0.20/0.56    $false),
% 0.20/0.56    inference(avatar_sat_refutation,[],[f65,f70,f75,f80,f85,f90,f95,f101,f246,f250,f253])).
% 0.20/0.56  fof(f253,plain,(
% 0.20/0.56    spl2_1 | ~spl2_8 | ~spl2_9),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f251])).
% 0.20/0.56  fof(f251,plain,(
% 0.20/0.56    $false | (spl2_1 | ~spl2_8 | ~spl2_9)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f64,f100,f194,f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f23])).
% 0.20/0.56  fof(f23,plain,(
% 0.20/0.56    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f6])).
% 0.20/0.56  fof(f6,axiom,(
% 0.20/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.56  fof(f194,plain,(
% 0.20/0.56    v1_xboole_0(u1_struct_0(sK0)) | ~spl2_9),
% 0.20/0.56    inference(avatar_component_clause,[],[f192])).
% 0.20/0.56  fof(f192,plain,(
% 0.20/0.56    spl2_9 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.56  fof(f100,plain,(
% 0.20/0.56    l1_struct_0(sK0) | ~spl2_8),
% 0.20/0.56    inference(avatar_component_clause,[],[f98])).
% 0.20/0.56  fof(f98,plain,(
% 0.20/0.56    spl2_8 <=> l1_struct_0(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ~v2_struct_0(sK0) | spl2_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f62])).
% 0.20/0.56  fof(f62,plain,(
% 0.20/0.56    spl2_1 <=> v2_struct_0(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.56  fof(f250,plain,(
% 0.20/0.56    spl2_9 | ~spl2_6 | spl2_13),
% 0.20/0.56    inference(avatar_split_clause,[],[f247,f243,f87,f192])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    spl2_6 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.56  fof(f243,plain,(
% 0.20/0.56    spl2_13 <=> r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.20/0.56  fof(f247,plain,(
% 0.20/0.56    ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | spl2_13),
% 0.20/0.56    inference(resolution,[],[f245,f112])).
% 0.20/0.56  fof(f112,plain,(
% 0.20/0.56    ( ! [X4,X3] : (r2_hidden(X3,k6_domain_1(X4,X3)) | ~m1_subset_1(X3,X4) | v1_xboole_0(X4)) )),
% 0.20/0.56    inference(superposition,[],[f104,f58])).
% 0.20/0.56  fof(f58,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_enumset1(X1,X1,X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f46,f54])).
% 0.20/0.56  % (30759)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.56  fof(f54,plain,(
% 0.20/0.56    ( ! [X0] : (k1_tarski(X0) = k1_enumset1(X0,X0,X0)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f53,f52])).
% 0.20/0.56  fof(f52,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f3])).
% 0.20/0.56  fof(f3,axiom,(
% 0.20/0.56    ! [X0,X1] : k1_enumset1(X0,X0,X1) = k2_tarski(X0,X1)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).
% 0.20/0.56  fof(f53,plain,(
% 0.20/0.56    ( ! [X0] : (k2_tarski(X0,X0) = k1_tarski(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f2])).
% 0.20/0.56  fof(f2,axiom,(
% 0.20/0.56    ! [X0] : k2_tarski(X0,X0) = k1_tarski(X0)),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f22])).
% 0.20/0.56  fof(f22,plain,(
% 0.20/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(X0,k1_enumset1(X0,X0,X1))) )),
% 0.20/0.56    inference(resolution,[],[f57,f59])).
% 0.20/0.56  fof(f59,plain,(
% 0.20/0.56    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.56    inference(equality_resolution,[],[f50])).
% 0.20/0.56  fof(f50,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f32])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(flattening,[],[f31])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.20/0.56    inference(nnf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.56  fof(f57,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r1_tarski(k1_enumset1(X0,X0,X1),X2) | r2_hidden(X0,X2)) )),
% 0.20/0.56    inference(definition_unfolding,[],[f40,f52])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(X0,X2) | ~r1_tarski(k2_tarski(X0,X1),X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f30])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | ~r2_hidden(X1,X2) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.56    inference(flattening,[],[f29])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ! [X0,X1,X2] : ((r1_tarski(k2_tarski(X0,X1),X2) | (~r2_hidden(X1,X2) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X2) & r2_hidden(X0,X2)) | ~r1_tarski(k2_tarski(X0,X1),X2)))),
% 0.20/0.56    inference(nnf_transformation,[],[f4])).
% 0.20/0.56  fof(f4,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : (r1_tarski(k2_tarski(X0,X1),X2) <=> (r2_hidden(X1,X2) & r2_hidden(X0,X2)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).
% 0.20/0.56  fof(f245,plain,(
% 0.20/0.56    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | spl2_13),
% 0.20/0.56    inference(avatar_component_clause,[],[f243])).
% 0.20/0.56  fof(f246,plain,(
% 0.20/0.56    spl2_9 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_5 | ~spl2_6 | ~spl2_13 | ~spl2_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f241,f92,f243,f87,f82,f77,f72,f67,f62,f192])).
% 0.20/0.56  fof(f67,plain,(
% 0.20/0.56    spl2_2 <=> v3_orders_2(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.56  fof(f72,plain,(
% 0.20/0.56    spl2_3 <=> v4_orders_2(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.20/0.56  fof(f77,plain,(
% 0.20/0.56    spl2_4 <=> v5_orders_2(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    spl2_5 <=> l1_orders_2(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    spl2_7 <=> r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.20/0.56  fof(f241,plain,(
% 0.20/0.56    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | v1_xboole_0(u1_struct_0(sK0)) | ~spl2_7),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f232])).
% 0.20/0.56  fof(f232,plain,(
% 0.20/0.56    ~r2_hidden(sK1,k6_domain_1(u1_struct_0(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~l1_orders_2(sK0) | ~v5_orders_2(sK0) | ~v4_orders_2(sK0) | ~v3_orders_2(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | v1_xboole_0(u1_struct_0(sK0)) | ~spl2_7),
% 0.20/0.56    inference(resolution,[],[f120,f94])).
% 0.20/0.56  fof(f94,plain,(
% 0.20/0.56    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) | ~spl2_7),
% 0.20/0.56    inference(avatar_component_clause,[],[f92])).
% 0.20/0.56  fof(f120,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~r2_hidden(X0,k1_orders_2(X1,k6_domain_1(u1_struct_0(X1),X2))) | ~r2_hidden(X0,k6_domain_1(u1_struct_0(X1),X2)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~l1_orders_2(X1) | ~v5_orders_2(X1) | ~v4_orders_2(X1) | ~v3_orders_2(X1) | v2_struct_0(X1) | ~m1_subset_1(X2,u1_struct_0(X1)) | v1_xboole_0(u1_struct_0(X1))) )),
% 0.20/0.56    inference(resolution,[],[f44,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.20/0.56    inference(flattening,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0,X1] : (m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => m1_subset_1(k6_domain_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).
% 0.20/0.56  fof(f44,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,X2) | ~r2_hidden(X1,k1_orders_2(X0,X2)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((~r2_hidden(X1,k1_orders_2(X0,X2)) | ~r2_hidden(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v5_orders_2(X0) | ~v4_orders_2(X0) | ~v3_orders_2(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r2_hidden(X1,k1_orders_2(X0,X2)) & r2_hidden(X1,X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_orders_2)).
% 0.20/0.56  fof(f101,plain,(
% 0.20/0.56    spl2_8 | ~spl2_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f96,f82,f98])).
% 0.20/0.56  fof(f96,plain,(
% 0.20/0.56    l1_struct_0(sK0) | ~spl2_5),
% 0.20/0.56    inference(resolution,[],[f48,f84])).
% 0.20/0.56  fof(f84,plain,(
% 0.20/0.56    l1_orders_2(sK0) | ~spl2_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f82])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X0] : (~l1_orders_2(X0) | l1_struct_0(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0] : (l1_struct_0(X0) | ~l1_orders_2(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0] : (l1_orders_2(X0) => l1_struct_0(X0))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_orders_2)).
% 0.20/0.56  fof(f95,plain,(
% 0.20/0.56    spl2_7),
% 0.20/0.56    inference(avatar_split_clause,[],[f39,f92])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1)))),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    (r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => (? [X1] : (r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) & l1_orders_2(sK0) & v5_orders_2(sK0) & v4_orders_2(sK0) & v3_orders_2(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ? [X1] : (r2_hidden(X1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),X1))) & m1_subset_1(X1,u1_struct_0(sK0))) => (r2_hidden(sK1,k1_orders_2(sK0,k6_domain_1(u1_struct_0(sK0),sK1))) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.56    introduced(choice_axiom,[])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : (r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,negated_conjecture,(
% 0.20/0.56    ~! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.56    inference(negated_conjecture,[],[f11])).
% 0.20/0.56  fof(f11,conjecture,(
% 0.20/0.56    ! [X0] : ((l1_orders_2(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ~r2_hidden(X1,k1_orders_2(X0,k6_domain_1(u1_struct_0(X0),X1)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_orders_2)).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    spl2_6),
% 0.20/0.56    inference(avatar_split_clause,[],[f38,f87])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    spl2_5),
% 0.20/0.56    inference(avatar_split_clause,[],[f37,f82])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    l1_orders_2(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f80,plain,(
% 0.20/0.56    spl2_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f36,f77])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    v5_orders_2(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f75,plain,(
% 0.20/0.56    spl2_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f35,f72])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    v4_orders_2(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f70,plain,(
% 0.20/0.56    spl2_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f34,f67])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    v3_orders_2(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  fof(f65,plain,(
% 0.20/0.56    ~spl2_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f33,f62])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    ~v2_struct_0(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f28])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (30776)------------------------------
% 0.20/0.56  % (30776)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (30776)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (30776)Memory used [KB]: 10874
% 0.20/0.56  % (30776)Time elapsed: 0.101 s
% 0.20/0.56  % (30776)------------------------------
% 0.20/0.56  % (30776)------------------------------
% 0.20/0.56  % (30782)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.57  % (30752)Success in time 0.213 s
%------------------------------------------------------------------------------
