%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 299 expanded)
%              Number of leaves         :   19 (  96 expanded)
%              Depth                    :   16
%              Number of atoms          :  548 (1543 expanded)
%              Number of equality atoms :   51 ( 216 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f274,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f120,f175,f185,f193,f233,f241,f249,f273])).

fof(f273,plain,
    ( ~ spl4_1
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f272])).

fof(f272,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f271,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v13_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v13_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

% (10088)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (10106)Refutation not found, incomplete strategy% (10106)------------------------------
% (10106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (10106)Termination reason: Refutation not found, incomplete strategy

% (10106)Memory used [KB]: 10618
% (10106)Time elapsed: 0.060 s
% (10106)------------------------------
% (10106)------------------------------
% (10094)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).

fof(f271,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_1
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f270,f109])).

fof(f109,plain,
    ( l1_lattices(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl4_1
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f270,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f269,f39])).

fof(f39,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f269,plain,
    ( ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_4
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f265,f156])).

fof(f156,plain,
    ( m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f155])).

fof(f155,plain,
    ( spl4_4
  <=> m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f265,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0))
    | ~ v13_lattices(sK0)
    | ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_9 ),
    inference(resolution,[],[f250,f91])).

fof(f91,plain,(
    ! [X0,X3] :
      ( sQ3_eqProxy(k5_lattices(X0),k2_lattices(X0,X3,k5_lattices(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f65,plain,(
    ! [X0,X3] :
      ( sQ3_eqProxy(k5_lattices(X0),k2_lattices(X0,X3,k5_lattices(X0)))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f57,f59])).

fof(f59,plain,(
    ! [X1,X0] :
      ( sQ3_eqProxy(X0,X1)
    <=> X0 = X1 ) ),
    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).

fof(f57,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X3,X1) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
                  | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
                & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X3] :
                  ( ( k2_lattices(X0,X3,X1) = X1
                    & k2_lattices(X0,X1,X3) = X1 )
                  | ~ m1_subset_1(X3,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k5_lattices(X0) = X1
              | ? [X2] :
                  ( ( k2_lattices(X0,X2,X1) != X1
                    | k2_lattices(X0,X1,X2) != X1 )
                  & m1_subset_1(X2,u1_struct_0(X0)) ) )
            & ( ! [X2] :
                  ( ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 )
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | k5_lattices(X0) != X1 ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_lattices(X0) = X1
          <=> ! [X2] :
                ( ( k2_lattices(X0,X2,X1) = X1
                  & k2_lattices(X0,X1,X2) = X1 )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_lattices(X0)
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ( k5_lattices(X0) = X1
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ( k2_lattices(X0,X2,X1) = X1
                    & k2_lattices(X0,X1,X2) = X1 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).

fof(f250,plain,
    ( ~ sQ3_eqProxy(k5_lattices(sK0),k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)))
    | ~ spl4_9 ),
    inference(resolution,[],[f228,f93])).

fof(f93,plain,(
    ! [X0] :
      ( ~ sQ3_eqProxy(X0,k4_lattices(sK0,k5_lattices(sK0),sK1))
      | ~ sQ3_eqProxy(k5_lattices(sK0),X0) ) ),
    inference(resolution,[],[f88,f60])).

fof(f60,plain,(
    ~ sQ3_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1)) ),
    inference(equality_proxy_replacement,[],[f42,f59])).

fof(f42,plain,(
    k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( sQ3_eqProxy(X0,X2)
      | ~ sQ3_eqProxy(X1,X2)
      | ~ sQ3_eqProxy(X0,X1) ) ),
    inference(equality_proxy_axiom,[],[f59])).

fof(f228,plain,
    ( sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f226])).

fof(f226,plain,
    ( spl4_9
  <=> sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f249,plain,(
    spl4_10 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl4_10 ),
    inference(subsumption_resolution,[],[f247,f40])).

fof(f40,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f247,plain,
    ( ~ l3_lattices(sK0)
    | spl4_10 ),
    inference(subsumption_resolution,[],[f246,f37])).

fof(f246,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_10 ),
    inference(subsumption_resolution,[],[f243,f38])).

fof(f38,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f243,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_10 ),
    inference(resolution,[],[f232,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
          & v8_lattices(X0)
          & v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).

fof(f232,plain,
    ( ~ v8_lattices(sK0)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl4_10
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f241,plain,(
    spl4_8 ),
    inference(avatar_contradiction_clause,[],[f240])).

fof(f240,plain,
    ( $false
    | spl4_8 ),
    inference(subsumption_resolution,[],[f239,f40])).

fof(f239,plain,
    ( ~ l3_lattices(sK0)
    | spl4_8 ),
    inference(subsumption_resolution,[],[f238,f37])).

fof(f238,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_8 ),
    inference(subsumption_resolution,[],[f235,f38])).

fof(f235,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_8 ),
    inference(resolution,[],[f224,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f224,plain,
    ( ~ v9_lattices(sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f222])).

fof(f222,plain,
    ( spl4_8
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f233,plain,
    ( ~ spl4_8
    | spl4_9
    | ~ spl4_10
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f216,f172,f168,f155,f230,f226,f222])).

% (10095)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
fof(f168,plain,
    ( spl4_6
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f172,plain,
    ( spl4_7
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f216,plain,
    ( ~ v8_lattices(sK0)
    | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ v9_lattices(sK0)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f215,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f215,plain,
    ( ~ v8_lattices(sK0)
    | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f214,f37])).

fof(f214,plain,
    ( ~ v8_lattices(sK0)
    | v2_struct_0(sK0)
    | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f213,f169])).

fof(f169,plain,
    ( v6_lattices(sK0)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f168])).

fof(f213,plain,
    ( ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f212,f40])).

fof(f212,plain,
    ( ~ l3_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ spl4_4
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f209,f173])).

fof(f173,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f209,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | ~ v8_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v9_lattices(sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f204,f156])).

fof(f204,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | sQ3_eqProxy(k2_lattices(X1,k4_lattices(X1,X2,X0),X2),k4_lattices(X1,X2,X0))
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ v9_lattices(X1) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v8_lattices(X1)
      | ~ v6_lattices(X1)
      | v2_struct_0(X1)
      | sQ3_eqProxy(k2_lattices(X1,k4_lattices(X1,X2,X0),X2),k4_lattices(X1,X2,X0))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1))
      | ~ l3_lattices(X1)
      | ~ v9_lattices(X1)
      | ~ v8_lattices(X1)
      | v2_struct_0(X1) ) ),
    inference(resolution,[],[f50,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_lattices(X0,X1,X2)
      | sQ3_eqProxy(k2_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_proxy_replacement,[],[f48,f59])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_lattices(X0,X1,X2) = X1
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_lattices(X0,X1,X2)
                  | k2_lattices(X0,X1,X2) != X1 )
                & ( k2_lattices(X0,X1,X2) = X1
                  | ~ r1_lattices(X0,X1,X2) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r1_lattices(X0,X1,X2)
              <=> k2_lattices(X0,X1,X2) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,k4_lattices(X0,X1,X2),X1)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,k4_lattices(X0,X1,X2),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).

fof(f193,plain,
    ( ~ spl4_1
    | spl4_7 ),
    inference(avatar_contradiction_clause,[],[f192])).

fof(f192,plain,
    ( $false
    | ~ spl4_1
    | spl4_7 ),
    inference(subsumption_resolution,[],[f191,f37])).

fof(f191,plain,
    ( v2_struct_0(sK0)
    | ~ spl4_1
    | spl4_7 ),
    inference(subsumption_resolution,[],[f189,f109])).

fof(f189,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_7 ),
    inference(resolution,[],[f174,f51])).

fof(f174,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f172])).

fof(f185,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl4_6 ),
    inference(subsumption_resolution,[],[f183,f40])).

fof(f183,plain,
    ( ~ l3_lattices(sK0)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f182,f37])).

fof(f182,plain,
    ( v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_6 ),
    inference(subsumption_resolution,[],[f179,f38])).

fof(f179,plain,
    ( ~ v10_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ l3_lattices(sK0)
    | spl4_6 ),
    inference(resolution,[],[f170,f45])).

fof(f45,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f170,plain,
    ( ~ v6_lattices(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f168])).

fof(f175,plain,
    ( ~ spl4_6
    | ~ spl4_7
    | ~ spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f166,f155,f108,f172,f168])).

fof(f166,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f165,f37])).

fof(f165,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_1
    | spl4_4 ),
    inference(subsumption_resolution,[],[f164,f109])).

fof(f164,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_4 ),
    inference(subsumption_resolution,[],[f163,f41])).

fof(f163,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ l1_lattices(sK0)
    | ~ v6_lattices(sK0)
    | v2_struct_0(sK0)
    | spl4_4 ),
    inference(resolution,[],[f157,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).

fof(f157,plain,
    ( ~ m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0))
    | spl4_4 ),
    inference(avatar_component_clause,[],[f155])).

fof(f120,plain,(
    spl4_1 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl4_1 ),
    inference(subsumption_resolution,[],[f117,f40])).

fof(f117,plain,
    ( ~ l3_lattices(sK0)
    | spl4_1 ),
    inference(resolution,[],[f110,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => l1_lattices(X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f110,plain,
    ( ~ l1_lattices(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n009.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:10:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.48  % (10091)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (10091)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.49  % (10106)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (10100)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f274,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(avatar_sat_refutation,[],[f120,f175,f185,f193,f233,f241,f249,f273])).
% 0.21/0.49  fof(f273,plain,(
% 0.21/0.49    ~spl4_1 | ~spl4_4 | ~spl4_9),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f272])).
% 0.21/0.49  fof(f272,plain,(
% 0.21/0.49    $false | (~spl4_1 | ~spl4_4 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f271,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v13_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f15,f30,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v13_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ? [X1] : (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) => (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  % (10088)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (10106)Refutation not found, incomplete strategy% (10106)------------------------------
% 0.21/0.49  % (10106)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10106)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (10106)Memory used [KB]: 10618
% 0.21/0.49  % (10106)Time elapsed: 0.060 s
% 0.21/0.49  % (10106)------------------------------
% 0.21/0.49  % (10106)------------------------------
% 0.21/0.49  % (10094)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 0.21/0.49    inference(negated_conjecture,[],[f8])).
% 0.21/0.49  fof(f8,conjecture,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattices)).
% 0.21/0.49  fof(f271,plain,(
% 0.21/0.49    v2_struct_0(sK0) | (~spl4_1 | ~spl4_4 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f270,f109])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    l1_lattices(sK0) | ~spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  fof(f108,plain,(
% 0.21/0.49    spl4_1 <=> l1_lattices(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.49  fof(f270,plain,(
% 0.21/0.49    ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f269,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    v13_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f269,plain,(
% 0.21/0.49    ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | (~spl4_4 | ~spl4_9)),
% 0.21/0.49    inference(subsumption_resolution,[],[f265,f156])).
% 0.21/0.49  fof(f156,plain,(
% 0.21/0.49    m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0)) | ~spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f155])).
% 0.21/0.49  fof(f155,plain,(
% 0.21/0.49    spl4_4 <=> m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.49  fof(f265,plain,(
% 0.21/0.49    ~m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0)) | ~v13_lattices(sK0) | ~l1_lattices(sK0) | v2_struct_0(sK0) | ~spl4_9),
% 0.21/0.49    inference(resolution,[],[f250,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    ( ! [X0,X3] : (sQ3_eqProxy(k5_lattices(X0),k2_lattices(X0,X3,k5_lattices(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f65,f51])).
% 0.21/0.49  fof(f51,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f24])).
% 0.21/0.49  fof(f24,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0,X3] : (sQ3_eqProxy(k5_lattices(X0),k2_lattices(X0,X3,k5_lattices(X0))) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f57,f59])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ! [X1,X0] : (sQ3_eqProxy(X0,X1) <=> X0 = X1)),
% 0.21/0.49    introduced(equality_proxy_definition,[new_symbols(naming,[sQ3_eqProxy])])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X3] : (k5_lattices(X0) = k2_lattices(X0,X3,k5_lattices(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_resolution,[],[f53])).
% 0.21/0.49  fof(f53,plain,(
% 0.21/0.49    ( ! [X0,X3,X1] : (k2_lattices(X0,X3,X1) = X1 | ~m1_subset_1(X3,u1_struct_0(X0)) | k5_lattices(X0) != X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ! [X1,X0] : (? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0))) => ((k2_lattices(X0,sK2(X0,X1),X1) != X1 | k2_lattices(X0,X1,sK2(X0,X1)) != X1) & m1_subset_1(sK2(X0,X1),u1_struct_0(X0))))),
% 0.21/0.49    introduced(choice_axiom,[])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X3] : ((k2_lattices(X0,X3,X1) = X1 & k2_lattices(X0,X1,X3) = X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(rectify,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((k5_lattices(X0) = X1 | ? [X2] : ((k2_lattices(X0,X2,X1) != X1 | k2_lattices(X0,X1,X2) != X1) & m1_subset_1(X2,u1_struct_0(X0)))) & (! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | k5_lattices(X0) != X1)) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f25])).
% 0.21/0.49  fof(f25,plain,(
% 0.21/0.49    ! [X0] : ((! [X1] : ((k5_lattices(X0) = X1 <=> ! [X2] : ((k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v13_lattices(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => (v13_lattices(X0) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => (k5_lattices(X0) = X1 <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (k2_lattices(X0,X2,X1) = X1 & k2_lattices(X0,X1,X2) = X1))))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d16_lattices)).
% 0.21/0.49  fof(f250,plain,(
% 0.21/0.49    ~sQ3_eqProxy(k5_lattices(sK0),k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0))) | ~spl4_9),
% 0.21/0.49    inference(resolution,[],[f228,f93])).
% 0.21/0.49  fof(f93,plain,(
% 0.21/0.49    ( ! [X0] : (~sQ3_eqProxy(X0,k4_lattices(sK0,k5_lattices(sK0),sK1)) | ~sQ3_eqProxy(k5_lattices(sK0),X0)) )),
% 0.21/0.49    inference(resolution,[],[f88,f60])).
% 0.21/0.49  fof(f60,plain,(
% 0.21/0.49    ~sQ3_eqProxy(k5_lattices(sK0),k4_lattices(sK0,k5_lattices(sK0),sK1))),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f42,f59])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (sQ3_eqProxy(X0,X2) | ~sQ3_eqProxy(X1,X2) | ~sQ3_eqProxy(X0,X1)) )),
% 0.21/0.49    inference(equality_proxy_axiom,[],[f59])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1)) | ~spl4_9),
% 0.21/0.49    inference(avatar_component_clause,[],[f226])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    spl4_9 <=> sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.49  fof(f249,plain,(
% 0.21/0.49    spl4_10),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f248])).
% 0.21/0.49  fof(f248,plain,(
% 0.21/0.49    $false | spl4_10),
% 0.21/0.49    inference(subsumption_resolution,[],[f247,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    l3_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f247,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | spl4_10),
% 0.21/0.49    inference(subsumption_resolution,[],[f246,f37])).
% 0.21/0.49  fof(f246,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl4_10),
% 0.21/0.49    inference(subsumption_resolution,[],[f243,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    v10_lattices(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f243,plain,(
% 0.21/0.49    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl4_10),
% 0.21/0.49    inference(resolution,[],[f232,f46])).
% 0.21/0.49  fof(f46,plain,(
% 0.21/0.49    ( ! [X0] : (v8_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : ((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.21/0.49    inference(flattening,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (((v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.49  fof(f11,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_lattices)).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | spl4_10),
% 0.21/0.49    inference(avatar_component_clause,[],[f230])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    spl4_10 <=> v8_lattices(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.49  fof(f241,plain,(
% 0.21/0.49    spl4_8),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f240])).
% 0.21/0.49  fof(f240,plain,(
% 0.21/0.49    $false | spl4_8),
% 0.21/0.49    inference(subsumption_resolution,[],[f239,f40])).
% 0.21/0.49  fof(f239,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | spl4_8),
% 0.21/0.49    inference(subsumption_resolution,[],[f238,f37])).
% 0.21/0.49  fof(f238,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl4_8),
% 0.21/0.49    inference(subsumption_resolution,[],[f235,f38])).
% 0.21/0.49  fof(f235,plain,(
% 0.21/0.49    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl4_8),
% 0.21/0.49    inference(resolution,[],[f224,f47])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f224,plain,(
% 0.21/0.49    ~v9_lattices(sK0) | spl4_8),
% 0.21/0.49    inference(avatar_component_clause,[],[f222])).
% 0.21/0.49  fof(f222,plain,(
% 0.21/0.49    spl4_8 <=> v9_lattices(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    ~spl4_8 | spl4_9 | ~spl4_10 | ~spl4_4 | ~spl4_6 | ~spl4_7),
% 0.21/0.49    inference(avatar_split_clause,[],[f216,f172,f168,f155,f230,f226,f222])).
% 0.21/0.49  % (10095)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    spl4_6 <=> v6_lattices(sK0)),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.49  fof(f172,plain,(
% 0.21/0.49    spl4_7 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.21/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.49  fof(f216,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1)) | ~v9_lattices(sK0) | (~spl4_4 | ~spl4_6 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f215,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f215,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v9_lattices(sK0) | (~spl4_4 | ~spl4_6 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f214,f37])).
% 0.21/0.49  fof(f214,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | v2_struct_0(sK0) | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v9_lattices(sK0) | (~spl4_4 | ~spl4_6 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f213,f169])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    v6_lattices(sK0) | ~spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f168])).
% 0.21/0.49  fof(f213,plain,(
% 0.21/0.49    ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v9_lattices(sK0) | (~spl4_4 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f212,f40])).
% 0.21/0.49  fof(f212,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v9_lattices(sK0) | (~spl4_4 | ~spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f209,f173])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f172])).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l3_lattices(sK0) | ~v8_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | sQ3_eqProxy(k2_lattices(sK0,k4_lattices(sK0,k5_lattices(sK0),sK1),k5_lattices(sK0)),k4_lattices(sK0,k5_lattices(sK0),sK1)) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~v9_lattices(sK0) | ~spl4_4),
% 0.21/0.49    inference(resolution,[],[f204,f156])).
% 0.21/0.49  fof(f204,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1) | sQ3_eqProxy(k2_lattices(X1,k4_lattices(X1,X2,X0),X2),k4_lattices(X1,X2,X0)) | ~m1_subset_1(X0,u1_struct_0(X1)) | ~v9_lattices(X1)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f203])).
% 0.21/0.49  fof(f203,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X0,u1_struct_0(X1)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~l3_lattices(X1) | ~v8_lattices(X1) | ~v6_lattices(X1) | v2_struct_0(X1) | sQ3_eqProxy(k2_lattices(X1,k4_lattices(X1,X2,X0),X2),k4_lattices(X1,X2,X0)) | ~m1_subset_1(X2,u1_struct_0(X1)) | ~m1_subset_1(k4_lattices(X1,X2,X0),u1_struct_0(X1)) | ~l3_lattices(X1) | ~v9_lattices(X1) | ~v8_lattices(X1) | v2_struct_0(X1)) )),
% 0.21/0.49    inference(resolution,[],[f50,f62])).
% 0.21/0.49  fof(f62,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~r1_lattices(X0,X1,X2) | sQ3_eqProxy(k2_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(equality_proxy_replacement,[],[f48,f59])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (((r1_lattices(X0,X1,X2) | k2_lattices(X0,X1,X2) != X1) & (k2_lattices(X0,X1,X2) = X1 | ~r1_lattices(X0,X1,X2))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(nnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : ((r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v9_lattices(X0) | ~v8_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v9_lattices(X0) & v8_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r1_lattices(X0,X1,X2) <=> k2_lattices(X0,X1,X2) = X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_lattices)).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (! [X2] : (r1_lattices(X0,k4_lattices(X0,X1,X2),X1) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v8_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : ((l3_lattices(X0) & v8_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => r1_lattices(X0,k4_lattices(X0,X1,X2),X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_lattices)).
% 0.21/0.49  fof(f193,plain,(
% 0.21/0.49    ~spl4_1 | spl4_7),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    $false | (~spl4_1 | spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f191,f37])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    v2_struct_0(sK0) | (~spl4_1 | spl4_7)),
% 0.21/0.49    inference(subsumption_resolution,[],[f189,f109])).
% 0.21/0.49  fof(f189,plain,(
% 0.21/0.49    ~l1_lattices(sK0) | v2_struct_0(sK0) | spl4_7),
% 0.21/0.49    inference(resolution,[],[f174,f51])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | spl4_7),
% 0.21/0.49    inference(avatar_component_clause,[],[f172])).
% 0.21/0.49  fof(f185,plain,(
% 0.21/0.49    spl4_6),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f184])).
% 0.21/0.49  fof(f184,plain,(
% 0.21/0.49    $false | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f183,f40])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f182,f37])).
% 0.21/0.49  fof(f182,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~l3_lattices(sK0) | spl4_6),
% 0.21/0.49    inference(subsumption_resolution,[],[f179,f38])).
% 0.21/0.49  fof(f179,plain,(
% 0.21/0.49    ~v10_lattices(sK0) | v2_struct_0(sK0) | ~l3_lattices(sK0) | spl4_6),
% 0.21/0.49    inference(resolution,[],[f170,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~v6_lattices(sK0) | spl4_6),
% 0.21/0.49    inference(avatar_component_clause,[],[f168])).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    ~spl4_6 | ~spl4_7 | ~spl4_1 | spl4_4),
% 0.21/0.49    inference(avatar_split_clause,[],[f166,f155,f108,f172,f168])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v6_lattices(sK0) | (~spl4_1 | spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f165,f37])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~v6_lattices(sK0) | v2_struct_0(sK0) | (~spl4_1 | spl4_4)),
% 0.21/0.49    inference(subsumption_resolution,[],[f164,f109])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | spl4_4),
% 0.21/0.49    inference(subsumption_resolution,[],[f163,f41])).
% 0.21/0.49  fof(f163,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~l1_lattices(sK0) | ~v6_lattices(sK0) | v2_struct_0(sK0) | spl4_4),
% 0.21/0.49    inference(resolution,[],[f157,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k4_lattices(X0,X1,X2),u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_lattices)).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~m1_subset_1(k4_lattices(sK0,k5_lattices(sK0),sK1),u1_struct_0(sK0)) | spl4_4),
% 0.21/0.49    inference(avatar_component_clause,[],[f155])).
% 0.21/0.49  fof(f120,plain,(
% 0.21/0.49    spl4_1),
% 0.21/0.49    inference(avatar_contradiction_clause,[],[f119])).
% 0.21/0.49  fof(f119,plain,(
% 0.21/0.49    $false | spl4_1),
% 0.21/0.49    inference(subsumption_resolution,[],[f117,f40])).
% 0.21/0.49  fof(f117,plain,(
% 0.21/0.49    ~l3_lattices(sK0) | spl4_1),
% 0.21/0.49    inference(resolution,[],[f110,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f10])).
% 0.21/0.49  fof(f10,plain,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => l1_lattices(X0))),
% 0.21/0.49    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.49  fof(f5,axiom,(
% 0.21/0.49    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.21/0.49  fof(f110,plain,(
% 0.21/0.49    ~l1_lattices(sK0) | spl4_1),
% 0.21/0.49    inference(avatar_component_clause,[],[f108])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (10091)------------------------------
% 0.21/0.49  % (10091)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (10091)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (10091)Memory used [KB]: 6268
% 0.21/0.49  % (10091)Time elapsed: 0.050 s
% 0.21/0.49  % (10091)------------------------------
% 0.21/0.49  % (10091)------------------------------
% 0.21/0.49  % (10085)Success in time 0.125 s
%------------------------------------------------------------------------------
