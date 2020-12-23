%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1205+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 188 expanded)
%              Number of leaves         :   25 (  76 expanded)
%              Depth                    :   12
%              Number of atoms          :  479 ( 859 expanded)
%              Number of equality atoms :   87 ( 144 expanded)
%              Maximal formula depth    :   12 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f167,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f84,f95,f98,f106,f119,f144,f157,f163,f166])).

fof(f166,plain,
    ( ~ spl5_2
    | ~ spl5_11
    | spl5_19 ),
    inference(avatar_split_clause,[],[f165,f161,f117,f66])).

fof(f66,plain,
    ( spl5_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f117,plain,
    ( spl5_11
  <=> ! [X0] :
        ( k1_lattices(sK0,k5_lattices(sK0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f161,plain,
    ( spl5_19
  <=> sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f165,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_11
    | spl5_19 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl5_11
    | spl5_19 ),
    inference(superposition,[],[f162,f118])).

fof(f118,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k5_lattices(sK0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f162,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( ~ spl5_2
    | ~ spl5_10
    | ~ spl5_19
    | spl5_1
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f158,f155,f62,f161,f114,f66])).

fof(f114,plain,
    ( spl5_10
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

% (25695)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% (25702)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f62,plain,
    ( spl5_1
  <=> sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f155,plain,
    ( spl5_18
  <=> ! [X1,X0] :
        ( k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f158,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl5_1
    | ~ spl5_18 ),
    inference(superposition,[],[f63,f156])).

fof(f156,plain,
    ( ! [X0,X1] :
        ( k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f155])).

fof(f63,plain,
    ( sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f157,plain,
    ( ~ spl5_3
    | spl5_6
    | spl5_18
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f153,f78,f155,f82,f70])).

fof(f70,plain,
    ( spl5_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f82,plain,
    ( spl5_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f78,plain,
    ( spl5_5
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( k3_lattices(sK0,X0,X1) = k1_lattices(sK0,X0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ l3_lattices(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f152,f79])).

fof(f79,plain,
    ( v10_lattices(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f152,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f151])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | k3_lattices(X1,X0,X2) = k1_lattices(X1,X0,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

% (25702)Refutation not found, incomplete strategy% (25702)------------------------------
% (25702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25702)Termination reason: Refutation not found, incomplete strategy

% (25702)Memory used [KB]: 6012
% (25702)Time elapsed: 0.003 s
% (25702)------------------------------
% (25702)------------------------------
fof(f9,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v8_lattices(X0)
          & v7_lattices(X0)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k3_lattices(X1,X2,X0) = k1_lattices(X1,X2,X0)
      | ~ m1_subset_1(X0,u1_struct_0(X1))
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f58,f45])).

fof(f45,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l2_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f144,plain,
    ( spl5_6
    | ~ spl5_7
    | spl5_10 ),
    inference(avatar_split_clause,[],[f143,f114,f90,f82])).

fof(f90,plain,
    ( spl5_7
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f143,plain,
    ( ~ l1_lattices(sK0)
    | v2_struct_0(sK0)
    | spl5_10 ),
    inference(resolution,[],[f115,f49])).

fof(f49,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f115,plain,
    ( ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f114])).

fof(f119,plain,
    ( ~ spl5_10
    | spl5_11
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(avatar_split_clause,[],[f112,f104,f93,f117,f114])).

fof(f93,plain,
    ( spl5_8
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f104,plain,
    ( spl5_9
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f112,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k5_lattices(sK0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) )
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(duplicate_literal_removal,[],[f107])).

fof(f107,plain,
    ( ! [X0] :
        ( k1_lattices(sK0,k5_lattices(sK0),X0) = X0
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_8
    | ~ spl5_9 ),
    inference(superposition,[],[f105,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f93])).

fof(f105,plain,
    ( ! [X0,X1] :
        ( k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f106,plain,
    ( spl5_6
    | ~ spl5_3
    | spl5_9
    | ~ spl5_5 ),
    inference(avatar_split_clause,[],[f102,f78,f104,f70,f82])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,k2_lattices(sK0,X0,X1),X1) = X1
        | ~ l3_lattices(sK0)
        | v2_struct_0(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_5 ),
    inference(resolution,[],[f100,f79])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( ~ v10_lattices(X1)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(duplicate_literal_removal,[],[f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,u1_struct_0(X1))
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | k1_lattices(X1,k2_lattices(X1,X2,X0),X0) = X0
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ v10_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X1) ) ),
    inference(resolution,[],[f54,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X4,X0,X3] :
      ( ~ v8_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
            & m1_subset_1(sK4(X0),u1_struct_0(X0))
            & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4])],[f34,f36,f35])).

fof(f35,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X2] :
          ( k1_lattices(X0,k2_lattices(X0,sK3(X0),X2),X2) != X2
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK4(X0) != k1_lattices(X0,k2_lattices(X0,sK3(X0),sK4(X0)),sK4(X0))
        & m1_subset_1(sK4(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k1_lattices(X0,k2_lattices(X0,X3,X4),X4) = X4
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( ( v8_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) != X2
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v8_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v8_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v8_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k1_lattices(X0,k2_lattices(X0,X1,X2),X2) = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_lattices)).

fof(f98,plain,
    ( ~ spl5_3
    | spl5_7 ),
    inference(avatar_split_clause,[],[f96,f90,f70])).

fof(f96,plain,
    ( ~ l3_lattices(sK0)
    | spl5_7 ),
    inference(resolution,[],[f91,f44])).

fof(f44,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,
    ( ~ l1_lattices(sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f95,plain,
    ( spl5_6
    | ~ spl5_7
    | spl5_8
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f87,f74,f93,f90,f82])).

fof(f74,plain,
    ( spl5_4
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),X0)
        | ~ l1_lattices(sK0)
        | v2_struct_0(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f86,f75])).

fof(f75,plain,
    ( v13_lattices(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f86,plain,(
    ! [X0,X3] :
      ( ~ v13_lattices(X0)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(global_subsumption,[],[f49,f60])).

fof(f60,plain,(
    ! [X0,X3] :
      ( k5_lattices(X0) = k2_lattices(X0,k5_lattices(X0),X3)
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( k2_lattices(X0,X1,X3) = X1
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k5_lattices(X0) != X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v13_lattices(X0)
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f30,f31])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( k2_lattices(X0,X2,X1) != X1
            | k2_lattices(X0,X1,X2) != X1 )
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( ( k2_lattices(X0,sK2(X0,X1),X1) != X1
          | k2_lattices(X0,X1,sK2(X0,X1)) != X1 )
        & m1_subset_1(sK2(X0,X1),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(rectify,[],[f29])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d16_lattices)).

fof(f84,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f38,f82])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v13_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( k3_lattices(X0,k5_lattices(X0),X1) != X1
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( k3_lattices(sK0,k5_lattices(sK0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v13_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( k3_lattices(sK0,k5_lattices(sK0),X1) != X1
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) != X1
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

fof(f80,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f40,f74])).

fof(f40,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f72,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f41,f70])).

fof(f41,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f66])).

fof(f42,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f43,f62])).

fof(f43,plain,(
    sK1 != k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
