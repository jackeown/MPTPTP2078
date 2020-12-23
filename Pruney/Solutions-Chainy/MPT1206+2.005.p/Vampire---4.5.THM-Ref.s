%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 249 expanded)
%              Number of leaves         :   30 ( 116 expanded)
%              Depth                    :    9
%              Number of atoms          :  439 ( 955 expanded)
%              Number of equality atoms :   54 ( 103 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (20460)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
fof(f253,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f91,f97,f103,f109,f115,f121,f127,f141,f207,f246,f251,f252])).

fof(f252,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | k4_lattices(sK0,k5_lattices(sK0),sK1) != k2_lattices(sK0,k5_lattices(sK0),sK1)
    | k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1))
    | k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f251,plain,
    ( spl4_27
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(avatar_split_clause,[],[f250,f139,f124,f118,f62,f227])).

fof(f227,plain,
    ( spl4_27
  <=> sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f62,plain,
    ( spl4_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f118,plain,
    ( spl4_12
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f124,plain,
    ( spl4_13
  <=> sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f139,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,X1,X0) = k3_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f250,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_13
    | ~ spl4_15 ),
    inference(forward_demodulation,[],[f175,f126])).

fof(f126,plain,
    ( sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f124])).

fof(f175,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl4_2
    | ~ spl4_12
    | ~ spl4_15 ),
    inference(unit_resulting_resolution,[],[f64,f120,f140])).

fof(f140,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | k1_lattices(sK0,X1,X0) = k3_lattices(sK0,X1,X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f139])).

fof(f120,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f118])).

fof(f64,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f62])).

fof(f246,plain,
    ( spl4_30
    | ~ spl4_2
    | spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f179,f118,f106,f88,f82,f62,f243])).

fof(f243,plain,
    ( spl4_30
  <=> k4_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f82,plain,
    ( spl4_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f88,plain,
    ( spl4_7
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f106,plain,
    ( spl4_10
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f179,plain,
    ( k4_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl4_2
    | spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f84,f108,f90,f64,f120,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ v6_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).

fof(f90,plain,
    ( l1_lattices(sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f88])).

fof(f108,plain,
    ( v6_lattices(sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f106])).

fof(f84,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f207,plain,
    ( spl4_23
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f189,f118,f112,f82,f67,f62,f204])).

fof(f204,plain,
    ( spl4_23
  <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f67,plain,
    ( spl4_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f112,plain,
    ( spl4_11
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

% (20463)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
fof(f189,plain,
    ( k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_6
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f84,f69,f114,f64,f120,f44])).

fof(f44,plain,(
    ! [X4,X0,X3] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X4,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0)))
            & m1_subset_1(sK3(X0),u1_struct_0(X0))
            & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f34,f33])).

% (20466)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (20461)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
fof(f33,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
     => ( ? [X2] :
            ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2))
            & m1_subset_1(X2,u1_struct_0(X0)) )
        & m1_subset_1(sK2(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

% (20471)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
fof(f34,plain,(
    ! [X0] :
      ( ? [X2] :
          ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2))
          & m1_subset_1(X2,u1_struct_0(X0)) )
     => ( sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0)))
        & m1_subset_1(sK3(X0),u1_struct_0(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X3] :
              ( ! [X4] :
                  ( k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3
                  | ~ m1_subset_1(X4,u1_struct_0(X0)) )
              | ~ m1_subset_1(X3,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(rectify,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v9_lattices(X0)
          | ? [X1] :
              ( ? [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1
                  & m1_subset_1(X2,u1_struct_0(X0)) )
              & m1_subset_1(X1,u1_struct_0(X0)) ) )
        & ( ! [X1] :
              ( ! [X2] :
                  ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                  | ~ m1_subset_1(X2,u1_struct_0(X0)) )
              | ~ m1_subset_1(X1,u1_struct_0(X0)) )
          | ~ v9_lattices(X0) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
      <=> ! [X1] :
            ( ! [X2] :
                ( k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1
                | ~ m1_subset_1(X2,u1_struct_0(X0)) )
            | ~ m1_subset_1(X1,u1_struct_0(X0)) ) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v9_lattices(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).

fof(f114,plain,
    ( v9_lattices(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f112])).

fof(f69,plain,
    ( l3_lattices(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f67])).

fof(f141,plain,
    ( ~ spl4_9
    | ~ spl4_8
    | spl4_15
    | spl4_6 ),
    inference(avatar_split_clause,[],[f132,f82,f139,f94,f100])).

fof(f100,plain,
    ( spl4_9
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f94,plain,
    ( spl4_8
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f132,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ l2_lattices(sK0)
        | ~ v4_lattices(sK0)
        | k1_lattices(sK0,X1,X0) = k3_lattices(sK0,X1,X0) )
    | spl4_6 ),
    inference(resolution,[],[f43,f84])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f127,plain,
    ( spl4_13
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f122,f82,f77,f72,f67,f62,f124])).

fof(f72,plain,
    ( spl4_4
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f77,plain,
    ( spl4_5
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f122,plain,
    ( sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f84,f79,f74,f69,f64,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => k3_lattices(X0,k5_lattices(X0),X1) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).

fof(f74,plain,
    ( v13_lattices(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f72])).

fof(f79,plain,
    ( v10_lattices(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f121,plain,
    ( spl4_12
    | spl4_6
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f116,f88,f82,f118])).

fof(f116,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl4_6
    | ~ spl4_7 ),
    inference(unit_resulting_resolution,[],[f84,f90,f49])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f115,plain,
    ( spl4_11
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f110,f82,f77,f67,f112])).

fof(f110,plain,
    ( v9_lattices(sK0)
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f69,f84,f79,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v6_lattices(X0)
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
       => ( v9_lattices(X0)
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
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v9_lattices(X0)
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

fof(f109,plain,
    ( spl4_10
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f104,f82,f77,f67,f106])).

fof(f104,plain,
    ( v6_lattices(sK0)
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f69,f84,f79,f52])).

fof(f52,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f103,plain,
    ( spl4_9
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f98,f82,f77,f67,f100])).

fof(f98,plain,
    ( v4_lattices(sK0)
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f69,f84,f79,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f97,plain,
    ( spl4_8
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f92,f67,f94])).

fof(f92,plain,
    ( l2_lattices(sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f69,f55])).

fof(f55,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f91,plain,
    ( spl4_7
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f86,f67,f88])).

fof(f86,plain,
    ( l1_lattices(sK0)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f69,f54])).

fof(f54,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f85,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f36,f82])).

fof(f36,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v13_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f29,f28])).

fof(f28,plain,
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

fof(f29,plain,
    ( ? [X1] :
        ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattices)).

fof(f80,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f38,f72])).

fof(f38,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f70,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f39,f67])).

fof(f39,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f30])).

fof(f65,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f40,f62])).

fof(f40,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f60,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f41,f57])).

fof(f57,plain,
    ( spl4_1
  <=> k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f41,plain,(
    k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 17:19:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.49  % (20456)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.50  % (20455)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.50  % (20451)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.50  % (20450)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (20452)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.50  % (20473)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.50  % (20453)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (20453)Refutation not found, incomplete strategy% (20453)------------------------------
% 0.20/0.50  % (20453)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (20465)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.50  % (20473)Refutation not found, incomplete strategy% (20473)------------------------------
% 0.20/0.50  % (20473)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (20464)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.50  % (20472)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.50  % (20459)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.50  % (20473)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (20473)Memory used [KB]: 10618
% 0.20/0.50  % (20473)Time elapsed: 0.057 s
% 0.20/0.50  % (20473)------------------------------
% 0.20/0.50  % (20473)------------------------------
% 0.20/0.50  % (20469)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (20456)Refutation found. Thanks to Tanya!
% 0.20/0.51  % SZS status Theorem for theBenchmark
% 0.20/0.51  % (20470)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.51  % (20462)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (20453)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (20453)Memory used [KB]: 10618
% 0.20/0.51  % (20453)Time elapsed: 0.093 s
% 0.20/0.51  % (20453)------------------------------
% 0.20/0.51  % (20453)------------------------------
% 0.20/0.51  % (20457)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.51  % SZS output start Proof for theBenchmark
% 0.20/0.51  % (20460)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.51  fof(f253,plain,(
% 0.20/0.51    $false),
% 0.20/0.51    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f91,f97,f103,f109,f115,f121,f127,f141,f207,f246,f251,f252])).
% 0.20/0.51  fof(f252,plain,(
% 0.20/0.51    sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1) | k4_lattices(sK0,k5_lattices(sK0),sK1) != k2_lattices(sK0,k5_lattices(sK0),sK1) | k5_lattices(sK0) != k2_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1)) | k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.51  fof(f251,plain,(
% 0.20/0.51    spl4_27 | ~spl4_2 | ~spl4_12 | ~spl4_13 | ~spl4_15),
% 0.20/0.51    inference(avatar_split_clause,[],[f250,f139,f124,f118,f62,f227])).
% 0.20/0.51  fof(f227,plain,(
% 0.20/0.51    spl4_27 <=> sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.20/0.51  fof(f62,plain,(
% 0.20/0.51    spl4_2 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.51  fof(f118,plain,(
% 0.20/0.51    spl4_12 <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.51  fof(f124,plain,(
% 0.20/0.51    spl4_13 <=> sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.51  fof(f139,plain,(
% 0.20/0.51    spl4_15 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,X1,X0) = k3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.20/0.51  fof(f250,plain,(
% 0.20/0.51    sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) | (~spl4_2 | ~spl4_12 | ~spl4_13 | ~spl4_15)),
% 0.20/0.51    inference(forward_demodulation,[],[f175,f126])).
% 0.20/0.51  fof(f126,plain,(
% 0.20/0.51    sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) | ~spl4_13),
% 0.20/0.51    inference(avatar_component_clause,[],[f124])).
% 0.20/0.51  fof(f175,plain,(
% 0.20/0.51    k3_lattices(sK0,k5_lattices(sK0),sK1) = k1_lattices(sK0,k5_lattices(sK0),sK1) | (~spl4_2 | ~spl4_12 | ~spl4_15)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f64,f120,f140])).
% 0.20/0.51  fof(f140,plain,(
% 0.20/0.51    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | k1_lattices(sK0,X1,X0) = k3_lattices(sK0,X1,X0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl4_15),
% 0.20/0.51    inference(avatar_component_clause,[],[f139])).
% 0.20/0.51  fof(f120,plain,(
% 0.20/0.51    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | ~spl4_12),
% 0.20/0.51    inference(avatar_component_clause,[],[f118])).
% 0.20/0.51  fof(f64,plain,(
% 0.20/0.51    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_2),
% 0.20/0.51    inference(avatar_component_clause,[],[f62])).
% 0.20/0.51  fof(f246,plain,(
% 0.20/0.51    spl4_30 | ~spl4_2 | spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f179,f118,f106,f88,f82,f62,f243])).
% 0.20/0.51  fof(f243,plain,(
% 0.20/0.51    spl4_30 <=> k4_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.51  fof(f82,plain,(
% 0.20/0.51    spl4_6 <=> v2_struct_0(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.51  fof(f88,plain,(
% 0.20/0.51    spl4_7 <=> l1_lattices(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.51  fof(f106,plain,(
% 0.20/0.51    spl4_10 <=> v6_lattices(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.51  fof(f179,plain,(
% 0.20/0.51    k4_lattices(sK0,k5_lattices(sK0),sK1) = k2_lattices(sK0,k5_lattices(sK0),sK1) | (~spl4_2 | spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_12)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f84,f108,f90,f64,f120,f42])).
% 0.20/0.51  fof(f42,plain,(
% 0.20/0.51    ( ! [X2,X0,X1] : (~v6_lattices(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f16])).
% 0.20/0.51  fof(f16,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(flattening,[],[f15])).
% 0.20/0.51  fof(f15,plain,(
% 0.20/0.51    ! [X0,X1,X2] : (k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_lattices(X0) | ~v6_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.51    inference(ennf_transformation,[],[f6])).
% 0.20/0.51  fof(f6,axiom,(
% 0.20/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l1_lattices(X0) & v6_lattices(X0) & ~v2_struct_0(X0)) => k4_lattices(X0,X1,X2) = k2_lattices(X0,X1,X2))),
% 0.20/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_lattices)).
% 0.20/0.51  fof(f90,plain,(
% 0.20/0.51    l1_lattices(sK0) | ~spl4_7),
% 0.20/0.51    inference(avatar_component_clause,[],[f88])).
% 0.20/0.51  fof(f108,plain,(
% 0.20/0.51    v6_lattices(sK0) | ~spl4_10),
% 0.20/0.51    inference(avatar_component_clause,[],[f106])).
% 0.20/0.51  fof(f84,plain,(
% 0.20/0.51    ~v2_struct_0(sK0) | spl4_6),
% 0.20/0.51    inference(avatar_component_clause,[],[f82])).
% 0.20/0.51  fof(f207,plain,(
% 0.20/0.51    spl4_23 | ~spl4_2 | ~spl4_3 | spl4_6 | ~spl4_11 | ~spl4_12),
% 0.20/0.51    inference(avatar_split_clause,[],[f189,f118,f112,f82,f67,f62,f204])).
% 0.20/0.51  fof(f204,plain,(
% 0.20/0.51    spl4_23 <=> k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1))),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.20/0.51  fof(f67,plain,(
% 0.20/0.51    spl4_3 <=> l3_lattices(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.51  fof(f112,plain,(
% 0.20/0.51    spl4_11 <=> v9_lattices(sK0)),
% 0.20/0.51    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.51  % (20463)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.51  fof(f189,plain,(
% 0.20/0.51    k5_lattices(sK0) = k2_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1)) | (~spl4_2 | ~spl4_3 | spl4_6 | ~spl4_11 | ~spl4_12)),
% 0.20/0.51    inference(unit_resulting_resolution,[],[f84,f69,f114,f64,f120,f44])).
% 0.20/0.51  fof(f44,plain,(
% 0.20/0.51    ( ! [X4,X0,X3] : (~v9_lattices(X0) | ~m1_subset_1(X4,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~l3_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.51    inference(cnf_transformation,[],[f35])).
% 0.20/0.51  fof(f35,plain,(
% 0.20/0.51    ! [X0] : (((v9_lattices(X0) | ((sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f32,f34,f33])).
% 0.20/0.51  % (20466)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.51  % (20461)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ! [X0] : (? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0))) => (? [X2] : (sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(sK2(X0),u1_struct_0(X0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  % (20471)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    ! [X0] : (? [X2] : (sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),X2)) & m1_subset_1(X2,u1_struct_0(X0))) => (sK2(X0) != k2_lattices(X0,sK2(X0),k1_lattices(X0,sK2(X0),sK3(X0))) & m1_subset_1(sK3(X0),u1_struct_0(X0))))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X3] : (! [X4] : (k2_lattices(X0,X3,k1_lattices(X0,X3,X4)) = X3 | ~m1_subset_1(X4,u1_struct_0(X0))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(rectify,[],[f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ! [X0] : (((v9_lattices(X0) | ? [X1] : (? [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) != X1 & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,u1_struct_0(X0)))) & (! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~v9_lattices(X0))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(nnf_transformation,[],[f20])).
% 0.20/0.52  fof(f20,plain,(
% 0.20/0.52    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | ~l3_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : ((v9_lattices(X0) <=> ! [X1] : (! [X2] : (k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1 | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)))) | (~l3_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f2])).
% 0.20/0.52  fof(f2,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) <=> ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => k2_lattices(X0,X1,k1_lattices(X0,X1,X2)) = X1))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_lattices)).
% 0.20/0.52  fof(f114,plain,(
% 0.20/0.52    v9_lattices(sK0) | ~spl4_11),
% 0.20/0.52    inference(avatar_component_clause,[],[f112])).
% 0.20/0.52  fof(f69,plain,(
% 0.20/0.52    l3_lattices(sK0) | ~spl4_3),
% 0.20/0.52    inference(avatar_component_clause,[],[f67])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    ~spl4_9 | ~spl4_8 | spl4_15 | spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f132,f82,f139,f94,f100])).
% 0.20/0.52  fof(f100,plain,(
% 0.20/0.52    spl4_9 <=> v4_lattices(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.52  fof(f94,plain,(
% 0.20/0.52    spl4_8 <=> l2_lattices(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.52  fof(f132,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~l2_lattices(sK0) | ~v4_lattices(sK0) | k1_lattices(sK0,X1,X0) = k3_lattices(sK0,X1,X0)) ) | spl4_6),
% 0.20/0.52    inference(resolution,[],[f43,f84])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2) | (~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l2_lattices(X0) | ~v4_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,u1_struct_0(X0)) & m1_subset_1(X1,u1_struct_0(X0)) & l2_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) => k1_lattices(X0,X1,X2) = k3_lattices(X0,X1,X2))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_lattices)).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    spl4_13 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f122,f82,f77,f72,f67,f62,f124])).
% 0.20/0.52  fof(f72,plain,(
% 0.20/0.52    spl4_4 <=> v13_lattices(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.20/0.52  fof(f77,plain,(
% 0.20/0.52    spl4_5 <=> v10_lattices(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.52  fof(f122,plain,(
% 0.20/0.52    sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) | (~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | spl4_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f84,f79,f74,f69,f64,f48])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f22])).
% 0.20/0.52  fof(f22,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f21])).
% 0.20/0.52  fof(f21,plain,(
% 0.20/0.52    ! [X0] : (! [X1] : (k3_lattices(X0,k5_lattices(X0),X1) = X1 | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l3_lattices(X0) | ~v13_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f7])).
% 0.20/0.52  fof(f7,axiom,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k3_lattices(X0,k5_lattices(X0),X1) = X1))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_lattices)).
% 0.20/0.52  fof(f74,plain,(
% 0.20/0.52    v13_lattices(sK0) | ~spl4_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f72])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    v10_lattices(sK0) | ~spl4_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f77])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    spl4_12 | spl4_6 | ~spl4_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f116,f88,f82,f118])).
% 0.20/0.52  fof(f116,plain,(
% 0.20/0.52    m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) | (spl4_6 | ~spl4_7)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f84,f90,f49])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | ~l1_lattices(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0] : (m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) | (~l1_lattices(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f3])).
% 0.20/0.52  fof(f3,axiom,(
% 0.20/0.52    ! [X0] : ((l1_lattices(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_lattices)).
% 0.20/0.52  fof(f115,plain,(
% 0.20/0.52    spl4_11 | ~spl4_3 | ~spl4_5 | spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f110,f82,f77,f67,f112])).
% 0.20/0.52  fof(f110,plain,(
% 0.20/0.52    v9_lattices(sK0) | (~spl4_3 | ~spl4_5 | spl4_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f69,f84,f79,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X0] : (v9_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f26,plain,(
% 0.20/0.52    ! [X0] : ((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0))),
% 0.20/0.52    inference(flattening,[],[f25])).
% 0.20/0.52  fof(f25,plain,(
% 0.20/0.52    ! [X0] : (((v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0)) | (~v10_lattices(X0) | v2_struct_0(X0))) | ~l3_lattices(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f12])).
% 0.20/0.52  fof(f12,plain,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f11])).
% 0.20/0.52  fof(f11,plain,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f10])).
% 0.20/0.52  fof(f10,plain,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.52    inference(pure_predicate_removal,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => ((v10_lattices(X0) & ~v2_struct_0(X0)) => (v9_lattices(X0) & v8_lattices(X0) & v7_lattices(X0) & v6_lattices(X0) & v5_lattices(X0) & v4_lattices(X0) & ~v2_struct_0(X0))))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_lattices)).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    spl4_10 | ~spl4_3 | ~spl4_5 | spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f104,f82,f77,f67,f106])).
% 0.20/0.52  fof(f104,plain,(
% 0.20/0.52    v6_lattices(sK0) | (~spl4_3 | ~spl4_5 | spl4_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f69,f84,f79,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X0] : (v6_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    spl4_9 | ~spl4_3 | ~spl4_5 | spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f98,f82,f77,f67,f100])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    v4_lattices(sK0) | (~spl4_3 | ~spl4_5 | spl4_6)),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f69,f84,f79,f51])).
% 0.20/0.52  fof(f51,plain,(
% 0.20/0.52    ( ! [X0] : (v4_lattices(X0) | ~v10_lattices(X0) | v2_struct_0(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f26])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    spl4_8 | ~spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f92,f67,f94])).
% 0.20/0.52  fof(f92,plain,(
% 0.20/0.52    l2_lattices(sK0) | ~spl4_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f69,f55])).
% 0.20/0.52  fof(f55,plain,(
% 0.20/0.52    ( ! [X0] : (l2_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0] : ((l2_lattices(X0) & l1_lattices(X0)) | ~l3_lattices(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f4])).
% 0.20/0.52  fof(f4,axiom,(
% 0.20/0.52    ! [X0] : (l3_lattices(X0) => (l2_lattices(X0) & l1_lattices(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l3_lattices)).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    spl4_7 | ~spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f86,f67,f88])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    l1_lattices(sK0) | ~spl4_3),
% 0.20/0.52    inference(unit_resulting_resolution,[],[f69,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X0] : (l1_lattices(X0) | ~l3_lattices(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f27])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    ~spl4_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f36,f82])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    ~v2_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f30,plain,(
% 0.20/0.52    (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0))) & l3_lattices(sK0) & v13_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f14,f29,f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => (? [X1] : (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) & l3_lattices(sK0) & v13_lattices(sK0) & v10_lattices(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f29,plain,(
% 0.20/0.52    ? [X1] : (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),X1) & m1_subset_1(X1,u1_struct_0(sK0))) => (k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1) & m1_subset_1(sK1,u1_struct_0(sK0)))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f13])).
% 0.20/0.52  fof(f13,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (k5_lattices(X0) != k4_lattices(X0,k5_lattices(X0),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,negated_conjecture,(
% 0.20/0.52    ~! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 0.20/0.52    inference(negated_conjecture,[],[f8])).
% 0.20/0.52  fof(f8,conjecture,(
% 0.20/0.52    ! [X0] : ((l3_lattices(X0) & v13_lattices(X0) & v10_lattices(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => k5_lattices(X0) = k4_lattices(X0,k5_lattices(X0),X1)))),
% 0.20/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_lattices)).
% 0.20/0.52  fof(f80,plain,(
% 0.20/0.52    spl4_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f77])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    v10_lattices(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    spl4_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f38,f72])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    v13_lattices(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    spl4_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f67])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    l3_lattices(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f65,plain,(
% 0.20/0.52    spl4_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f62])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  fof(f60,plain,(
% 0.20/0.52    ~spl4_1),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f57])).
% 0.20/0.52  fof(f57,plain,(
% 0.20/0.52    spl4_1 <=> k5_lattices(sK0) = k4_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    k5_lattices(sK0) != k4_lattices(sK0,k5_lattices(sK0),sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f30])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (20456)------------------------------
% 0.20/0.52  % (20456)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20456)Termination reason: Refutation
% 0.20/0.52  % (20466)Refutation not found, incomplete strategy% (20466)------------------------------
% 0.20/0.52  % (20466)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (20466)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (20466)Memory used [KB]: 1663
% 0.20/0.52  % (20466)Time elapsed: 0.115 s
% 0.20/0.52  % (20466)------------------------------
% 0.20/0.52  % (20466)------------------------------
% 0.20/0.52  
% 0.20/0.52  % (20456)Memory used [KB]: 10746
% 0.20/0.52  % (20456)Time elapsed: 0.108 s
% 0.20/0.52  % (20456)------------------------------
% 0.20/0.52  % (20456)------------------------------
% 0.20/0.52  % (20468)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.52  % (20449)Success in time 0.163 s
%------------------------------------------------------------------------------
