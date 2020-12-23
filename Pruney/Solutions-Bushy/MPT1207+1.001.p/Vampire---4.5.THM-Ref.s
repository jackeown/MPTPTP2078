%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1207+1.001 : TPTP v7.4.0. Released v7.4.0.
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

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 289 expanded)
%              Number of leaves         :   29 ( 141 expanded)
%              Depth                    :    7
%              Number of atoms          :  460 (1090 expanded)
%              Number of equality atoms :   15 (  17 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f215,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f74,f79,f85,f91,f97,f103,f109,f115,f121,f127,f133,f186,f203,f213,f214])).

fof(f214,plain,
    ( sK1 != k1_lattices(sK0,k5_lattices(sK0),sK1)
    | r1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ r1_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f213,plain,
    ( ~ spl2_27
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_6
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f161,f124,f118,f112,f106,f76,f61,f56,f51,f210])).

fof(f210,plain,
    ( spl2_27
  <=> r1_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f51,plain,
    ( spl2_1
  <=> r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f56,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f61,plain,
    ( spl2_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f76,plain,
    ( spl2_6
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f106,plain,
    ( spl2_11
  <=> v6_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f112,plain,
    ( spl2_12
  <=> v8_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f118,plain,
    ( spl2_13
  <=> v9_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f124,plain,
    ( spl2_14
  <=> m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f161,plain,
    ( ~ r1_lattices(sK0,k5_lattices(sK0),sK1)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_6
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f78,f108,f114,f120,f63,f58,f53,f126,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ r1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r3_lattices(X0,X1,X2)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( ( r3_lattices(X0,X1,X2)
          | ~ r1_lattices(X0,X1,X2) )
        & ( r1_lattices(X0,X1,X2)
          | ~ r3_lattices(X0,X1,X2) ) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) )
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( r3_lattices(X0,X1,X2)
      <=> r1_lattices(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r3_lattices)).

fof(f126,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f53,plain,
    ( ~ r3_lattices(sK0,k5_lattices(sK0),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f58,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f63,plain,
    ( l3_lattices(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f120,plain,
    ( v9_lattices(sK0)
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f118])).

fof(f114,plain,
    ( v8_lattices(sK0)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f108,plain,
    ( v6_lattices(sK0)
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f106])).

fof(f78,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f203,plain,
    ( spl2_25
    | ~ spl2_2
    | spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f198,f130,f124,f94,f88,f76,f56,f200])).

fof(f200,plain,
    ( spl2_25
  <=> sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f88,plain,
    ( spl2_8
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f94,plain,
    ( spl2_9
  <=> v4_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f130,plain,
    ( spl2_15
  <=> sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f198,plain,
    ( sK1 = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl2_2
    | spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_14
    | ~ spl2_15 ),
    inference(forward_demodulation,[],[f163,f132])).

fof(f132,plain,
    ( sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f130])).

fof(f163,plain,
    ( k3_lattices(sK0,k5_lattices(sK0),sK1) = k1_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl2_2
    | spl2_6
    | ~ spl2_8
    | ~ spl2_9
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f78,f96,f90,f58,f126,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,u1_struct_0(X0))
        & m1_subset_1(X1,u1_struct_0(X0))
        & l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => k3_lattices(X0,X1,X2) = k1_lattices(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_lattices)).

fof(f90,plain,
    ( l2_lattices(sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f88])).

fof(f96,plain,
    ( v4_lattices(sK0)
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f186,plain,
    ( spl2_22
    | ~ spl2_2
    | ~ spl2_3
    | spl2_6
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f167,f124,f118,f112,f106,f100,f76,f61,f56,f183])).

fof(f183,plain,
    ( spl2_22
  <=> r1_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f100,plain,
    ( spl2_10
  <=> v5_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f167,plain,
    ( r1_lattices(sK0,k5_lattices(sK0),k1_lattices(sK0,k5_lattices(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_3
    | spl2_6
    | ~ spl2_10
    | ~ spl2_11
    | ~ spl2_12
    | ~ spl2_13
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f78,f102,f108,f114,f120,f63,f58,f126,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v9_lattices(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_lattices(X0,X1,k1_lattices(X0,X1,X2))
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v9_lattices(X0)
      | ~ v8_lattices(X0)
      | ~ v6_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

% (24583)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
fof(f6,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => r1_lattices(X0,X1,k1_lattices(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_lattices)).

fof(f102,plain,
    ( v5_lattices(sK0)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f100])).

fof(f133,plain,
    ( spl2_15
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f128,f76,f71,f66,f61,f56,f130])).

fof(f66,plain,
    ( spl2_4
  <=> v13_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f71,plain,
    ( spl2_5
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f128,plain,
    ( sK1 = k3_lattices(sK0,k5_lattices(sK0),sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f78,f73,f68,f63,f58,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k3_lattices(X0,k5_lattices(X0),X1) = X1
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k3_lattices(X0,k5_lattices(X0),X1) = X1
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l3_lattices(X0)
      | ~ v13_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_lattices)).

fof(f68,plain,
    ( v13_lattices(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f73,plain,
    ( v10_lattices(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f127,plain,
    ( spl2_14
    | spl2_6
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f122,f82,f76,f124])).

fof(f82,plain,
    ( spl2_7
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f122,plain,
    ( m1_subset_1(k5_lattices(sK0),u1_struct_0(sK0))
    | spl2_6
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f78,f84,f39])).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( m1_subset_1(k5_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_lattices(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_lattices)).

fof(f84,plain,
    ( l1_lattices(sK0)
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f82])).

fof(f121,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f116,f76,f71,f61,f118])).

fof(f116,plain,
    ( v9_lattices(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f63,f78,f73,f49])).

fof(f49,plain,(
    ! [X0] :
      ( v9_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( v9_lattices(X0)
        & v8_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
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

fof(f115,plain,
    ( spl2_12
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f110,f76,f71,f61,f112])).

fof(f110,plain,
    ( v8_lattices(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f63,f78,f73,f48])).

fof(f48,plain,(
    ! [X0] :
      ( v8_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f109,plain,
    ( spl2_11
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f104,f76,f71,f61,f106])).

fof(f104,plain,
    ( v6_lattices(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f63,f78,f73,f47])).

fof(f47,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,
    ( spl2_10
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f98,f76,f71,f61,f100])).

fof(f98,plain,
    ( v5_lattices(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f63,f78,f73,f46])).

fof(f46,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f97,plain,
    ( spl2_9
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f92,f76,f71,f61,f94])).

fof(f92,plain,
    ( v4_lattices(sK0)
    | ~ spl2_3
    | ~ spl2_5
    | spl2_6 ),
    inference(unit_resulting_resolution,[],[f63,f78,f73,f45])).

% (24583)Refutation not found, incomplete strategy% (24583)------------------------------
% (24583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f45,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f25])).

% (24583)Termination reason: Refutation not found, incomplete strategy

% (24583)Memory used [KB]: 1535
% (24583)Time elapsed: 0.100 s
% (24583)------------------------------
% (24583)------------------------------
fof(f91,plain,
    ( spl2_8
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f86,f61,f88])).

fof(f86,plain,
    ( l2_lattices(sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f63,f43])).

fof(f43,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f85,plain,
    ( spl2_7
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f80,f61,f82])).

fof(f80,plain,
    ( l1_lattices(sK0)
    | ~ spl2_3 ),
    inference(unit_resulting_resolution,[],[f63,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f79,plain,(
    ~ spl2_6 ),
    inference(avatar_split_clause,[],[f30,f76])).

fof(f30,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ~ r3_lattices(sK0,k5_lattices(sK0),sK1)
    & m1_subset_1(sK1,u1_struct_0(sK0))
    & l3_lattices(sK0)
    & v13_lattices(sK0)
    & v10_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f12,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r3_lattices(X0,k5_lattices(X0),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r3_lattices(sK0,k5_lattices(sK0),X1)
          & m1_subset_1(X1,u1_struct_0(sK0)) )
      & l3_lattices(sK0)
      & v13_lattices(sK0)
      & v10_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ~ r3_lattices(sK0,k5_lattices(sK0),X1)
        & m1_subset_1(X1,u1_struct_0(sK0)) )
   => ( ~ r3_lattices(sK0,k5_lattices(sK0),sK1)
      & m1_subset_1(sK1,u1_struct_0(sK0)) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r3_lattices(X0,k5_lattices(X0),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l3_lattices(X0)
      & v13_lattices(X0)
      & v10_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (24590)Refutation not found, incomplete strategy% (24590)------------------------------
% (24590)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24590)Termination reason: Refutation not found, incomplete strategy

% (24590)Memory used [KB]: 10618
% (24590)Time elapsed: 0.062 s
% (24590)------------------------------
% (24590)------------------------------
fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & v13_lattices(X0)
          & v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v13_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r3_lattices(X0,k5_lattices(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattices)).

fof(f74,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f31,f71])).

fof(f31,plain,(
    v10_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f69,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f32,f66])).

fof(f32,plain,(
    v13_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f33,f61])).

fof(f33,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f59,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f56])).

fof(f34,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f28])).

fof(f54,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f35,f51])).

fof(f35,plain,(
    ~ r3_lattices(sK0,k5_lattices(sK0),sK1) ),
    inference(cnf_transformation,[],[f28])).

%------------------------------------------------------------------------------
