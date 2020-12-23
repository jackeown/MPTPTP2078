%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 287 expanded)
%              Number of leaves         :   30 ( 151 expanded)
%              Depth                    :    7
%              Number of atoms          :  486 (2189 expanded)
%              Number of equality atoms :   16 (  16 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f585,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f52,f57,f62,f72,f77,f82,f87,f92,f97,f102,f107,f112,f118,f136,f203,f230,f275,f573,f584])).

fof(f584,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK0,sK0,sK3)
    | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK0,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

% (3316)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% (3321)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
fof(f573,plain,
    ( spl4_79
    | ~ spl4_5
    | spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_13
    | ~ spl4_14
    | spl4_30 ),
    inference(avatar_split_clause,[],[f566,f227,f115,f109,f104,f99,f74,f69,f569])).

fof(f569,plain,
    ( spl4_79
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK0,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).

fof(f69,plain,
    ( spl4_5
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f74,plain,
    ( spl4_6
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f99,plain,
    ( spl4_11
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f104,plain,
    ( spl4_12
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f109,plain,
    ( spl4_13
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f115,plain,
    ( spl4_14
  <=> m1_pre_topc(sK0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f227,plain,
    ( spl4_30
  <=> r1_tsep_1(sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f566,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK0,sK0,sK3)
    | ~ spl4_5
    | spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_13
    | ~ spl4_14
    | spl4_30 ),
    inference(unit_resulting_resolution,[],[f111,f106,f101,f111,f76,f117,f71,f71,f229,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_pre_topc(X2,X1)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X2,X1)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X2,X1) )
                & ( m1_pre_topc(X1,X2)
                  | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
                & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                  | ~ m1_pre_topc(X1,X2) ) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ( ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                   => m1_pre_topc(X2,X1) )
                  & ( m1_pre_topc(X2,X1)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                  & ( k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
                   => m1_pre_topc(X1,X2) )
                  & ( m1_pre_topc(X1,X2)
                   => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).

fof(f229,plain,
    ( ~ r1_tsep_1(sK0,sK3)
    | spl4_30 ),
    inference(avatar_component_clause,[],[f227])).

fof(f71,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f69])).

fof(f117,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f115])).

fof(f76,plain,
    ( ~ v2_struct_0(sK3)
    | spl4_6 ),
    inference(avatar_component_clause,[],[f74])).

fof(f101,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f99])).

fof(f106,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f104])).

fof(f111,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_13 ),
    inference(avatar_component_clause,[],[f109])).

fof(f275,plain,
    ( spl4_38
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9
    | spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | spl4_13
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f205,f115,f109,f104,f99,f94,f89,f84,f79,f74,f69,f59,f54,f272])).

fof(f272,plain,
    ( spl4_38
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).

fof(f54,plain,
    ( spl4_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f59,plain,
    ( spl4_3
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f79,plain,
    ( spl4_7
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f84,plain,
    ( spl4_8
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f89,plain,
    ( spl4_9
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f94,plain,
    ( spl4_10
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f205,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK0,sK3))
    | spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | spl4_6
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9
    | spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | spl4_13
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f111,f106,f101,f96,f111,f86,f61,f81,f56,f76,f71,f91,f91,f117,f38])).

fof(f38,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X4)
      | ~ m1_pre_topc(X1,X3)
      | ~ m1_pre_topc(X4,X0)
      | v2_struct_0(X4)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      | r1_tsep_1(X1,X2)
                      | ~ m1_pre_topc(X2,X4)
                      | ~ m1_pre_topc(X1,X3)
                      | ~ m1_pre_topc(X4,X0)
                      | v2_struct_0(X4) )
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f91,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f56,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f54])).

fof(f81,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f79])).

fof(f61,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f86,plain,
    ( ~ v2_struct_0(sK2)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f96,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f94])).

fof(f230,plain,
    ( ~ spl4_30
    | ~ spl4_5
    | spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_13
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f218,f115,f109,f104,f99,f74,f69,f227])).

fof(f218,plain,
    ( ~ r1_tsep_1(sK0,sK3)
    | ~ spl4_5
    | spl4_6
    | ~ spl4_11
    | ~ spl4_12
    | spl4_13
    | ~ spl4_14 ),
    inference(unit_resulting_resolution,[],[f111,f106,f101,f76,f111,f71,f71,f117,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ~ r1_tsep_1(X2,X1)
                & ~ r1_tsep_1(X1,X2) )
              | ~ m1_pre_topc(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f203,plain,
    ( ~ spl4_28
    | spl4_1
    | ~ spl4_17 ),
    inference(avatar_split_clause,[],[f190,f133,f49,f200])).

fof(f200,plain,
    ( spl4_28
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f49,plain,
    ( spl4_1
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f133,plain,
    ( spl4_17
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f190,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | spl4_1
    | ~ spl4_17 ),
    inference(unit_resulting_resolution,[],[f51,f135,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f135,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f133])).

fof(f51,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f136,plain,
    ( spl4_17
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f119,f99,f69,f133])).

fof(f119,plain,
    ( l1_pre_topc(sK3)
    | ~ spl4_5
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f101,f71,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f118,plain,
    ( spl4_14
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f113,f99,f115])).

fof(f113,plain,
    ( m1_pre_topc(sK0,sK0)
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f112,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f25,f109])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3)
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3)
              & ~ r1_tsep_1(sK1,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(sK1,X3)
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3)
            & ~ r1_tsep_1(sK1,X2)
            & m1_pre_topc(X2,X3)
            & m1_pre_topc(sK1,X3)
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3)
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(sK2,X3)
          & m1_pre_topc(sK1,X3)
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3)
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(sK2,X3)
        & m1_pre_topc(sK1,X3)
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK1,sK3)
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f107,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f26,f104])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f102,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f27,f99])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f97,plain,(
    ~ spl4_10 ),
    inference(avatar_split_clause,[],[f28,f94])).

fof(f28,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f92,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f29,f89])).

fof(f29,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f87,plain,(
    ~ spl4_8 ),
    inference(avatar_split_clause,[],[f30,f84])).

fof(f30,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f31,f79])).

fof(f31,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f77,plain,(
    ~ spl4_6 ),
    inference(avatar_split_clause,[],[f32,f74])).

fof(f32,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f72,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f35,f59])).

fof(f35,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f36,f54])).

fof(f36,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f37,f49])).

fof(f37,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:30:23 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.48  % (3302)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.48  % (3322)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.20/0.49  % (3310)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.20/0.49  % (3308)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.20/0.49  % (3305)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (3324)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.20/0.49  % (3323)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.20/0.49  % (3315)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.20/0.49  % (3306)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.20/0.49  % (3313)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.50  % (3318)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.20/0.50  % (3307)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.50  % (3304)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.20/0.50  % (3310)Refutation not found, incomplete strategy% (3310)------------------------------
% 0.20/0.50  % (3310)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3300)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.20/0.50  % (3303)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.20/0.50  % (3317)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.20/0.50  % (3303)Refutation not found, incomplete strategy% (3303)------------------------------
% 0.20/0.50  % (3303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.50  % (3303)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.50  
% 0.20/0.50  % (3303)Memory used [KB]: 10618
% 0.20/0.50  % (3303)Time elapsed: 0.094 s
% 0.20/0.50  % (3303)------------------------------
% 0.20/0.50  % (3303)------------------------------
% 0.20/0.50  % (3301)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.20/0.51  % (3311)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.51  % (3319)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.20/0.51  % (3314)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.20/0.51  % (3310)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3310)Memory used [KB]: 10746
% 0.20/0.51  % (3310)Time elapsed: 0.098 s
% 0.20/0.51  % (3310)------------------------------
% 0.20/0.51  % (3310)------------------------------
% 0.20/0.51  % (3309)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.20/0.51  % (3312)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.51  % (3307)Refutation not found, incomplete strategy% (3307)------------------------------
% 0.20/0.51  % (3307)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (3307)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (3307)Memory used [KB]: 6268
% 0.20/0.51  % (3307)Time elapsed: 0.068 s
% 0.20/0.51  % (3307)------------------------------
% 0.20/0.51  % (3307)------------------------------
% 0.20/0.52  % (3306)Refutation found. Thanks to Tanya!
% 0.20/0.52  % SZS status Theorem for theBenchmark
% 0.20/0.52  % SZS output start Proof for theBenchmark
% 0.20/0.52  fof(f585,plain,(
% 0.20/0.52    $false),
% 0.20/0.52    inference(avatar_sat_refutation,[],[f52,f57,f62,f72,f77,f82,f87,f92,f97,f102,f107,f112,f118,f136,f203,f230,f275,f573,f584])).
% 0.20/0.52  fof(f584,plain,(
% 0.20/0.52    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != k2_tsep_1(sK0,sK0,sK3) | m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK0,sK3))),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  % (3316)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.20/0.52  % (3321)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.53  fof(f573,plain,(
% 0.20/0.53    spl4_79 | ~spl4_5 | spl4_6 | ~spl4_11 | ~spl4_12 | spl4_13 | ~spl4_14 | spl4_30),
% 0.20/0.53    inference(avatar_split_clause,[],[f566,f227,f115,f109,f104,f99,f74,f69,f569])).
% 0.20/0.53  fof(f569,plain,(
% 0.20/0.53    spl4_79 <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK0,sK0,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_79])])).
% 0.20/0.53  fof(f69,plain,(
% 0.20/0.53    spl4_5 <=> m1_pre_topc(sK3,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.20/0.53  fof(f74,plain,(
% 0.20/0.53    spl4_6 <=> v2_struct_0(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.20/0.53  fof(f99,plain,(
% 0.20/0.53    spl4_11 <=> l1_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.20/0.53  fof(f104,plain,(
% 0.20/0.53    spl4_12 <=> v2_pre_topc(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.20/0.53  fof(f109,plain,(
% 0.20/0.53    spl4_13 <=> v2_struct_0(sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.20/0.53  fof(f115,plain,(
% 0.20/0.53    spl4_14 <=> m1_pre_topc(sK0,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.20/0.53  fof(f227,plain,(
% 0.20/0.53    spl4_30 <=> r1_tsep_1(sK0,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.20/0.53  fof(f566,plain,(
% 0.20/0.53    g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = k2_tsep_1(sK0,sK0,sK3) | (~spl4_5 | spl4_6 | ~spl4_11 | ~spl4_12 | spl4_13 | ~spl4_14 | spl4_30)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f111,f106,f101,f111,f76,f117,f71,f71,f229,f41])).
% 0.20/0.53  fof(f41,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~m1_pre_topc(X2,X1) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f14])).
% 0.20/0.53  fof(f14,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f13])).
% 0.20/0.53  fof(f13,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X2,X1) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X2,X1)) & (m1_pre_topc(X1,X2) | k2_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X2))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f6])).
% 0.20/0.53  fof(f6,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ((k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) => m1_pre_topc(X2,X1)) & (m1_pre_topc(X2,X1) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) => m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) => k2_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_tsep_1)).
% 0.20/0.53  fof(f229,plain,(
% 0.20/0.53    ~r1_tsep_1(sK0,sK3) | spl4_30),
% 0.20/0.53    inference(avatar_component_clause,[],[f227])).
% 0.20/0.53  fof(f71,plain,(
% 0.20/0.53    m1_pre_topc(sK3,sK0) | ~spl4_5),
% 0.20/0.53    inference(avatar_component_clause,[],[f69])).
% 0.20/0.53  fof(f117,plain,(
% 0.20/0.53    m1_pre_topc(sK0,sK0) | ~spl4_14),
% 0.20/0.53    inference(avatar_component_clause,[],[f115])).
% 0.20/0.53  fof(f76,plain,(
% 0.20/0.53    ~v2_struct_0(sK3) | spl4_6),
% 0.20/0.53    inference(avatar_component_clause,[],[f74])).
% 0.20/0.53  fof(f101,plain,(
% 0.20/0.53    l1_pre_topc(sK0) | ~spl4_11),
% 0.20/0.53    inference(avatar_component_clause,[],[f99])).
% 0.20/0.53  fof(f106,plain,(
% 0.20/0.53    v2_pre_topc(sK0) | ~spl4_12),
% 0.20/0.53    inference(avatar_component_clause,[],[f104])).
% 0.20/0.53  fof(f111,plain,(
% 0.20/0.53    ~v2_struct_0(sK0) | spl4_13),
% 0.20/0.53    inference(avatar_component_clause,[],[f109])).
% 0.20/0.53  fof(f275,plain,(
% 0.20/0.53    spl4_38 | spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_7 | spl4_8 | ~spl4_9 | spl4_10 | ~spl4_11 | ~spl4_12 | spl4_13 | ~spl4_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f205,f115,f109,f104,f99,f94,f89,f84,f79,f74,f69,f59,f54,f272])).
% 0.20/0.53  fof(f272,plain,(
% 0.20/0.53    spl4_38 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK0,sK3))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_38])])).
% 0.20/0.53  fof(f54,plain,(
% 0.20/0.53    spl4_2 <=> r1_tsep_1(sK1,sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.20/0.53  fof(f59,plain,(
% 0.20/0.53    spl4_3 <=> m1_pre_topc(sK2,sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.20/0.53  fof(f79,plain,(
% 0.20/0.53    spl4_7 <=> m1_pre_topc(sK2,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.20/0.53  fof(f84,plain,(
% 0.20/0.53    spl4_8 <=> v2_struct_0(sK2)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.20/0.53  fof(f89,plain,(
% 0.20/0.53    spl4_9 <=> m1_pre_topc(sK1,sK0)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.20/0.53  fof(f94,plain,(
% 0.20/0.53    spl4_10 <=> v2_struct_0(sK1)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.20/0.53  fof(f205,plain,(
% 0.20/0.53    m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK0,sK3)) | (spl4_2 | ~spl4_3 | ~spl4_5 | spl4_6 | ~spl4_7 | spl4_8 | ~spl4_9 | spl4_10 | ~spl4_11 | ~spl4_12 | spl4_13 | ~spl4_14)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f111,f106,f101,f96,f111,f86,f61,f81,f56,f76,f71,f91,f91,f117,f38])).
% 0.20/0.53  fof(f38,plain,(
% 0.20/0.53    ( ! [X4,X2,X0,X3,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f12])).
% 0.20/0.53  fof(f12,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3) | ~m1_pre_topc(X4,X0) | v2_struct_0(X4)) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f11])).
% 0.20/0.53  fof(f11,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X4) | ~m1_pre_topc(X1,X3))) | (~m1_pre_topc(X4,X0) | v2_struct_0(X4))) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f4])).
% 0.20/0.53  fof(f4,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).
% 0.20/0.53  fof(f91,plain,(
% 0.20/0.53    m1_pre_topc(sK1,sK0) | ~spl4_9),
% 0.20/0.53    inference(avatar_component_clause,[],[f89])).
% 0.20/0.53  fof(f56,plain,(
% 0.20/0.53    ~r1_tsep_1(sK1,sK2) | spl4_2),
% 0.20/0.53    inference(avatar_component_clause,[],[f54])).
% 0.20/0.53  fof(f81,plain,(
% 0.20/0.53    m1_pre_topc(sK2,sK0) | ~spl4_7),
% 0.20/0.53    inference(avatar_component_clause,[],[f79])).
% 0.20/0.53  fof(f61,plain,(
% 0.20/0.53    m1_pre_topc(sK2,sK3) | ~spl4_3),
% 0.20/0.53    inference(avatar_component_clause,[],[f59])).
% 0.20/0.53  fof(f86,plain,(
% 0.20/0.53    ~v2_struct_0(sK2) | spl4_8),
% 0.20/0.53    inference(avatar_component_clause,[],[f84])).
% 0.20/0.53  fof(f96,plain,(
% 0.20/0.53    ~v2_struct_0(sK1) | spl4_10),
% 0.20/0.53    inference(avatar_component_clause,[],[f94])).
% 0.20/0.53  fof(f230,plain,(
% 0.20/0.53    ~spl4_30 | ~spl4_5 | spl4_6 | ~spl4_11 | ~spl4_12 | spl4_13 | ~spl4_14),
% 0.20/0.53    inference(avatar_split_clause,[],[f218,f115,f109,f104,f99,f74,f69,f227])).
% 0.20/0.53  fof(f218,plain,(
% 0.20/0.53    ~r1_tsep_1(sK0,sK3) | (~spl4_5 | spl4_6 | ~spl4_11 | ~spl4_12 | spl4_13 | ~spl4_14)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f111,f106,f101,f76,f111,f71,f71,f117,f44])).
% 0.20/0.53  fof(f44,plain,(
% 0.20/0.53    ( ! [X2,X0,X1] : (~r1_tsep_1(X2,X1) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f16])).
% 0.20/0.53  fof(f16,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : ((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f15])).
% 0.20/0.53  fof(f15,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (! [X2] : (((~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2)) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f3])).
% 0.20/0.53  fof(f3,axiom,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.20/0.53  fof(f203,plain,(
% 0.20/0.53    ~spl4_28 | spl4_1 | ~spl4_17),
% 0.20/0.53    inference(avatar_split_clause,[],[f190,f133,f49,f200])).
% 0.20/0.53  fof(f200,plain,(
% 0.20/0.53    spl4_28 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.20/0.53  fof(f49,plain,(
% 0.20/0.53    spl4_1 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.20/0.53  fof(f133,plain,(
% 0.20/0.53    spl4_17 <=> l1_pre_topc(sK3)),
% 0.20/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.20/0.53  fof(f190,plain,(
% 0.20/0.53    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) | (spl4_1 | ~spl4_17)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f51,f135,f45])).
% 0.20/0.53  fof(f45,plain,(
% 0.20/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f17])).
% 0.20/0.53  fof(f17,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f2])).
% 0.20/0.53  fof(f2,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.20/0.53  fof(f135,plain,(
% 0.20/0.53    l1_pre_topc(sK3) | ~spl4_17),
% 0.20/0.53    inference(avatar_component_clause,[],[f133])).
% 0.20/0.53  fof(f51,plain,(
% 0.20/0.53    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) | spl4_1),
% 0.20/0.53    inference(avatar_component_clause,[],[f49])).
% 0.20/0.53  fof(f136,plain,(
% 0.20/0.53    spl4_17 | ~spl4_5 | ~spl4_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f119,f99,f69,f133])).
% 0.20/0.53  fof(f119,plain,(
% 0.20/0.53    l1_pre_topc(sK3) | (~spl4_5 | ~spl4_11)),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f101,f71,f46])).
% 0.20/0.53  fof(f46,plain,(
% 0.20/0.53    ( ! [X0,X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f18])).
% 0.20/0.53  fof(f18,plain,(
% 0.20/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f1])).
% 0.20/0.53  fof(f1,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.20/0.53  fof(f118,plain,(
% 0.20/0.53    spl4_14 | ~spl4_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f113,f99,f115])).
% 0.20/0.53  fof(f113,plain,(
% 0.20/0.53    m1_pre_topc(sK0,sK0) | ~spl4_11),
% 0.20/0.53    inference(unit_resulting_resolution,[],[f101,f47])).
% 0.20/0.53  fof(f47,plain,(
% 0.20/0.53    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.53    inference(cnf_transformation,[],[f19])).
% 0.20/0.53  fof(f19,plain,(
% 0.20/0.53    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.53    inference(ennf_transformation,[],[f5])).
% 0.20/0.53  fof(f5,axiom,(
% 0.20/0.53    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.53  fof(f112,plain,(
% 0.20/0.53    ~spl4_13),
% 0.20/0.53    inference(avatar_split_clause,[],[f25,f109])).
% 0.20/0.53  fof(f25,plain,(
% 0.20/0.53    ~v2_struct_0(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f24,plain,(
% 0.20/0.53    (((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.20/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f10,f23,f22,f21,f20])).
% 0.20/0.53  fof(f20,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f21,plain,(
% 0.20/0.53    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f22,plain,(
% 0.20/0.53    ? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),X3) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f23,plain,(
% 0.20/0.53    ? [X3] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X3) & m1_pre_topc(sK1,X3) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 0.20/0.53    introduced(choice_axiom,[])).
% 0.20/0.53  fof(f10,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.53    inference(flattening,[],[f9])).
% 0.20/0.53  fof(f9,plain,(
% 0.20/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.53    inference(ennf_transformation,[],[f8])).
% 0.20/0.53  fof(f8,negated_conjecture,(
% 0.20/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.20/0.53    inference(negated_conjecture,[],[f7])).
% 0.20/0.53  fof(f7,conjecture,(
% 0.20/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.20/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).
% 0.20/0.53  fof(f107,plain,(
% 0.20/0.53    spl4_12),
% 0.20/0.53    inference(avatar_split_clause,[],[f26,f104])).
% 0.20/0.53  fof(f26,plain,(
% 0.20/0.53    v2_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f102,plain,(
% 0.20/0.53    spl4_11),
% 0.20/0.53    inference(avatar_split_clause,[],[f27,f99])).
% 0.20/0.53  fof(f27,plain,(
% 0.20/0.53    l1_pre_topc(sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f97,plain,(
% 0.20/0.53    ~spl4_10),
% 0.20/0.53    inference(avatar_split_clause,[],[f28,f94])).
% 0.20/0.53  fof(f28,plain,(
% 0.20/0.53    ~v2_struct_0(sK1)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f92,plain,(
% 0.20/0.53    spl4_9),
% 0.20/0.53    inference(avatar_split_clause,[],[f29,f89])).
% 0.20/0.53  fof(f29,plain,(
% 0.20/0.53    m1_pre_topc(sK1,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f87,plain,(
% 0.20/0.53    ~spl4_8),
% 0.20/0.53    inference(avatar_split_clause,[],[f30,f84])).
% 0.20/0.53  fof(f30,plain,(
% 0.20/0.53    ~v2_struct_0(sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f82,plain,(
% 0.20/0.53    spl4_7),
% 0.20/0.53    inference(avatar_split_clause,[],[f31,f79])).
% 0.20/0.53  fof(f31,plain,(
% 0.20/0.53    m1_pre_topc(sK2,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f77,plain,(
% 0.20/0.53    ~spl4_6),
% 0.20/0.53    inference(avatar_split_clause,[],[f32,f74])).
% 0.20/0.53  fof(f32,plain,(
% 0.20/0.53    ~v2_struct_0(sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f72,plain,(
% 0.20/0.53    spl4_5),
% 0.20/0.53    inference(avatar_split_clause,[],[f33,f69])).
% 0.20/0.53  fof(f33,plain,(
% 0.20/0.53    m1_pre_topc(sK3,sK0)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f62,plain,(
% 0.20/0.53    spl4_3),
% 0.20/0.53    inference(avatar_split_clause,[],[f35,f59])).
% 0.20/0.53  fof(f35,plain,(
% 0.20/0.53    m1_pre_topc(sK2,sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f57,plain,(
% 0.20/0.53    ~spl4_2),
% 0.20/0.53    inference(avatar_split_clause,[],[f36,f54])).
% 0.20/0.53  fof(f36,plain,(
% 0.20/0.53    ~r1_tsep_1(sK1,sK2)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  fof(f52,plain,(
% 0.20/0.53    ~spl4_1),
% 0.20/0.53    inference(avatar_split_clause,[],[f37,f49])).
% 0.20/0.53  fof(f37,plain,(
% 0.20/0.53    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK3)),
% 0.20/0.53    inference(cnf_transformation,[],[f24])).
% 0.20/0.53  % SZS output end Proof for theBenchmark
% 0.20/0.53  % (3306)------------------------------
% 0.20/0.53  % (3306)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.53  % (3306)Termination reason: Refutation
% 0.20/0.53  
% 0.20/0.53  % (3306)Memory used [KB]: 11257
% 0.20/0.53  % (3306)Time elapsed: 0.099 s
% 0.20/0.53  % (3306)------------------------------
% 0.20/0.53  % (3306)------------------------------
% 0.20/0.53  % (3296)Success in time 0.171 s
%------------------------------------------------------------------------------
