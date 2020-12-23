%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1737+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:27 EST 2020

% Result     : Theorem 2.53s
% Output     : Refutation 2.53s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 594 expanded)
%              Number of leaves         :   66 ( 312 expanded)
%              Depth                    :    9
%              Number of atoms          : 1441 (4377 expanded)
%              Number of equality atoms :   40 (  60 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5557,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f104,f108,f112,f116,f120,f124,f128,f132,f136,f140,f144,f148,f156,f185,f199,f219,f340,f356,f358,f399,f483,f516,f569,f584,f599,f1035,f1125,f1276,f1468,f2138,f2162,f2226,f2385,f2423,f2425,f5393,f5399,f5412,f5425,f5427,f5463,f5522,f5529,f5549,f5554,f5555,f5556])).

fof(f5556,plain,
    ( k1_tsep_1(sK0,sK2,sK1) != k1_tsep_1(sK0,sK1,sK2)
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5555,plain,
    ( k1_tsep_1(sK0,sK2,sK1) != k1_tsep_1(sK0,sK1,sK2)
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5554,plain,
    ( ~ spl4_388
    | ~ spl4_382
    | spl4_391 ),
    inference(avatar_split_clause,[],[f5552,f2419,f2383,f2410])).

fof(f2410,plain,
    ( spl4_388
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_388])])).

fof(f2383,plain,
    ( spl4_382
  <=> m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_382])])).

fof(f2419,plain,
    ( spl4_391
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_391])])).

fof(f5552,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_382
    | spl4_391 ),
    inference(resolution,[],[f5550,f2384])).

fof(f2384,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_382 ),
    inference(avatar_component_clause,[],[f2383])).

fof(f5550,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
        | ~ l1_pre_topc(X0) )
    | spl4_391 ),
    inference(resolution,[],[f2420,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f2420,plain,
    ( ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_391 ),
    inference(avatar_component_clause,[],[f2419])).

fof(f5549,plain,
    ( ~ spl4_387
    | ~ spl4_388
    | ~ spl4_382
    | spl4_390 ),
    inference(avatar_split_clause,[],[f5547,f2416,f2383,f2410,f2407])).

fof(f2407,plain,
    ( spl4_387
  <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_387])])).

fof(f2416,plain,
    ( spl4_390
  <=> v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_390])])).

fof(f5547,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_382
    | spl4_390 ),
    inference(resolution,[],[f5523,f2384])).

fof(f5523,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl4_390 ),
    inference(resolution,[],[f2417,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( v2_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f2417,plain,
    ( ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | spl4_390 ),
    inference(avatar_component_clause,[],[f2416])).

fof(f5529,plain,
    ( ~ spl4_15
    | ~ spl4_49
    | ~ spl4_14
    | spl4_387 ),
    inference(avatar_split_clause,[],[f5527,f2407,f138,f349,f142])).

fof(f142,plain,
    ( spl4_15
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f349,plain,
    ( spl4_49
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f138,plain,
    ( spl4_14
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f5527,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_14
    | spl4_387 ),
    inference(resolution,[],[f5465,f139])).

fof(f139,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f5465,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0)
        | ~ v2_pre_topc(X0) )
    | spl4_387 ),
    inference(resolution,[],[f2408,f75])).

fof(f2408,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_387 ),
    inference(avatar_component_clause,[],[f2407])).

fof(f5522,plain,
    ( ~ spl4_15
    | ~ spl4_12
    | ~ spl4_14
    | spl4_389 ),
    inference(avatar_split_clause,[],[f5520,f2413,f138,f130,f142])).

fof(f130,plain,
    ( spl4_12
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f2413,plain,
    ( spl4_389
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_389])])).

fof(f5520,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_14
    | spl4_389 ),
    inference(resolution,[],[f5519,f139])).

fof(f5519,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ v2_pre_topc(X0) )
    | spl4_389 ),
    inference(resolution,[],[f2414,f75])).

fof(f2414,plain,
    ( ~ v2_pre_topc(sK1)
    | spl4_389 ),
    inference(avatar_component_clause,[],[f2413])).

fof(f5463,plain,
    ( ~ spl4_49
    | ~ spl4_14
    | spl4_388 ),
    inference(avatar_split_clause,[],[f5461,f2410,f138,f349])).

fof(f5461,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl4_14
    | spl4_388 ),
    inference(resolution,[],[f5428,f139])).

fof(f5428,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),X0) )
    | spl4_388 ),
    inference(resolution,[],[f2411,f61])).

fof(f2411,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_388 ),
    inference(avatar_component_clause,[],[f2410])).

fof(f5427,plain,
    ( ~ spl4_388
    | spl4_366 ),
    inference(avatar_split_clause,[],[f5426,f2288,f2410])).

fof(f2288,plain,
    ( spl4_366
  <=> l1_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_366])])).

fof(f5426,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl4_366 ),
    inference(resolution,[],[f2289,f60])).

fof(f60,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f2289,plain,
    ( ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | spl4_366 ),
    inference(avatar_component_clause,[],[f2288])).

fof(f5425,plain,
    ( ~ spl4_198
    | ~ spl4_366
    | ~ spl4_352
    | spl4_386 ),
    inference(avatar_split_clause,[],[f5417,f2399,f2221,f2288,f1269])).

fof(f1269,plain,
    ( spl4_198
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_198])])).

fof(f2221,plain,
    ( spl4_352
  <=> r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_352])])).

fof(f2399,plain,
    ( spl4_386
  <=> r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_386])])).

fof(f5417,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_struct_0(sK3)
    | spl4_386 ),
    inference(resolution,[],[f2400,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f2400,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | spl4_386 ),
    inference(avatar_component_clause,[],[f2399])).

fof(f5412,plain,
    ( spl4_11
    | ~ spl4_386
    | ~ spl4_10
    | ~ spl4_862 ),
    inference(avatar_split_clause,[],[f5402,f5397,f122,f2399,f126])).

fof(f126,plain,
    ( spl4_11
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f122,plain,
    ( spl4_10
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f5397,plain,
    ( spl4_862
  <=> ! [X0] :
        ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,X0),sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_862])])).

fof(f5402,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK0,sK1,sK2),sK3)
    | v2_struct_0(sK2)
    | ~ spl4_10
    | ~ spl4_862 ),
    inference(resolution,[],[f5398,f123])).

fof(f123,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f122])).

fof(f5398,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,X0),sK3)
        | v2_struct_0(X0) )
    | ~ spl4_862 ),
    inference(avatar_component_clause,[],[f5397])).

fof(f5399,plain,
    ( spl4_13
    | ~ spl4_15
    | ~ spl4_14
    | ~ spl4_12
    | spl4_862
    | spl4_16
    | ~ spl4_861 ),
    inference(avatar_split_clause,[],[f5395,f5391,f146,f5397,f130,f138,f142,f134])).

fof(f134,plain,
    ( spl4_13
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f146,plain,
    ( spl4_16
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f5391,plain,
    ( spl4_861
  <=> ! [X1,X0] :
        ( v2_struct_0(X0)
        | ~ m1_pre_topc(k1_tsep_1(X0,sK1,X1),sK0)
        | ~ r1_tsep_1(k1_tsep_1(X0,sK1,X1),sK3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_861])])).

fof(f5395,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,X0),sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK1) )
    | ~ spl4_861 ),
    inference(duplicate_literal_removal,[],[f5394])).

fof(f5394,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | ~ r1_tsep_1(k1_tsep_1(sK0,sK1,X0),sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_861 ),
    inference(resolution,[],[f5392,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f5392,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(k1_tsep_1(X0,sK1,X1),sK0)
        | v2_struct_0(X0)
        | ~ r1_tsep_1(k1_tsep_1(X0,sK1,X1),sK3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl4_861 ),
    inference(avatar_component_clause,[],[f5391])).

fof(f5393,plain,
    ( spl4_13
    | spl4_861
    | ~ spl4_90 ),
    inference(avatar_split_clause,[],[f5389,f597,f5391,f134])).

fof(f597,plain,
    ( spl4_90
  <=> ! [X1,X0] :
        ( v2_struct_0(k1_tsep_1(X0,sK1,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ r1_tsep_1(k1_tsep_1(X0,sK1,X1),sK3)
        | ~ m1_pre_topc(k1_tsep_1(X0,sK1,X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f5389,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ r1_tsep_1(k1_tsep_1(X0,sK1,X1),sK3)
        | ~ m1_pre_topc(k1_tsep_1(X0,sK1,X1),sK0)
        | v2_struct_0(sK1) )
    | ~ spl4_90 ),
    inference(duplicate_literal_removal,[],[f5388])).

fof(f5388,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ r1_tsep_1(k1_tsep_1(X0,sK1,X1),sK3)
        | ~ m1_pre_topc(k1_tsep_1(X0,sK1,X1),sK0)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_90 ),
    inference(resolution,[],[f598,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f598,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(X0,sK1,X1))
        | v2_struct_0(X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X0)
        | ~ r1_tsep_1(k1_tsep_1(X0,sK1,X1),sK3)
        | ~ m1_pre_topc(k1_tsep_1(X0,sK1,X1),sK0) )
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f597])).

fof(f2425,plain,
    ( ~ spl4_387
    | ~ spl4_388
    | ~ spl4_389
    | ~ spl4_168
    | ~ spl4_390
    | ~ spl4_391
    | spl4_2
    | ~ spl4_382
    | ~ spl4_353 ),
    inference(avatar_split_clause,[],[f2405,f2224,f2383,f92,f2419,f2416,f1106,f2413,f2410,f2407])).

fof(f1106,plain,
    ( spl4_168
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_168])])).

fof(f92,plain,
    ( spl4_2
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f2224,plain,
    ( spl4_353
  <=> v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_353])])).

fof(f2405,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_353 ),
    inference(resolution,[],[f2225,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                  | ~ m1_pre_topc(X2,X0)
                  | ~ v1_tsep_1(X2,X0) )
                & ( ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) )
                  | ~ m1_pre_topc(X1,X0)
                  | ~ v1_tsep_1(X1,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_tsep_1(X1,X0) )
              <=> ( m1_pre_topc(X2,X0)
                  & v1_tsep_1(X2,X0) ) )
              | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
              | ~ l1_pre_topc(X2)
              | ~ v2_pre_topc(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( l1_pre_topc(X2)
                & v2_pre_topc(X2) )
             => ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_tsep_1(X1,X0) )
                <=> ( m1_pre_topc(X2,X0)
                    & v1_tsep_1(X2,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_tmap_1)).

fof(f2225,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_353 ),
    inference(avatar_component_clause,[],[f2224])).

fof(f2423,plain,
    ( ~ spl4_387
    | ~ spl4_388
    | ~ spl4_389
    | ~ spl4_168
    | ~ spl4_390
    | ~ spl4_391
    | spl4_1
    | ~ spl4_382
    | ~ spl4_353 ),
    inference(avatar_split_clause,[],[f2404,f2224,f2383,f89,f2419,f2416,f1106,f2413,f2410,f2407])).

fof(f89,plain,
    ( spl4_1
  <=> v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f2404,plain,
    ( ~ m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_353 ),
    inference(resolution,[],[f2225,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | ~ m1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)),X0)
      | v1_tsep_1(X1,X0)
      | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ v2_pre_topc(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f78])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != X2
      | ~ l1_pre_topc(X2)
      | ~ v2_pre_topc(X2)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f2385,plain,
    ( spl4_48
    | ~ spl4_49
    | spl4_382
    | ~ spl4_70
    | ~ spl4_344
    | spl4_352 ),
    inference(avatar_split_clause,[],[f2381,f2221,f2159,f481,f2383,f349,f346])).

fof(f346,plain,
    ( spl4_48
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_48])])).

fof(f481,plain,
    ( spl4_70
  <=> ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0)
        | r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_70])])).

fof(f2159,plain,
    ( spl4_344
  <=> g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_344])])).

fof(f2381,plain,
    ( m1_pre_topc(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_70
    | ~ spl4_344
    | spl4_352 ),
    inference(forward_demodulation,[],[f2376,f2160])).

fof(f2160,plain,
    ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_344 ),
    inference(avatar_component_clause,[],[f2159])).

fof(f2376,plain,
    ( m1_pre_topc(k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2)),k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_70
    | spl4_352 ),
    inference(resolution,[],[f2355,f482])).

fof(f482,plain,
    ( ! [X0] :
        ( r1_tsep_1(sK3,X0)
        | m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_70 ),
    inference(avatar_component_clause,[],[f481])).

fof(f2355,plain,
    ( ~ r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | spl4_352 ),
    inference(avatar_component_clause,[],[f2221])).

fof(f2226,plain,
    ( spl4_16
    | ~ spl4_15
    | ~ spl4_14
    | spl4_48
    | ~ spl4_49
    | spl4_9
    | ~ spl4_8
    | ~ spl4_7
    | spl4_352
    | spl4_353
    | ~ spl4_344 ),
    inference(avatar_split_clause,[],[f2219,f2159,f2224,f2221,f110,f114,f118,f349,f346,f138,f142,f146])).

fof(f118,plain,
    ( spl4_9
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f114,plain,
    ( spl4_8
  <=> v1_tsep_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f110,plain,
    ( spl4_7
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f2219,plain,
    ( v1_tsep_1(g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)),k1_tsep_1(sK0,sK1,sK2))
    | r1_tsep_1(sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_pre_topc(sK3,sK0)
    | ~ v1_tsep_1(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_344 ),
    inference(superposition,[],[f62,f2160])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_tsep_1(k2_tsep_1(X0,X2,X1),X1)
      | r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) )
              | r1_tsep_1(X2,X1)
              | ~ m1_pre_topc(X2,X0)
              | ~ v1_tsep_1(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & v1_tsep_1(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X2,X1)
               => ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
                  & v1_tsep_1(k2_tsep_1(X0,X2,X1),X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tmap_1)).

fof(f2162,plain,
    ( spl4_344
    | spl4_11
    | ~ spl4_5
    | ~ spl4_10
    | ~ spl4_339 ),
    inference(avatar_split_clause,[],[f2145,f2136,f122,f102,f126,f2159])).

fof(f102,plain,
    ( spl4_5
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f2136,plain,
    ( spl4_339
  <=> ! [X0] :
        ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,X0))
        | ~ r1_tsep_1(sK3,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_339])])).

fof(f2145,plain,
    ( ~ r1_tsep_1(sK3,sK2)
    | v2_struct_0(sK2)
    | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_10
    | ~ spl4_339 ),
    inference(resolution,[],[f2137,f123])).

fof(f2137,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ r1_tsep_1(sK3,X0)
        | v2_struct_0(X0)
        | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,X0)) )
    | ~ spl4_339 ),
    inference(avatar_component_clause,[],[f2136])).

fof(f2138,plain,
    ( spl4_9
    | ~ spl4_7
    | spl4_339
    | ~ spl4_6
    | ~ spl4_229 ),
    inference(avatar_split_clause,[],[f2132,f1466,f106,f2136,f110,f118])).

fof(f106,plain,
    ( spl4_6
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f1466,plain,
    ( spl4_229
  <=> ! [X5,X4] :
        ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,X4,k1_tsep_1(sK0,sK1,X5))
        | ~ m1_pre_topc(sK1,X4)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | ~ r1_tsep_1(X4,X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_229])])).

fof(f2132,plain,
    ( ! [X0] :
        ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,sK3,k1_tsep_1(sK0,sK1,X0))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ r1_tsep_1(sK3,X0) )
    | ~ spl4_6
    | ~ spl4_229 ),
    inference(resolution,[],[f1467,f107])).

fof(f107,plain,
    ( m1_pre_topc(sK1,sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1467,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(sK1,X4)
        | g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,X4,k1_tsep_1(sK0,sK1,X5))
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4)
        | ~ r1_tsep_1(X4,X5) )
    | ~ spl4_229 ),
    inference(avatar_component_clause,[],[f1466])).

fof(f1468,plain,
    ( spl4_13
    | spl4_229
    | ~ spl4_12
    | ~ spl4_157 ),
    inference(avatar_split_clause,[],[f1458,f1033,f130,f1466,f134])).

fof(f1033,plain,
    ( spl4_157
  <=> ! [X1,X0,X2] :
        ( ~ r1_tsep_1(X0,X1)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(sK0,X0,k1_tsep_1(sK0,X2,X1))
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_157])])).

fof(f1458,plain,
    ( ! [X4,X5] :
        ( g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) = k2_tsep_1(sK0,X4,k1_tsep_1(sK0,sK1,X5))
        | v2_struct_0(sK1)
        | ~ r1_tsep_1(X4,X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(sK1,X4) )
    | ~ spl4_12
    | ~ spl4_157 ),
    inference(resolution,[],[f1034,f131])).

fof(f131,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1034,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_pre_topc(X2,sK0)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(sK0,X0,k1_tsep_1(sK0,X2,X1))
        | v2_struct_0(X2)
        | ~ r1_tsep_1(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,X0) )
    | ~ spl4_157 ),
    inference(avatar_component_clause,[],[f1033])).

fof(f1276,plain,
    ( ~ spl4_74
    | spl4_198 ),
    inference(avatar_split_clause,[],[f1275,f1269,f503])).

fof(f503,plain,
    ( spl4_74
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_74])])).

fof(f1275,plain,
    ( ~ l1_pre_topc(sK3)
    | spl4_198 ),
    inference(resolution,[],[f1270,f60])).

fof(f1270,plain,
    ( ~ l1_struct_0(sK3)
    | spl4_198 ),
    inference(avatar_component_clause,[],[f1269])).

fof(f1125,plain,
    ( ~ spl4_12
    | ~ spl4_14
    | spl4_168 ),
    inference(avatar_split_clause,[],[f1123,f1106,f138,f130])).

fof(f1123,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ spl4_14
    | spl4_168 ),
    inference(resolution,[],[f1122,f139])).

fof(f1122,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | spl4_168 ),
    inference(resolution,[],[f1107,f61])).

fof(f1107,plain,
    ( ~ l1_pre_topc(sK1)
    | spl4_168 ),
    inference(avatar_component_clause,[],[f1106])).

fof(f1035,plain,
    ( spl4_16
    | ~ spl4_15
    | spl4_157
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f1030,f138,f1033,f142,f146])).

fof(f1030,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) = k2_tsep_1(sK0,X0,k1_tsep_1(sK0,X2,X1))
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f67,f139])).

fof(f67,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3))
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                    & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X3,X1))
                        & g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k2_tsep_1(X0,X2,k1_tsep_1(X0,X1,X3)) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tmap_1)).

fof(f599,plain,
    ( spl4_13
    | spl4_90
    | ~ spl4_87 ),
    inference(avatar_split_clause,[],[f591,f582,f597,f134])).

fof(f582,plain,
    ( spl4_87
  <=> ! [X0] :
        ( ~ r1_tsep_1(X0,sK3)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_87])])).

fof(f591,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(k1_tsep_1(X0,sK1,X1))
        | ~ m1_pre_topc(k1_tsep_1(X0,sK1,X1),sK0)
        | ~ r1_tsep_1(k1_tsep_1(X0,sK1,X1),sK3)
        | ~ m1_pre_topc(X1,X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(sK1)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl4_87 ),
    inference(resolution,[],[f583,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f583,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ r1_tsep_1(X0,sK3) )
    | ~ spl4_87 ),
    inference(avatar_component_clause,[],[f582])).

fof(f584,plain,
    ( spl4_9
    | ~ spl4_7
    | spl4_87
    | ~ spl4_6
    | ~ spl4_84 ),
    inference(avatar_split_clause,[],[f578,f567,f106,f582,f110,f118])).

fof(f567,plain,
    ( spl4_84
  <=> ! [X5,X4] :
        ( ~ r1_tsep_1(X4,X5)
        | ~ m1_pre_topc(sK1,X5)
        | ~ m1_pre_topc(sK1,X4)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_84])])).

fof(f578,plain,
    ( ! [X0] :
        ( ~ r1_tsep_1(X0,sK3)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(sK3,sK0)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl4_6
    | ~ spl4_84 ),
    inference(resolution,[],[f568,f107])).

fof(f568,plain,
    ( ! [X4,X5] :
        ( ~ m1_pre_topc(sK1,X5)
        | ~ r1_tsep_1(X4,X5)
        | ~ m1_pre_topc(sK1,X4)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X4) )
    | ~ spl4_84 ),
    inference(avatar_component_clause,[],[f567])).

fof(f569,plain,
    ( spl4_84
    | spl4_13
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_57 ),
    inference(avatar_split_clause,[],[f559,f397,f154,f130,f134,f567])).

fof(f154,plain,
    ( spl4_17
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ r1_tsep_1(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f397,plain,
    ( spl4_57
  <=> ! [X1,X0,X2] :
        ( r1_tsep_1(X0,X1)
        | ~ r1_tsep_1(X2,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f559,plain,
    ( ! [X4,X5] :
        ( v2_struct_0(sK1)
        | ~ r1_tsep_1(X4,X5)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | ~ m1_pre_topc(sK1,X4)
        | ~ m1_pre_topc(sK1,X5) )
    | ~ spl4_12
    | ~ spl4_17
    | ~ spl4_57 ),
    inference(resolution,[],[f548,f131])).

fof(f548,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | ~ r1_tsep_1(X3,X4)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X5,X3)
        | ~ m1_pre_topc(X5,X4) )
    | ~ spl4_17
    | ~ spl4_57 ),
    inference(duplicate_literal_removal,[],[f547])).

fof(f547,plain,
    ( ! [X4,X5,X3] :
        ( ~ r1_tsep_1(X3,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X5,X3)
        | ~ m1_pre_topc(X5,X4)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0) )
    | ~ spl4_17
    | ~ spl4_57 ),
    inference(resolution,[],[f398,f155])).

fof(f155,plain,
    ( ! [X0,X1] :
        ( ~ r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl4_17 ),
    inference(avatar_component_clause,[],[f154])).

fof(f398,plain,
    ( ! [X2,X0,X1] :
        ( r1_tsep_1(X0,X1)
        | ~ r1_tsep_1(X2,X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,X2) )
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f397])).

fof(f516,plain,
    ( ~ spl4_7
    | ~ spl4_14
    | spl4_74 ),
    inference(avatar_split_clause,[],[f514,f503,f138,f110])).

fof(f514,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ spl4_14
    | spl4_74 ),
    inference(resolution,[],[f513,f139])).

fof(f513,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0) )
    | spl4_74 ),
    inference(resolution,[],[f504,f61])).

fof(f504,plain,
    ( ~ l1_pre_topc(sK3)
    | spl4_74 ),
    inference(avatar_component_clause,[],[f503])).

fof(f483,plain,
    ( ~ spl4_7
    | spl4_9
    | spl4_70
    | ~ spl4_8
    | ~ spl4_47 ),
    inference(avatar_split_clause,[],[f478,f338,f114,f481,f118,f110])).

fof(f338,plain,
    ( spl4_47
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,X1)
        | m1_pre_topc(k2_tsep_1(sK0,X0,X1),X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ v1_tsep_1(X0,sK0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_47])])).

fof(f478,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK3,X0),X0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK3)
        | r1_tsep_1(sK3,X0)
        | ~ m1_pre_topc(sK3,sK0) )
    | ~ spl4_8
    | ~ spl4_47 ),
    inference(resolution,[],[f339,f115])).

fof(f115,plain,
    ( v1_tsep_1(sK3,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f339,plain,
    ( ! [X0,X1] :
        ( ~ v1_tsep_1(X0,sK0)
        | m1_pre_topc(k2_tsep_1(sK0,X0,X1),X1)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0) )
    | ~ spl4_47 ),
    inference(avatar_component_clause,[],[f338])).

fof(f399,plain,
    ( spl4_16
    | ~ spl4_15
    | spl4_57
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f394,f138,f397,f142,f146])).

fof(f394,plain,
    ( ! [X2,X0,X1] :
        ( r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ r1_tsep_1(X2,X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f71,f139])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X2,X3)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) )
                      | ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tmap_1)).

fof(f358,plain,
    ( spl4_16
    | ~ spl4_14
    | spl4_13
    | ~ spl4_12
    | spl4_11
    | ~ spl4_10
    | ~ spl4_48 ),
    inference(avatar_split_clause,[],[f357,f346,f122,f126,f130,f134,f138,f146])).

fof(f357,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl4_48 ),
    inference(resolution,[],[f347,f82])).

fof(f347,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl4_48 ),
    inference(avatar_component_clause,[],[f346])).

fof(f356,plain,
    ( spl4_16
    | ~ spl4_14
    | spl4_13
    | ~ spl4_12
    | spl4_11
    | ~ spl4_10
    | spl4_49 ),
    inference(avatar_split_clause,[],[f355,f349,f122,f126,f130,f134,f138,f146])).

fof(f355,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl4_49 ),
    inference(resolution,[],[f350,f83])).

fof(f350,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl4_49 ),
    inference(avatar_component_clause,[],[f349])).

fof(f340,plain,
    ( spl4_16
    | ~ spl4_15
    | spl4_47
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f335,f138,f338,f142,f146])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X0,sK0)
        | ~ v1_tsep_1(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | m1_pre_topc(k2_tsep_1(sK0,X0,X1),X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f63,f139])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tsep_1(X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | ~ v1_tsep_1(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | m1_pre_topc(k2_tsep_1(X0,X2,X1),X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f219,plain,
    ( spl4_27
    | spl4_11
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(avatar_split_clause,[],[f210,f197,f122,f126,f217])).

fof(f217,plain,
    ( spl4_27
  <=> k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f197,plain,
    ( spl4_23
  <=> ! [X3] :
        ( k1_tsep_1(sK0,X3,sK1) = k1_tsep_1(sK0,sK1,X3)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f210,plain,
    ( v2_struct_0(sK2)
    | k1_tsep_1(sK0,sK2,sK1) = k1_tsep_1(sK0,sK1,sK2)
    | ~ spl4_10
    | ~ spl4_23 ),
    inference(resolution,[],[f198,f123])).

fof(f198,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | k1_tsep_1(sK0,X3,sK1) = k1_tsep_1(sK0,sK1,X3) )
    | ~ spl4_23 ),
    inference(avatar_component_clause,[],[f197])).

fof(f199,plain,
    ( spl4_13
    | spl4_23
    | ~ spl4_12
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f187,f183,f130,f197,f134])).

fof(f183,plain,
    ( spl4_21
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X1,X0) = k1_tsep_1(sK0,X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f187,plain,
    ( ! [X3] :
        ( k1_tsep_1(sK0,X3,sK1) = k1_tsep_1(sK0,sK1,X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | v2_struct_0(sK1) )
    | ~ spl4_12
    | ~ spl4_21 ),
    inference(resolution,[],[f184,f131])).

fof(f184,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | k1_tsep_1(sK0,X1,X0) = k1_tsep_1(sK0,X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) )
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f183])).

fof(f185,plain,
    ( spl4_16
    | spl4_21
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f180,f138,f183,f146])).

fof(f180,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k1_tsep_1(sK0,X1,X0) = k1_tsep_1(sK0,X0,X1)
        | v2_struct_0(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f81,f139])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => k1_tsep_1(X0,X1,X2) = k1_tsep_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k1_tsep_1)).

fof(f156,plain,
    ( spl4_16
    | ~ spl4_15
    | spl4_17
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f149,f138,f154,f142,f146])).

fof(f149,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ r1_tsep_1(X0,X1)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl4_14 ),
    inference(resolution,[],[f65,f139])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ r1_tsep_1(X1,X2)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f148,plain,(
    ~ spl4_16 ),
    inference(avatar_split_clause,[],[f47,f146])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
      | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
      | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
      | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
    & r1_tsep_1(sK3,sK2)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK3,sK0)
    & v1_tsep_1(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f17,f43,f42,f41,f40])).

fof(f40,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                      | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                    & r1_tsep_1(X3,X2)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X3,X0)
                    & v1_tsep_1(X3,X0)
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
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(sK0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(sK0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,sK0)
                  & v1_tsep_1(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ m1_pre_topc(X1,k1_tsep_1(sK0,X2,X1))
                  | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X2,X1))
                  | ~ m1_pre_topc(X1,k1_tsep_1(sK0,X1,X2))
                  | ~ v1_tsep_1(X1,k1_tsep_1(sK0,X1,X2)) )
                & r1_tsep_1(X3,X2)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK0)
                & v1_tsep_1(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,X2,sK1))
                | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,X2,sK1))
                | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,X2))
                | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,X2)) )
              & r1_tsep_1(X3,X2)
              & m1_pre_topc(sK1,X3)
              & m1_pre_topc(X3,sK0)
              & v1_tsep_1(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,X2,sK1))
              | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,X2,sK1))
              | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,X2))
              | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,X2)) )
            & r1_tsep_1(X3,X2)
            & m1_pre_topc(sK1,X3)
            & m1_pre_topc(X3,sK0)
            & v1_tsep_1(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
            | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
            | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
            | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
          & r1_tsep_1(X3,sK2)
          & m1_pre_topc(sK1,X3)
          & m1_pre_topc(X3,sK0)
          & v1_tsep_1(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X3] :
        ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
          | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
          | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
          | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
        & r1_tsep_1(X3,sK2)
        & m1_pre_topc(sK1,X3)
        & m1_pre_topc(X3,sK0)
        & v1_tsep_1(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
        | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
        | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
        | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) )
      & r1_tsep_1(sK3,sK2)
      & m1_pre_topc(sK1,sK3)
      & m1_pre_topc(sK3,sK0)
      & v1_tsep_1(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                    | ~ m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                    | ~ v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) )
                  & r1_tsep_1(X3,X2)
                  & m1_pre_topc(X1,X3)
                  & m1_pre_topc(X3,X0)
                  & v1_tsep_1(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
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
                      & v1_tsep_1(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ( r1_tsep_1(X3,X2)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                        & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                        & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                        & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
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
                    & v1_tsep_1(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ( r1_tsep_1(X3,X2)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(X1,k1_tsep_1(X0,X2,X1))
                      & v1_tsep_1(X1,k1_tsep_1(X0,X2,X1))
                      & m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
                      & v1_tsep_1(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tmap_1)).

fof(f144,plain,(
    spl4_15 ),
    inference(avatar_split_clause,[],[f48,f142])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f140,plain,(
    spl4_14 ),
    inference(avatar_split_clause,[],[f49,f138])).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f136,plain,(
    ~ spl4_13 ),
    inference(avatar_split_clause,[],[f50,f134])).

fof(f50,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f132,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f51,f130])).

fof(f51,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f128,plain,(
    ~ spl4_11 ),
    inference(avatar_split_clause,[],[f52,f126])).

fof(f52,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f124,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f53,f122])).

fof(f53,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f120,plain,(
    ~ spl4_9 ),
    inference(avatar_split_clause,[],[f54,f118])).

fof(f54,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f116,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f55,f114])).

fof(f55,plain,(
    v1_tsep_1(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f112,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f56,f110])).

fof(f56,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f108,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f57,f106])).

fof(f57,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f104,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f58,f102])).

fof(f58,plain,(
    r1_tsep_1(sK3,sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f59,f98,f95,f92,f89])).

fof(f95,plain,
    ( spl4_3
  <=> v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f98,plain,
    ( spl4_4
  <=> m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f59,plain,
    ( ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK2,sK1))
    | ~ m1_pre_topc(sK1,k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_tsep_1(sK1,k1_tsep_1(sK0,sK1,sK2)) ),
    inference(cnf_transformation,[],[f44])).

%------------------------------------------------------------------------------
