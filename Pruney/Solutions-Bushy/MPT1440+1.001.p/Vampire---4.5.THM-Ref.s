%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1440+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:55 EST 2020

% Result     : Theorem 3.97s
% Output     : Refutation 4.15s
% Verified   : 
% Statistics : Number of formulae       :  416 (1055 expanded)
%              Number of leaves         :   92 ( 524 expanded)
%              Depth                    :   19
%              Number of atoms          : 2111 (5104 expanded)
%              Number of equality atoms :  128 ( 258 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3458,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f154,f158,f162,f164,f166,f168,f170,f242,f244,f254,f269,f300,f304,f311,f315,f319,f323,f327,f331,f344,f346,f348,f350,f355,f357,f359,f363,f368,f370,f375,f377,f894,f2559,f2609,f2666,f2668,f2703,f2710,f2730,f2732,f2784,f2904,f2908,f2938,f2940,f2964,f2985,f3062,f3091,f3096,f3104,f3107,f3113,f3116,f3147,f3149,f3164,f3166,f3168,f3183,f3185,f3197,f3205,f3211,f3243,f3276,f3358,f3399,f3453])).

fof(f3453,plain,
    ( ~ spl2_371
    | ~ spl2_372
    | ~ spl2_375
    | ~ spl2_418
    | ~ spl2_383
    | ~ spl2_417 ),
    inference(avatar_split_clause,[],[f3452,f3274,f3060,f3356,f2930,f2921,f2918])).

fof(f2918,plain,
    ( spl2_371
  <=> l1_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_371])])).

fof(f2921,plain,
    ( spl2_372
  <=> v1_funct_1(u1_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_372])])).

fof(f2930,plain,
    ( spl2_375
  <=> v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_375])])).

fof(f3356,plain,
    ( spl2_418
  <=> r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_418])])).

fof(f3060,plain,
    ( spl2_383
  <=> u1_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_383])])).

fof(f3274,plain,
    ( spl2_417
  <=> ! [X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_417])])).

fof(f3452,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ l1_lattices(sK1)
    | ~ spl2_383
    | ~ spl2_417 ),
    inference(forward_demodulation,[],[f3450,f3061])).

fof(f3061,plain,
    ( u1_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))
    | ~ spl2_383 ),
    inference(avatar_component_clause,[],[f3060])).

fof(f3450,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ l1_lattices(sK1)
    | ~ spl2_417 ),
    inference(resolution,[],[f3275,f94])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_lattices(X0)
     => ( m1_subset_1(u1_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_lattices)).

fof(f3275,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X5))
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(X5) )
    | ~ spl2_417 ),
    inference(avatar_component_clause,[],[f3274])).

fof(f3399,plain,
    ( spl2_9
    | ~ spl2_8
    | ~ spl2_7
    | spl2_418 ),
    inference(avatar_split_clause,[],[f3369,f3356,f152,f156,f160])).

fof(f160,plain,
    ( spl2_9
  <=> v2_struct_0(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f156,plain,
    ( spl2_8
  <=> v10_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f152,plain,
    ( spl2_7
  <=> l3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f3369,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | spl2_418 ),
    inference(resolution,[],[f3357,f120])).

fof(f120,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_lattice2)).

fof(f3357,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | spl2_418 ),
    inference(avatar_component_clause,[],[f3356])).

fof(f3358,plain,
    ( ~ spl2_365
    | ~ spl2_366
    | ~ spl2_369
    | ~ spl2_418
    | ~ spl2_383
    | ~ spl2_411 ),
    inference(avatar_split_clause,[],[f3354,f3241,f3060,f3356,f2896,f2887,f2884])).

fof(f2884,plain,
    ( spl2_365
  <=> l1_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_365])])).

fof(f2887,plain,
    ( spl2_366
  <=> v1_funct_1(u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_366])])).

fof(f2896,plain,
    ( spl2_369
  <=> v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_369])])).

fof(f3241,plain,
    ( spl2_411
  <=> ! [X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X5,u1_lattices(sK1)))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_411])])).

fof(f3354,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ l1_lattices(sK0)
    | ~ spl2_383
    | ~ spl2_411 ),
    inference(forward_demodulation,[],[f3352,f3061])).

fof(f3352,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ l1_lattices(sK0)
    | ~ spl2_411 ),
    inference(resolution,[],[f3242,f94])).

fof(f3242,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X5,u1_lattices(sK1)))
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X5) )
    | ~ spl2_411 ),
    inference(avatar_component_clause,[],[f3241])).

fof(f3276,plain,
    ( ~ spl2_386
    | ~ spl2_369
    | ~ spl2_366
    | spl2_417
    | ~ spl2_32
    | ~ spl2_232
    | spl2_405 ),
    inference(avatar_split_clause,[],[f3272,f3208,f1927,f317,f3274,f2887,f2896,f3086])).

fof(f3086,plain,
    ( spl2_386
  <=> m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_386])])).

fof(f317,plain,
    ( spl2_32
  <=> ! [X1,X0] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f1927,plain,
    ( spl2_232
  <=> u1_struct_0(k7_filter_1(sK0,sK1)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_232])])).

fof(f3208,plain,
    ( spl2_405
  <=> r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_405])])).

fof(f3272,plain,
    ( ! [X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X5))
        | ~ v1_funct_1(u1_lattices(sK0))
        | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)))) )
    | ~ spl2_32
    | ~ spl2_232
    | spl2_405 ),
    inference(forward_demodulation,[],[f3250,f1928])).

fof(f1928,plain,
    ( u1_struct_0(k7_filter_1(sK0,sK1)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl2_232 ),
    inference(avatar_component_clause,[],[f1927])).

fof(f3250,plain,
    ( ! [X5] :
        ( ~ v1_funct_1(u1_lattices(sK0))
        | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),X5)) )
    | ~ spl2_32
    | spl2_405 ),
    inference(resolution,[],[f3209,f318])).

fof(f318,plain,
    ( ! [X0,X1] :
        ( r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0)
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1)) )
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f317])).

fof(f3209,plain,
    ( ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | spl2_405 ),
    inference(avatar_component_clause,[],[f3208])).

fof(f3243,plain,
    ( ~ spl2_385
    | ~ spl2_375
    | ~ spl2_372
    | spl2_411
    | ~ spl2_34
    | ~ spl2_232
    | spl2_404 ),
    inference(avatar_split_clause,[],[f3239,f3202,f1927,f325,f3241,f2921,f2930,f3083])).

fof(f3083,plain,
    ( spl2_385
  <=> m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_385])])).

fof(f325,plain,
    ( spl2_34
  <=> ! [X5,X4] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5))
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_34])])).

fof(f3202,plain,
    ( spl2_404
  <=> r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),u1_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_404])])).

fof(f3239,plain,
    ( ! [X5] :
        ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X5,u1_lattices(sK1)))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(u1_lattices(sK1))
        | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)))) )
    | ~ spl2_34
    | ~ spl2_232
    | spl2_404 ),
    inference(forward_demodulation,[],[f3217,f1928])).

fof(f3217,plain,
    ( ! [X5] :
        ( ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(u1_lattices(sK1))
        | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X5,u1_lattices(sK1))) )
    | ~ spl2_34
    | spl2_404 ),
    inference(resolution,[],[f3203,f326])).

fof(f326,plain,
    ( ! [X4,X5] :
        ( r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5)
        | ~ v1_funct_1(X4)
        | ~ v1_funct_2(X4,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X5)
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5)) )
    | ~ spl2_34 ),
    inference(avatar_component_clause,[],[f325])).

fof(f3203,plain,
    ( ~ r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),u1_lattices(sK1))
    | spl2_404 ),
    inference(avatar_component_clause,[],[f3202])).

fof(f3211,plain,
    ( spl2_1
    | ~ spl2_3
    | ~ spl2_26
    | ~ spl2_29
    | ~ spl2_368
    | ~ spl2_378
    | ~ spl2_405
    | spl2_2
    | ~ spl2_388 ),
    inference(avatar_split_clause,[],[f3206,f3094,f136,f3208,f2956,f2893,f306,f295,f139,f133])).

fof(f133,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f139,plain,
    ( spl2_3
  <=> l3_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f295,plain,
    ( spl2_26
  <=> v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f306,plain,
    ( spl2_29
  <=> v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_29])])).

fof(f2893,plain,
    ( spl2_368
  <=> v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_368])])).

fof(f2956,plain,
    ( spl2_378
  <=> v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_378])])).

fof(f136,plain,
    ( spl2_2
  <=> v10_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f3094,plain,
    ( spl2_388
  <=> r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_388])])).

fof(f3206,plain,
    ( v10_lattices(sK0)
    | ~ r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),u1_lattices(sK0))
    | ~ v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_388 ),
    inference(resolution,[],[f3095,f122])).

fof(f122,plain,(
    ! [X0] :
      ( ~ r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | v10_lattices(X0)
      | ~ r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0] :
      ( v10_lattices(X0)
      | ~ r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0] :
      ( v10_lattices(X0)
      | ~ r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
      | ~ v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( ( r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
          & r1_lattice2(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0))
          & v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
          & v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
          & v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
          & v1_binop_1(u2_lattices(X0),u1_struct_0(X0)) )
       => v10_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_lattice2)).

fof(f3095,plain,
    ( r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | ~ spl2_388 ),
    inference(avatar_component_clause,[],[f3094])).

fof(f3205,plain,
    ( spl2_4
    | ~ spl2_6
    | ~ spl2_28
    | ~ spl2_31
    | ~ spl2_374
    | ~ spl2_381
    | ~ spl2_404
    | spl2_5
    | ~ spl2_384 ),
    inference(avatar_split_clause,[],[f3200,f3080,f145,f3202,f2977,f2927,f313,f302,f148,f142])).

fof(f142,plain,
    ( spl2_4
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f148,plain,
    ( spl2_6
  <=> l3_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f302,plain,
    ( spl2_28
  <=> v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f313,plain,
    ( spl2_31
  <=> v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_31])])).

fof(f2927,plain,
    ( spl2_374
  <=> v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_374])])).

fof(f2977,plain,
    ( spl2_381
  <=> v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_381])])).

fof(f145,plain,
    ( spl2_5
  <=> v10_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f3080,plain,
    ( spl2_384
  <=> r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_384])])).

fof(f3200,plain,
    ( v10_lattices(sK1)
    | ~ r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),u1_lattices(sK1))
    | ~ v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ spl2_384 ),
    inference(resolution,[],[f3081,f122])).

fof(f3081,plain,
    ( r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl2_384 ),
    inference(avatar_component_clause,[],[f3080])).

fof(f3197,plain,
    ( spl2_9
    | ~ spl2_8
    | ~ spl2_7
    | spl2_387 ),
    inference(avatar_split_clause,[],[f3196,f3089,f152,f156,f160])).

fof(f3089,plain,
    ( spl2_387
  <=> r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_387])])).

fof(f3196,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | spl2_387 ),
    inference(resolution,[],[f3090,f121])).

fof(f121,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
    ! [X0] :
      ( r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0))
      | ~ l3_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & v10_lattices(X0)
        & ~ v2_struct_0(X0) )
     => r1_lattice2(u1_struct_0(X0),u1_lattices(X0),u2_lattices(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_lattice2)).

fof(f3090,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | spl2_387 ),
    inference(avatar_component_clause,[],[f3089])).

fof(f3185,plain,
    ( ~ spl2_7
    | spl2_9
    | ~ spl2_8
    | spl2_401 ),
    inference(avatar_split_clause,[],[f3184,f3181,f156,f160,f152])).

fof(f3181,plain,
    ( spl2_401
  <=> v7_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_401])])).

fof(f3184,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_401 ),
    inference(resolution,[],[f3182,f106])).

fof(f106,plain,(
    ! [X0] :
      ( v7_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( v7_lattices(X0)
        & v6_lattices(X0)
        & v5_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( ( v10_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ( v7_lattices(X0)
          & v6_lattices(X0)
          & v5_lattices(X0)
          & v4_lattices(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    inference(pure_predicate_removal,[],[f24])).

fof(f24,plain,(
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
    inference(pure_predicate_removal,[],[f2])).

fof(f2,axiom,(
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

fof(f3182,plain,
    ( ~ v7_lattices(k7_filter_1(sK0,sK1))
    | spl2_401 ),
    inference(avatar_component_clause,[],[f3181])).

fof(f3183,plain,
    ( spl2_9
    | ~ spl2_401
    | ~ spl2_398
    | spl2_390 ),
    inference(avatar_split_clause,[],[f3179,f3111,f3162,f3181,f160])).

fof(f3162,plain,
    ( spl2_398
  <=> l1_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_398])])).

fof(f3111,plain,
    ( spl2_390
  <=> v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_390])])).

fof(f3179,plain,
    ( ~ l1_lattices(k7_filter_1(sK0,sK1))
    | ~ v7_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | spl2_390 ),
    inference(resolution,[],[f3112,f112])).

fof(f112,plain,(
    ! [X0] :
      ( v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0)
      | ~ v7_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & v7_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_lattice2)).

fof(f3112,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | spl2_390 ),
    inference(avatar_component_clause,[],[f3111])).

fof(f3168,plain,
    ( ~ spl2_7
    | spl2_398 ),
    inference(avatar_split_clause,[],[f3167,f3162,f152])).

fof(f3167,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_398 ),
    inference(resolution,[],[f3163,f99])).

fof(f99,plain,(
    ! [X0] :
      ( l1_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & l1_lattices(X0) )
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( l2_lattices(X0)
        & l1_lattices(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l3_lattices)).

fof(f3163,plain,
    ( ~ l1_lattices(k7_filter_1(sK0,sK1))
    | spl2_398 ),
    inference(avatar_component_clause,[],[f3162])).

fof(f3166,plain,
    ( ~ spl2_7
    | spl2_9
    | ~ spl2_8
    | spl2_397 ),
    inference(avatar_split_clause,[],[f3165,f3159,f156,f160,f152])).

fof(f3159,plain,
    ( spl2_397
  <=> v6_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_397])])).

fof(f3165,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_397 ),
    inference(resolution,[],[f3160,f105])).

fof(f105,plain,(
    ! [X0] :
      ( v6_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3160,plain,
    ( ~ v6_lattices(k7_filter_1(sK0,sK1))
    | spl2_397 ),
    inference(avatar_component_clause,[],[f3159])).

fof(f3164,plain,
    ( spl2_9
    | ~ spl2_397
    | ~ spl2_398
    | spl2_389 ),
    inference(avatar_split_clause,[],[f3157,f3102,f3162,f3159,f160])).

fof(f3102,plain,
    ( spl2_389
  <=> v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_389])])).

fof(f3157,plain,
    ( ~ l1_lattices(k7_filter_1(sK0,sK1))
    | ~ v6_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | spl2_389 ),
    inference(resolution,[],[f3103,f109])).

fof(f109,plain,(
    ! [X0] :
      ( v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) )
      | ~ l1_lattices(X0)
      | ~ v6_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_lattices(X0)
        & v6_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_binop_1(u1_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u1_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_lattice2)).

fof(f3103,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | spl2_389 ),
    inference(avatar_component_clause,[],[f3102])).

fof(f3149,plain,
    ( ~ spl2_365
    | spl2_386 ),
    inference(avatar_split_clause,[],[f3148,f3086,f2884])).

fof(f3148,plain,
    ( ~ l1_lattices(sK0)
    | spl2_386 ),
    inference(resolution,[],[f3087,f94])).

fof(f3087,plain,
    ( ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | spl2_386 ),
    inference(avatar_component_clause,[],[f3086])).

fof(f3147,plain,
    ( ~ spl2_371
    | spl2_385 ),
    inference(avatar_split_clause,[],[f3146,f3083,f2918])).

fof(f3146,plain,
    ( ~ l1_lattices(sK1)
    | spl2_385 ),
    inference(resolution,[],[f3084,f94])).

fof(f3084,plain,
    ( ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | spl2_385 ),
    inference(avatar_component_clause,[],[f3083])).

fof(f3116,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_366
    | ~ spl2_369
    | ~ spl2_386
    | ~ spl2_372
    | ~ spl2_375
    | ~ spl2_385
    | spl2_381
    | ~ spl2_390
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(avatar_split_clause,[],[f3114,f3060,f1927,f3111,f2977,f3083,f2930,f2921,f3086,f2896,f2887,f274,f271])).

fof(f271,plain,
    ( spl2_18
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f274,plain,
    ( spl2_19
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f3114,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(forward_demodulation,[],[f3070,f1928])).

fof(f3070,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v2_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_383 ),
    inference(superposition,[],[f88,f3061])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | v2_binop_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( v2_binop_1(X3,X1)
                        & v2_binop_1(X2,X0) )
                      | ~ v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                    & ( v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
                      | ~ v2_binop_1(X3,X1)
                      | ~ v2_binop_1(X2,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f71])).

fof(f71,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( v2_binop_1(X3,X1)
                        & v2_binop_1(X2,X0) )
                      | ~ v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                    & ( v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
                      | ~ v2_binop_1(X3,X1)
                      | ~ v2_binop_1(X2,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_binop_1(X3,X1)
                      & v2_binop_1(X2,X0) )
                  <=> v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v2_binop_1(X3,X1)
                      & v2_binop_1(X2,X0) )
                  <=> v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                    & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                    & v1_funct_1(X3) )
                 => ( ( v2_binop_1(X3,X1)
                      & v2_binop_1(X2,X0) )
                  <=> v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_filter_1)).

fof(f3113,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_366
    | ~ spl2_369
    | ~ spl2_386
    | ~ spl2_372
    | ~ spl2_375
    | ~ spl2_385
    | spl2_378
    | ~ spl2_390
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(avatar_split_clause,[],[f3108,f3060,f1927,f3111,f2956,f3083,f2930,f2921,f3086,f2896,f2887,f274,f271])).

fof(f3108,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(forward_demodulation,[],[f3069,f1928])).

fof(f3069,plain,
    ( ~ v2_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v2_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_383 ),
    inference(superposition,[],[f87,f3061])).

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | v2_binop_1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f3107,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_366
    | ~ spl2_369
    | ~ spl2_386
    | ~ spl2_372
    | ~ spl2_375
    | ~ spl2_385
    | spl2_374
    | ~ spl2_389
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(avatar_split_clause,[],[f3105,f3060,f1927,f3102,f2927,f3083,f2930,f2921,f3086,f2896,f2887,f274,f271])).

fof(f3105,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(forward_demodulation,[],[f3068,f1928])).

fof(f3068,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_binop_1(u1_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_383 ),
    inference(superposition,[],[f85,f3061])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | v1_binop_1(X3,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( v1_binop_1(X3,X1)
                        & v1_binop_1(X2,X0) )
                      | ~ v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                    & ( v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
                      | ~ v1_binop_1(X3,X1)
                      | ~ v1_binop_1(X2,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( ( v1_binop_1(X3,X1)
                        & v1_binop_1(X2,X0) )
                      | ~ v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                    & ( v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
                      | ~ v1_binop_1(X3,X1)
                      | ~ v1_binop_1(X2,X0) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v1_binop_1(X3,X1)
                      & v1_binop_1(X2,X0) )
                  <=> v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v1_binop_1(X3,X1)
                      & v1_binop_1(X2,X0) )
                  <=> v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                    & v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
                    & v1_funct_1(X3) )
                 => ( ( v1_binop_1(X3,X1)
                      & v1_binop_1(X2,X0) )
                  <=> v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_filter_1)).

fof(f3104,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_366
    | ~ spl2_369
    | ~ spl2_386
    | ~ spl2_372
    | ~ spl2_375
    | ~ spl2_385
    | spl2_368
    | ~ spl2_389
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(avatar_split_clause,[],[f3099,f3060,f1927,f3102,f2893,f3083,f2930,f2921,f3086,f2896,f2887,f274,f271])).

fof(f3099,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(forward_demodulation,[],[f3067,f1928])).

fof(f3067,plain,
    ( ~ v1_binop_1(u1_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_binop_1(u1_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u1_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_383 ),
    inference(superposition,[],[f84,f3061])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_binop_1(k6_filter_1(X0,X1,X2,X3),k2_zfmisc_1(X0,X1))
      | v1_binop_1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f3096,plain,
    ( spl2_388
    | ~ spl2_385
    | ~ spl2_375
    | ~ spl2_372
    | ~ spl2_386
    | ~ spl2_369
    | ~ spl2_366
    | ~ spl2_387
    | ~ spl2_33
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(avatar_split_clause,[],[f3092,f3060,f1927,f321,f3089,f2887,f2896,f3086,f2921,f2930,f3083,f3094])).

fof(f321,plain,
    ( spl2_33
  <=> ! [X3,X2] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f3092,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | ~ spl2_33
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(forward_demodulation,[],[f3065,f1928])).

fof(f3065,plain,
    ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | r1_lattice2(u1_struct_0(sK0),u1_lattices(sK0),u2_lattices(sK0))
    | ~ spl2_33
    | ~ spl2_383 ),
    inference(superposition,[],[f322,f3061])).

fof(f322,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X3)
        | ~ v1_funct_2(X3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0)) )
    | ~ spl2_33 ),
    inference(avatar_component_clause,[],[f321])).

fof(f3091,plain,
    ( spl2_384
    | ~ spl2_385
    | ~ spl2_375
    | ~ spl2_372
    | ~ spl2_386
    | ~ spl2_369
    | ~ spl2_366
    | ~ spl2_387
    | ~ spl2_35
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(avatar_split_clause,[],[f3078,f3060,f1927,f329,f3089,f2887,f2896,f3086,f2921,f2930,f3083,f3080])).

fof(f329,plain,
    ( spl2_35
  <=> ! [X7,X6] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_35])])).

fof(f3078,plain,
    ( ~ r1_lattice2(u1_struct_0(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl2_35
    | ~ spl2_232
    | ~ spl2_383 ),
    inference(forward_demodulation,[],[f3064,f1928])).

fof(f3064,plain,
    ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u1_lattices(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)))
    | ~ v1_funct_1(u1_lattices(sK0))
    | ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_1(u1_lattices(sK1))
    | ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ m1_subset_1(u1_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | r1_lattice2(u1_struct_0(sK1),u1_lattices(sK1),u2_lattices(sK1))
    | ~ spl2_35
    | ~ spl2_383 ),
    inference(superposition,[],[f330,f3061])).

fof(f330,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | ~ v1_funct_1(X6)
        | ~ v1_funct_2(X6,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_1(X7)
        | ~ v1_funct_2(X7,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1)) )
    | ~ spl2_35 ),
    inference(avatar_component_clause,[],[f329])).

fof(f3062,plain,
    ( spl2_383
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_323 ),
    inference(avatar_split_clause,[],[f3058,f2561,f267,f152,f3060])).

fof(f267,plain,
    ( spl2_17
  <=> k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f2561,plain,
    ( spl2_323
  <=> k7_filter_1(sK0,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_323])])).

fof(f3058,plain,
    ( u1_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_323 ),
    inference(trivial_inequality_removal,[],[f3049])).

fof(f3049,plain,
    ( k7_filter_1(sK0,sK1) != k7_filter_1(sK0,sK1)
    | u1_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1))
    | ~ spl2_7
    | ~ spl2_17
    | ~ spl2_323 ),
    inference(superposition,[],[f3045,f268])).

fof(f268,plain,
    ( k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f267])).

fof(f3045,plain,
    ( ! [X6,X8,X7] :
        ( k7_filter_1(sK0,sK1) != g3_lattices(X6,X7,X8)
        | u1_lattices(k7_filter_1(sK0,sK1)) = X8 )
    | ~ spl2_7
    | ~ spl2_323 ),
    inference(forward_demodulation,[],[f3043,f2785])).

fof(f2785,plain,
    ( k7_filter_1(sK0,sK1) = g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | ~ spl2_323 ),
    inference(avatar_component_clause,[],[f2561])).

fof(f3043,plain,
    ( ! [X6,X8,X7] :
        ( g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))) != g3_lattices(X6,X7,X8)
        | u1_lattices(k7_filter_1(sK0,sK1)) = X8 )
    | ~ spl2_7 ),
    inference(resolution,[],[f2855,f153])).

fof(f153,plain,
    ( l3_lattices(k7_filter_1(sK0,sK1))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f2855,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) != g3_lattices(X1,X2,X3)
      | u1_lattices(X0) = X3 ) ),
    inference(duplicate_literal_removal,[],[f2854])).

fof(f2854,plain,(
    ! [X2,X0,X3,X1] :
      ( g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) != g3_lattices(X1,X2,X3)
      | ~ l3_lattices(X0)
      | u1_lattices(X0) = X3
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f2246,f100])).

fof(f100,plain,(
    ! [X0] :
      ( l2_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f2246,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ l2_lattices(X4)
      | g3_lattices(u1_struct_0(X4),u2_lattices(X4),u1_lattices(X4)) != g3_lattices(X6,X7,X5)
      | ~ l3_lattices(X4)
      | u1_lattices(X4) = X5 ) ),
    inference(global_subsumption,[],[f97,f96,f2244])).

fof(f2244,plain,(
    ! [X6,X4,X7,X5] :
      ( u1_lattices(X4) = X5
      | ~ v1_funct_2(u2_lattices(X4),k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X4)),u1_struct_0(X4))
      | ~ v1_funct_1(u2_lattices(X4))
      | g3_lattices(u1_struct_0(X4),u2_lattices(X4),u1_lattices(X4)) != g3_lattices(X6,X7,X5)
      | ~ l3_lattices(X4)
      | ~ l2_lattices(X4) ) ),
    inference(resolution,[],[f1739,f98])).

fof(f98,plain,(
    ! [X0] :
      ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (4426)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
fof(f9,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => ( m1_subset_1(u2_lattices(X0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u2_lattices)).

fof(f1739,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | u1_lattices(X0) = X1
      | ~ v1_funct_2(X2,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | g3_lattices(u1_struct_0(X0),X2,u1_lattices(X0)) != g3_lattices(X3,X4,X1)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f1298,f99])).

fof(f1298,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_lattices(X0)
      | u1_lattices(X0) = X4
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | g3_lattices(u1_struct_0(X0),X1,u1_lattices(X0)) != g3_lattices(X2,X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f1297])).

fof(f1297,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( g3_lattices(u1_struct_0(X0),X1,u1_lattices(X0)) != g3_lattices(X2,X3,X4)
      | u1_lattices(X0) = X4
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_lattices(X0)
      | ~ l1_lattices(X0) ) ),
    inference(resolution,[],[f524,f92])).

fof(f92,plain,(
    ! [X0] :
      ( v1_funct_1(u1_lattices(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f524,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(u1_lattices(X0))
      | g3_lattices(u1_struct_0(X0),X2,u1_lattices(X0)) != g3_lattices(X3,X4,X1)
      | u1_lattices(X0) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f523])).

fof(f523,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( u1_lattices(X0) = X1
      | g3_lattices(u1_struct_0(X0),X2,u1_lattices(X0)) != g3_lattices(X3,X4,X1)
      | ~ v1_funct_1(u1_lattices(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_lattices(X0)
      | ~ l1_lattices(X0) ) ),
    inference(resolution,[],[f177,f93])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l1_lattices(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f177,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | u1_lattices(X0) = X4
      | g3_lattices(u1_struct_0(X0),X1,u1_lattices(X0)) != g3_lattices(X2,X3,X4)
      | ~ v1_funct_1(u1_lattices(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_lattices(X0) ) ),
    inference(resolution,[],[f128,f94])).

fof(f128,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5)
      | X2 = X5
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( ! [X3,X4,X5] :
          ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2] :
      ( ! [X3,X4,X5] :
          ( ( X2 = X5
            & X1 = X4
            & X0 = X3 )
          | g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X2)
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
        & v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
        & v1_funct_1(X1) )
     => ! [X3,X4,X5] :
          ( g3_lattices(X0,X1,X2) = g3_lattices(X3,X4,X5)
         => ( X2 = X5
            & X1 = X4
            & X0 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g3_lattices)).

fof(f96,plain,(
    ! [X0] :
      ( v1_funct_1(u2_lattices(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f97,plain,(
    ! [X0] :
      ( v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f2985,plain,
    ( ~ spl2_371
    | spl2_375 ),
    inference(avatar_split_clause,[],[f2984,f2930,f2918])).

fof(f2984,plain,
    ( ~ l1_lattices(sK1)
    | spl2_375 ),
    inference(resolution,[],[f2931,f93])).

fof(f2931,plain,
    ( ~ v1_funct_2(u1_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl2_375 ),
    inference(avatar_component_clause,[],[f2930])).

fof(f2964,plain,
    ( ~ spl2_365
    | spl2_369 ),
    inference(avatar_split_clause,[],[f2963,f2896,f2884])).

fof(f2963,plain,
    ( ~ l1_lattices(sK0)
    | spl2_369 ),
    inference(resolution,[],[f2897,f93])).

fof(f2897,plain,
    ( ~ v1_funct_2(u1_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl2_369 ),
    inference(avatar_component_clause,[],[f2896])).

fof(f2940,plain,
    ( ~ spl2_371
    | spl2_372 ),
    inference(avatar_split_clause,[],[f2939,f2921,f2918])).

fof(f2939,plain,
    ( ~ l1_lattices(sK1)
    | spl2_372 ),
    inference(resolution,[],[f2922,f92])).

fof(f2922,plain,
    ( ~ v1_funct_1(u1_lattices(sK1))
    | spl2_372 ),
    inference(avatar_component_clause,[],[f2921])).

fof(f2938,plain,
    ( ~ spl2_6
    | spl2_371 ),
    inference(avatar_split_clause,[],[f2937,f2918,f148])).

fof(f2937,plain,
    ( ~ l3_lattices(sK1)
    | spl2_371 ),
    inference(resolution,[],[f2919,f99])).

fof(f2919,plain,
    ( ~ l1_lattices(sK1)
    | spl2_371 ),
    inference(avatar_component_clause,[],[f2918])).

fof(f2908,plain,
    ( ~ spl2_365
    | spl2_366 ),
    inference(avatar_split_clause,[],[f2907,f2887,f2884])).

fof(f2907,plain,
    ( ~ l1_lattices(sK0)
    | spl2_366 ),
    inference(resolution,[],[f2888,f92])).

fof(f2888,plain,
    ( ~ v1_funct_1(u1_lattices(sK0))
    | spl2_366 ),
    inference(avatar_component_clause,[],[f2887])).

fof(f2904,plain,
    ( ~ spl2_3
    | spl2_365 ),
    inference(avatar_split_clause,[],[f2903,f2884,f139])).

fof(f2903,plain,
    ( ~ l3_lattices(sK0)
    | spl2_365 ),
    inference(resolution,[],[f2885,f99])).

fof(f2885,plain,
    ( ~ l1_lattices(sK0)
    | spl2_365 ),
    inference(avatar_component_clause,[],[f2884])).

fof(f2784,plain,
    ( ~ spl2_7
    | ~ spl2_14
    | spl2_323 ),
    inference(avatar_split_clause,[],[f2783,f2561,f237,f152])).

fof(f237,plain,
    ( spl2_14
  <=> v3_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f2783,plain,
    ( ~ v3_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_323 ),
    inference(trivial_inequality_removal,[],[f2782])).

fof(f2782,plain,
    ( k7_filter_1(sK0,sK1) != k7_filter_1(sK0,sK1)
    | ~ v3_lattices(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_323 ),
    inference(superposition,[],[f2562,f101])).

fof(f101,plain,(
    ! [X0] :
      ( g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) = X0
      | ~ v3_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) = X0
      | ~ v3_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) = X0
      | ~ v3_lattices(X0)
      | ~ l3_lattices(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l3_lattices(X0)
     => ( v3_lattices(X0)
       => g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v3_lattices)).

fof(f2562,plain,
    ( k7_filter_1(sK0,sK1) != g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1)))
    | spl2_323 ),
    inference(avatar_component_clause,[],[f2561])).

fof(f2732,plain,
    ( ~ spl2_7
    | spl2_9
    | ~ spl2_8
    | spl2_352 ),
    inference(avatar_split_clause,[],[f2731,f2728,f156,f160,f152])).

fof(f2728,plain,
    ( spl2_352
  <=> v5_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_352])])).

fof(f2731,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_352 ),
    inference(resolution,[],[f2729,f104])).

fof(f104,plain,(
    ! [X0] :
      ( v5_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2729,plain,
    ( ~ v5_lattices(k7_filter_1(sK0,sK1))
    | spl2_352 ),
    inference(avatar_component_clause,[],[f2728])).

fof(f2730,plain,
    ( spl2_9
    | ~ spl2_352
    | ~ spl2_113
    | spl2_105 ),
    inference(avatar_split_clause,[],[f2726,f857,f890,f2728,f160])).

fof(f890,plain,
    ( spl2_113
  <=> l2_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_113])])).

fof(f857,plain,
    ( spl2_105
  <=> v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_105])])).

fof(f2726,plain,
    ( ~ l2_lattices(k7_filter_1(sK0,sK1))
    | ~ v5_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | spl2_105 ),
    inference(resolution,[],[f2667,f118])).

fof(f118,plain,(
    ! [X0] :
      ( v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0)
      | ~ v5_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v5_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_lattice2)).

fof(f2667,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | spl2_105 ),
    inference(avatar_component_clause,[],[f857])).

fof(f2710,plain,
    ( ~ spl2_7
    | spl2_9
    | ~ spl2_8
    | spl2_348 ),
    inference(avatar_split_clause,[],[f2708,f2701,f156,f160,f152])).

fof(f2701,plain,
    ( spl2_348
  <=> v4_lattices(k7_filter_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_348])])).

fof(f2708,plain,
    ( ~ v10_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_348 ),
    inference(resolution,[],[f2702,f103])).

fof(f103,plain,(
    ! [X0] :
      ( v4_lattices(X0)
      | ~ v10_lattices(X0)
      | v2_struct_0(X0)
      | ~ l3_lattices(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f2702,plain,
    ( ~ v4_lattices(k7_filter_1(sK0,sK1))
    | spl2_348 ),
    inference(avatar_component_clause,[],[f2701])).

fof(f2703,plain,
    ( spl2_9
    | ~ spl2_348
    | ~ spl2_113
    | spl2_103 ),
    inference(avatar_split_clause,[],[f2699,f849,f890,f2701,f160])).

fof(f849,plain,
    ( spl2_103
  <=> v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_103])])).

fof(f2699,plain,
    ( ~ l2_lattices(k7_filter_1(sK0,sK1))
    | ~ v4_lattices(k7_filter_1(sK0,sK1))
    | v2_struct_0(k7_filter_1(sK0,sK1))
    | spl2_103 ),
    inference(resolution,[],[f2665,f115])).

fof(f115,plain,(
    ! [X0] :
      ( v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) )
      | ~ l2_lattices(X0)
      | ~ v4_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l2_lattices(X0)
        & v4_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( v1_binop_1(u2_lattices(X0),u1_struct_0(X0))
        & v1_funct_2(u2_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
        & v1_funct_1(u2_lattices(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_lattice2)).

fof(f2665,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | spl2_103 ),
    inference(avatar_component_clause,[],[f849])).

fof(f2668,plain,
    ( ~ spl2_105
    | spl2_30
    | ~ spl2_232 ),
    inference(avatar_split_clause,[],[f2651,f1927,f309,f857])).

fof(f309,plain,
    ( spl2_30
  <=> v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_30])])).

fof(f2651,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | spl2_30
    | ~ spl2_232 ),
    inference(superposition,[],[f310,f1928])).

fof(f310,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl2_30 ),
    inference(avatar_component_clause,[],[f309])).

fof(f2666,plain,
    ( ~ spl2_103
    | spl2_27
    | ~ spl2_232 ),
    inference(avatar_split_clause,[],[f2650,f1927,f298,f849])).

fof(f298,plain,
    ( spl2_27
  <=> v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f2650,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),u1_struct_0(k7_filter_1(sK0,sK1)))
    | spl2_27
    | ~ spl2_232 ),
    inference(superposition,[],[f299,f1928])).

fof(f299,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f298])).

fof(f2609,plain,
    ( spl2_232
    | ~ spl2_17
    | ~ spl2_322 ),
    inference(avatar_split_clause,[],[f2608,f2557,f267,f1927])).

fof(f2557,plain,
    ( spl2_322
  <=> ! [X1,X0,X2] :
        ( g3_lattices(X0,X1,X2) != k7_filter_1(sK0,sK1)
        | u1_struct_0(k7_filter_1(sK0,sK1)) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_322])])).

fof(f2608,plain,
    ( u1_struct_0(k7_filter_1(sK0,sK1)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl2_17
    | ~ spl2_322 ),
    inference(trivial_inequality_removal,[],[f2599])).

fof(f2599,plain,
    ( k7_filter_1(sK0,sK1) != k7_filter_1(sK0,sK1)
    | u1_struct_0(k7_filter_1(sK0,sK1)) = k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl2_17
    | ~ spl2_322 ),
    inference(superposition,[],[f2558,f268])).

fof(f2558,plain,
    ( ! [X2,X0,X1] :
        ( g3_lattices(X0,X1,X2) != k7_filter_1(sK0,sK1)
        | u1_struct_0(k7_filter_1(sK0,sK1)) = X0 )
    | ~ spl2_322 ),
    inference(avatar_component_clause,[],[f2557])).

fof(f2559,plain,
    ( ~ spl2_7
    | ~ spl2_14
    | spl2_322
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f2543,f152,f2557,f237,f152])).

fof(f2543,plain,
    ( ! [X2,X0,X1] :
        ( g3_lattices(X0,X1,X2) != k7_filter_1(sK0,sK1)
        | u1_struct_0(k7_filter_1(sK0,sK1)) = X0
        | ~ v3_lattices(k7_filter_1(sK0,sK1))
        | ~ l3_lattices(k7_filter_1(sK0,sK1)) )
    | ~ spl2_7 ),
    inference(superposition,[],[f2416,f101])).

fof(f2416,plain,
    ( ! [X6,X8,X7] :
        ( g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))) != g3_lattices(X6,X7,X8)
        | u1_struct_0(k7_filter_1(sK0,sK1)) = X6 )
    | ~ spl2_7 ),
    inference(resolution,[],[f2413,f153])).

fof(f2413,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) != g3_lattices(X1,X2,X3)
      | u1_struct_0(X0) = X1 ) ),
    inference(duplicate_literal_removal,[],[f2412])).

fof(f2412,plain,(
    ! [X2,X0,X3,X1] :
      ( g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) != g3_lattices(X1,X2,X3)
      | ~ l3_lattices(X0)
      | u1_struct_0(X0) = X1
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f2199,f100])).

fof(f2199,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ l2_lattices(X4)
      | g3_lattices(u1_struct_0(X4),u2_lattices(X4),u1_lattices(X4)) != g3_lattices(X5,X6,X7)
      | ~ l3_lattices(X4)
      | u1_struct_0(X4) = X5 ) ),
    inference(global_subsumption,[],[f97,f96,f2197])).

fof(f2197,plain,(
    ! [X6,X4,X7,X5] :
      ( u1_struct_0(X4) = X5
      | ~ v1_funct_2(u2_lattices(X4),k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X4)),u1_struct_0(X4))
      | ~ v1_funct_1(u2_lattices(X4))
      | g3_lattices(u1_struct_0(X4),u2_lattices(X4),u1_lattices(X4)) != g3_lattices(X5,X6,X7)
      | ~ l3_lattices(X4)
      | ~ l2_lattices(X4) ) ),
    inference(resolution,[],[f1618,f98])).

fof(f1618,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | u1_struct_0(X0) = X1
      | ~ v1_funct_2(X2,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | g3_lattices(u1_struct_0(X0),X2,u1_lattices(X0)) != g3_lattices(X1,X3,X4)
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f1218,f99])).

fof(f1218,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_lattices(X0)
      | u1_struct_0(X0) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | g3_lattices(u1_struct_0(X0),X1,u1_lattices(X0)) != g3_lattices(X2,X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f1217])).

fof(f1217,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( g3_lattices(u1_struct_0(X0),X1,u1_lattices(X0)) != g3_lattices(X2,X3,X4)
      | u1_struct_0(X0) = X2
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_lattices(X0)
      | ~ l1_lattices(X0) ) ),
    inference(resolution,[],[f401,f92])).

fof(f401,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(u1_lattices(X0))
      | g3_lattices(u1_struct_0(X0),X2,u1_lattices(X0)) != g3_lattices(X1,X3,X4)
      | u1_struct_0(X0) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_lattices(X0) ) ),
    inference(duplicate_literal_removal,[],[f400])).

fof(f400,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( u1_struct_0(X0) = X1
      | g3_lattices(u1_struct_0(X0),X2,u1_lattices(X0)) != g3_lattices(X1,X3,X4)
      | ~ v1_funct_1(u1_lattices(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X2,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X2)
      | ~ l1_lattices(X0)
      | ~ l1_lattices(X0) ) ),
    inference(resolution,[],[f173,f93])).

fof(f173,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | u1_struct_0(X0) = X2
      | g3_lattices(u1_struct_0(X0),X1,u1_lattices(X0)) != g3_lattices(X2,X3,X4)
      | ~ v1_funct_1(u1_lattices(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_lattices(X0) ) ),
    inference(resolution,[],[f126,f94])).

fof(f126,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5)
      | X0 = X3
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f894,plain,
    ( ~ spl2_7
    | spl2_113 ),
    inference(avatar_split_clause,[],[f893,f890,f152])).

fof(f893,plain,
    ( ~ l3_lattices(k7_filter_1(sK0,sK1))
    | spl2_113 ),
    inference(resolution,[],[f891,f100])).

fof(f891,plain,
    ( ~ l2_lattices(k7_filter_1(sK0,sK1))
    | spl2_113 ),
    inference(avatar_component_clause,[],[f890])).

fof(f377,plain,
    ( ~ spl2_39
    | spl2_41 ),
    inference(avatar_split_clause,[],[f376,f373,f353])).

fof(f353,plain,
    ( spl2_39
  <=> l2_lattices(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_39])])).

fof(f373,plain,
    ( spl2_41
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_41])])).

fof(f376,plain,
    ( ~ l2_lattices(sK1)
    | spl2_41 ),
    inference(resolution,[],[f374,f95])).

fof(f95,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l2_lattices(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l2_lattices(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l2_lattices)).

fof(f374,plain,
    ( ~ l1_struct_0(sK1)
    | spl2_41 ),
    inference(avatar_component_clause,[],[f373])).

fof(f375,plain,
    ( spl2_4
    | ~ spl2_41
    | ~ spl2_19 ),
    inference(avatar_split_clause,[],[f371,f274,f373,f142])).

fof(f371,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl2_19 ),
    inference(resolution,[],[f275,f119])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f275,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f274])).

fof(f370,plain,
    ( ~ spl2_38
    | spl2_40 ),
    inference(avatar_split_clause,[],[f369,f366,f342])).

fof(f342,plain,
    ( spl2_38
  <=> l2_lattices(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_38])])).

fof(f366,plain,
    ( spl2_40
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_40])])).

fof(f369,plain,
    ( ~ l2_lattices(sK0)
    | spl2_40 ),
    inference(resolution,[],[f367,f95])).

fof(f367,plain,
    ( ~ l1_struct_0(sK0)
    | spl2_40 ),
    inference(avatar_component_clause,[],[f366])).

fof(f368,plain,
    ( spl2_1
    | ~ spl2_40
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f364,f271,f366,f133])).

fof(f364,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_18 ),
    inference(resolution,[],[f272,f119])).

fof(f272,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f271])).

fof(f363,plain,
    ( ~ spl2_39
    | spl2_25 ),
    inference(avatar_split_clause,[],[f362,f292,f353])).

fof(f292,plain,
    ( spl2_25
  <=> m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f362,plain,
    ( ~ l2_lattices(sK1)
    | spl2_25 ),
    inference(resolution,[],[f293,f98])).

fof(f293,plain,
    ( ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | spl2_25 ),
    inference(avatar_component_clause,[],[f292])).

fof(f359,plain,
    ( ~ spl2_39
    | spl2_24 ),
    inference(avatar_split_clause,[],[f358,f289,f353])).

fof(f289,plain,
    ( spl2_24
  <=> v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f358,plain,
    ( ~ l2_lattices(sK1)
    | spl2_24 ),
    inference(resolution,[],[f290,f97])).

fof(f290,plain,
    ( ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f289])).

fof(f357,plain,
    ( ~ spl2_6
    | spl2_39 ),
    inference(avatar_split_clause,[],[f356,f353,f148])).

fof(f356,plain,
    ( ~ l3_lattices(sK1)
    | spl2_39 ),
    inference(resolution,[],[f354,f100])).

fof(f354,plain,
    ( ~ l2_lattices(sK1)
    | spl2_39 ),
    inference(avatar_component_clause,[],[f353])).

fof(f355,plain,
    ( ~ spl2_39
    | spl2_23 ),
    inference(avatar_split_clause,[],[f351,f286,f353])).

fof(f286,plain,
    ( spl2_23
  <=> v1_funct_1(u2_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f351,plain,
    ( ~ l2_lattices(sK1)
    | spl2_23 ),
    inference(resolution,[],[f287,f96])).

fof(f287,plain,
    ( ~ v1_funct_1(u2_lattices(sK1))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f286])).

fof(f350,plain,
    ( ~ spl2_38
    | spl2_22 ),
    inference(avatar_split_clause,[],[f349,f283,f342])).

fof(f283,plain,
    ( spl2_22
  <=> m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f349,plain,
    ( ~ l2_lattices(sK0)
    | spl2_22 ),
    inference(resolution,[],[f284,f98])).

fof(f284,plain,
    ( ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | spl2_22 ),
    inference(avatar_component_clause,[],[f283])).

fof(f348,plain,
    ( ~ spl2_38
    | spl2_21 ),
    inference(avatar_split_clause,[],[f347,f280,f342])).

fof(f280,plain,
    ( spl2_21
  <=> v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f347,plain,
    ( ~ l2_lattices(sK0)
    | spl2_21 ),
    inference(resolution,[],[f281,f97])).

fof(f281,plain,
    ( ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | spl2_21 ),
    inference(avatar_component_clause,[],[f280])).

fof(f346,plain,
    ( ~ spl2_3
    | spl2_38 ),
    inference(avatar_split_clause,[],[f345,f342,f139])).

fof(f345,plain,
    ( ~ l3_lattices(sK0)
    | spl2_38 ),
    inference(resolution,[],[f343,f100])).

fof(f343,plain,
    ( ~ l2_lattices(sK0)
    | spl2_38 ),
    inference(avatar_component_clause,[],[f342])).

fof(f344,plain,
    ( ~ spl2_38
    | spl2_20 ),
    inference(avatar_split_clause,[],[f340,f277,f342])).

fof(f277,plain,
    ( spl2_20
  <=> v1_funct_1(u2_lattices(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f340,plain,
    ( ~ l2_lattices(sK0)
    | spl2_20 ),
    inference(resolution,[],[f278,f96])).

fof(f278,plain,
    ( ~ v1_funct_1(u2_lattices(sK0))
    | spl2_20 ),
    inference(avatar_component_clause,[],[f277])).

fof(f331,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_24
    | ~ spl2_25
    | spl2_35
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f263,f252,f329,f292,f289,f286,f283,f280,f277,f274,f271])).

fof(f252,plain,
    ( spl2_16
  <=> u2_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f263,plain,
    ( ! [X6,X7] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X6,X7),u2_lattices(k7_filter_1(sK0,sK1)))
        | r1_lattice2(u1_struct_0(sK1),X7,u2_lattices(sK1))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X7,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(X7)
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X6,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X6)
        | v1_xboole_0(u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl2_16 ),
    inference(superposition,[],[f91,f253])).

fof(f253,plain,
    ( u2_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f252])).

fof(f91,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | r1_lattice2(X1,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r1_lattice2(X1,X4,X5)
                                & r1_lattice2(X0,X2,X3) )
                              | ~ r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r1_lattice2(X1,X4,X5)
                              | ~ r1_lattice2(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( ( r1_lattice2(X1,X4,X5)
                                & r1_lattice2(X0,X2,X3) )
                              | ~ r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                            & ( r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
                              | ~ r1_lattice2(X1,X4,X5)
                              | ~ r1_lattice2(X0,X2,X3) ) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_lattice2(X1,X4,X5)
                              & r1_lattice2(X0,X2,X3) )
                          <=> r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ( ( r1_lattice2(X1,X4,X5)
                              & r1_lattice2(X0,X2,X3) )
                          <=> r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) )
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                          | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                  | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
              | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
              | ~ v1_funct_1(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                & v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
                    & v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
                    & v1_funct_1(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                        & v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
                            & v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
                            & v1_funct_1(X5) )
                         => ( ( r1_lattice2(X1,X4,X5)
                              & r1_lattice2(X0,X2,X3) )
                          <=> r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5)) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_filter_1)).

fof(f327,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_24
    | ~ spl2_25
    | spl2_34
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f262,f252,f325,f292,f289,f286,f283,f280,f277,f274,f271])).

fof(f262,plain,
    ( ! [X4,X5] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X4,X5))
        | r1_lattice2(u1_struct_0(sK1),u2_lattices(sK1),X5)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X5,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(X5)
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X4,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X4)
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(u2_lattices(sK0))
        | v1_xboole_0(u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl2_16 ),
    inference(superposition,[],[f91,f253])).

fof(f323,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_24
    | ~ spl2_25
    | spl2_33
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f261,f252,f321,f292,f289,f286,f283,f280,f277,f274,f271])).

fof(f261,plain,
    ( ! [X2,X3] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X2,X3),u2_lattices(k7_filter_1(sK0,sK1)))
        | r1_lattice2(u1_struct_0(sK0),X2,u2_lattices(sK0))
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X3,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(u2_lattices(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X2)
        | v1_xboole_0(u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl2_16 ),
    inference(superposition,[],[f90,f253])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ r1_lattice2(k2_zfmisc_1(X0,X1),k6_filter_1(X0,X1,X2,X4),k6_filter_1(X0,X1,X3,X5))
      | r1_lattice2(X0,X2,X3)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X5,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X1,X1),X1)))
      | ~ v1_funct_2(X4,k2_zfmisc_1(X1,X1),X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X3,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f319,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_24
    | ~ spl2_25
    | spl2_32
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f260,f252,f317,f292,f289,f286,f283,f280,f277,f274,f271])).

fof(f260,plain,
    ( ! [X0,X1] :
        ( ~ r1_lattice2(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),X0,X1))
        | r1_lattice2(u1_struct_0(sK0),u2_lattices(sK0),X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
        | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
        | ~ v1_funct_1(u2_lattices(sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(X0,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
        | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
        | ~ v1_funct_1(u2_lattices(sK0))
        | v1_xboole_0(u1_struct_0(sK1))
        | v1_xboole_0(u1_struct_0(sK0)) )
    | ~ spl2_16 ),
    inference(superposition,[],[f90,f253])).

fof(f315,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_24
    | ~ spl2_25
    | spl2_31
    | ~ spl2_30
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f259,f252,f309,f313,f292,f289,f286,f283,f280,f277,f274,f271])).

fof(f259,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v2_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u2_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f88,f253])).

fof(f311,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_24
    | ~ spl2_25
    | spl2_29
    | ~ spl2_30
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f258,f252,f309,f306,f292,f289,f286,f283,f280,f277,f274,f271])).

fof(f258,plain,
    ( ~ v2_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v2_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u2_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f87,f253])).

fof(f304,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_24
    | ~ spl2_25
    | spl2_28
    | ~ spl2_27
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f257,f252,f298,f302,f292,f289,f286,f283,f280,f277,f274,f271])).

fof(f257,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_binop_1(u2_lattices(sK1),u1_struct_0(sK1))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u2_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f85,f253])).

fof(f300,plain,
    ( spl2_18
    | spl2_19
    | ~ spl2_20
    | ~ spl2_21
    | ~ spl2_22
    | ~ spl2_23
    | ~ spl2_24
    | ~ spl2_25
    | spl2_26
    | ~ spl2_27
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f256,f252,f298,f295,f292,f289,f286,f283,f280,f277,f274,f271])).

fof(f256,plain,
    ( ~ v1_binop_1(u2_lattices(k7_filter_1(sK0,sK1)),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_binop_1(u2_lattices(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u2_lattices(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))))
    | ~ v1_funct_2(u2_lattices(sK1),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK1)),u1_struct_0(sK1))
    | ~ v1_funct_1(u2_lattices(sK1))
    | ~ m1_subset_1(u2_lattices(sK0),k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))))
    | ~ v1_funct_2(u2_lattices(sK0),k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK0)),u1_struct_0(sK0))
    | ~ v1_funct_1(u2_lattices(sK0))
    | v1_xboole_0(u1_struct_0(sK1))
    | v1_xboole_0(u1_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f84,f253])).

fof(f269,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | spl2_17
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f255,f252,f267,f148,f142,f139,f133])).

fof(f255,plain,
    ( k7_filter_1(sK0,sK1) = g3_lattices(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)),u2_lattices(k7_filter_1(sK0,sK1)),k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u1_lattices(sK0),u1_lattices(sK1)))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_16 ),
    inference(superposition,[],[f123,f253])).

fof(f123,plain,(
    ! [X0,X1] :
      ( k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1)))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1)))
          | ~ l3_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1)))
          | ~ l3_lattices(X1)
          | v2_struct_0(X1) )
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & ~ v2_struct_0(X1) )
         => k7_filter_1(X0,X1) = g3_lattices(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u2_lattices(X0),u2_lattices(X1)),k6_filter_1(u1_struct_0(X0),u1_struct_0(X1),u1_lattices(X0),u1_lattices(X1))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_filter_1)).

fof(f254,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | spl2_16
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f250,f240,f252,f148,f142,f139,f133])).

fof(f240,plain,
    ( spl2_15
  <=> ! [X1,X0,X2] :
        ( g3_lattices(X0,X1,X2) != k7_filter_1(sK0,sK1)
        | u2_lattices(k7_filter_1(sK0,sK1)) = X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f250,plain,
    ( u2_lattices(k7_filter_1(sK0,sK1)) = k6_filter_1(u1_struct_0(sK0),u1_struct_0(sK1),u2_lattices(sK0),u2_lattices(sK1))
    | ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_15 ),
    inference(equality_resolution,[],[f246])).

fof(f246,plain,
    ( ! [X2,X1] :
        ( k7_filter_1(sK0,sK1) != k7_filter_1(X1,X2)
        | k6_filter_1(u1_struct_0(X1),u1_struct_0(X2),u2_lattices(X1),u2_lattices(X2)) = u2_lattices(k7_filter_1(sK0,sK1))
        | ~ l3_lattices(X2)
        | v2_struct_0(X2)
        | ~ l3_lattices(X1)
        | v2_struct_0(X1) )
    | ~ spl2_15 ),
    inference(superposition,[],[f241,f123])).

fof(f241,plain,
    ( ! [X2,X0,X1] :
        ( g3_lattices(X0,X1,X2) != k7_filter_1(sK0,sK1)
        | u2_lattices(k7_filter_1(sK0,sK1)) = X1 )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f240])).

fof(f244,plain,
    ( spl2_1
    | ~ spl2_3
    | spl2_4
    | ~ spl2_6
    | spl2_14 ),
    inference(avatar_split_clause,[],[f243,f237,f148,f142,f139,f133])).

fof(f243,plain,
    ( ~ l3_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | v2_struct_0(sK0)
    | spl2_14 ),
    inference(resolution,[],[f238,f124])).

fof(f124,plain,(
    ! [X0,X1] :
      ( v3_lattices(k7_filter_1(X0,X1))
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) )
      | ~ l3_lattices(X1)
      | v2_struct_0(X1)
      | ~ l3_lattices(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( l3_lattices(X1)
        & ~ v2_struct_0(X1)
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ( l3_lattices(k7_filter_1(X0,X1))
        & v3_lattices(k7_filter_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_filter_1)).

fof(f238,plain,
    ( ~ v3_lattices(k7_filter_1(sK0,sK1))
    | spl2_14 ),
    inference(avatar_component_clause,[],[f237])).

fof(f242,plain,
    ( ~ spl2_7
    | ~ spl2_14
    | spl2_15
    | ~ spl2_7 ),
    inference(avatar_split_clause,[],[f231,f152,f240,f237,f152])).

fof(f231,plain,
    ( ! [X2,X0,X1] :
        ( g3_lattices(X0,X1,X2) != k7_filter_1(sK0,sK1)
        | u2_lattices(k7_filter_1(sK0,sK1)) = X1
        | ~ v3_lattices(k7_filter_1(sK0,sK1))
        | ~ l3_lattices(k7_filter_1(sK0,sK1)) )
    | ~ spl2_7 ),
    inference(superposition,[],[f205,f101])).

fof(f205,plain,
    ( ! [X6,X8,X7] :
        ( g3_lattices(u1_struct_0(k7_filter_1(sK0,sK1)),u2_lattices(k7_filter_1(sK0,sK1)),u1_lattices(k7_filter_1(sK0,sK1))) != g3_lattices(X6,X7,X8)
        | u2_lattices(k7_filter_1(sK0,sK1)) = X7 )
    | ~ spl2_7 ),
    inference(resolution,[],[f202,f153])).

fof(f202,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l3_lattices(X0)
      | g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) != g3_lattices(X1,X2,X3)
      | u2_lattices(X0) = X2 ) ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,(
    ! [X2,X0,X3,X1] :
      ( g3_lattices(u1_struct_0(X0),u2_lattices(X0),u1_lattices(X0)) != g3_lattices(X1,X2,X3)
      | ~ l3_lattices(X0)
      | u2_lattices(X0) = X2
      | ~ l3_lattices(X0) ) ),
    inference(resolution,[],[f195,f100])).

fof(f195,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ l2_lattices(X4)
      | g3_lattices(u1_struct_0(X4),u2_lattices(X4),u1_lattices(X4)) != g3_lattices(X6,X5,X7)
      | ~ l3_lattices(X4)
      | u2_lattices(X4) = X5 ) ),
    inference(global_subsumption,[],[f97,f96,f193])).

fof(f193,plain,(
    ! [X6,X4,X7,X5] :
      ( u2_lattices(X4) = X5
      | ~ v1_funct_2(u2_lattices(X4),k2_zfmisc_1(u1_struct_0(X4),u1_struct_0(X4)),u1_struct_0(X4))
      | ~ v1_funct_1(u2_lattices(X4))
      | g3_lattices(u1_struct_0(X4),u2_lattices(X4),u1_lattices(X4)) != g3_lattices(X6,X5,X7)
      | ~ l3_lattices(X4)
      | ~ l2_lattices(X4) ) ),
    inference(resolution,[],[f191,f98])).

fof(f191,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)),u1_struct_0(X2))))
      | X0 = X1
      | ~ v1_funct_2(X0,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | g3_lattices(u1_struct_0(X2),X0,u1_lattices(X2)) != g3_lattices(X3,X1,X4)
      | ~ l3_lattices(X2) ) ),
    inference(resolution,[],[f190,f99])).

fof(f190,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ l1_lattices(X0)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | g3_lattices(u1_struct_0(X0),X1,u1_lattices(X0)) != g3_lattices(X2,X3,X4) ) ),
    inference(duplicate_literal_removal,[],[f189])).

fof(f189,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( g3_lattices(u1_struct_0(X0),X1,u1_lattices(X0)) != g3_lattices(X2,X3,X4)
      | X1 = X3
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_lattices(X0)
      | ~ l1_lattices(X0) ) ),
    inference(resolution,[],[f188,f92])).

fof(f188,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(u1_lattices(X2))
      | g3_lattices(u1_struct_0(X2),X0,u1_lattices(X2)) != g3_lattices(X3,X1,X4)
      | X0 = X1
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ l1_lattices(X2) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( X0 = X1
      | g3_lattices(u1_struct_0(X2),X0,u1_lattices(X2)) != g3_lattices(X3,X1,X4)
      | ~ v1_funct_1(u1_lattices(X2))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)),u1_struct_0(X2))))
      | ~ v1_funct_2(X0,k2_zfmisc_1(u1_struct_0(X2),u1_struct_0(X2)),u1_struct_0(X2))
      | ~ v1_funct_1(X0)
      | ~ l1_lattices(X2)
      | ~ l1_lattices(X2) ) ),
    inference(resolution,[],[f175,f93])).

fof(f175,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_2(u1_lattices(X0),k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | X1 = X3
      | g3_lattices(u1_struct_0(X0),X1,u1_lattices(X0)) != g3_lattices(X2,X3,X4)
      | ~ v1_funct_1(u1_lattices(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))))
      | ~ v1_funct_2(X1,k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X0)),u1_struct_0(X0))
      | ~ v1_funct_1(X1)
      | ~ l1_lattices(X0) ) ),
    inference(resolution,[],[f127,f94])).

fof(f127,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | g3_lattices(X0,X1,X2) != g3_lattices(X3,X4,X5)
      | X1 = X4
      | ~ v1_funct_2(X2,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_zfmisc_1(X0,X0),X0)))
      | ~ v1_funct_2(X1,k2_zfmisc_1(X0,X0),X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f170,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f75,f133])).

fof(f75,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( ( ~ l3_lattices(sK1)
      | ~ v10_lattices(sK1)
      | v2_struct_0(sK1)
      | ~ l3_lattices(sK0)
      | ~ v10_lattices(sK0)
      | v2_struct_0(sK0) )
    & l3_lattices(k7_filter_1(sK0,sK1))
    & v10_lattices(k7_filter_1(sK0,sK1))
    & ~ v2_struct_0(k7_filter_1(sK0,sK1))
    & l3_lattices(sK1)
    & ~ v2_struct_0(sK1)
    & l3_lattices(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f27,f67,f66])).

fof(f66,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ l3_lattices(X1)
              | ~ v10_lattices(X1)
              | v2_struct_0(X1)
              | ~ l3_lattices(X0)
              | ~ v10_lattices(X0)
              | v2_struct_0(X0) )
            & l3_lattices(k7_filter_1(X0,X1))
            & v10_lattices(k7_filter_1(X0,X1))
            & ~ v2_struct_0(k7_filter_1(X0,X1))
            & l3_lattices(X1)
            & ~ v2_struct_0(X1) )
        & l3_lattices(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ l3_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(sK0)
            | ~ v10_lattices(sK0)
            | v2_struct_0(sK0) )
          & l3_lattices(k7_filter_1(sK0,X1))
          & v10_lattices(k7_filter_1(sK0,X1))
          & ~ v2_struct_0(k7_filter_1(sK0,X1))
          & l3_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X1] :
        ( ( ~ l3_lattices(X1)
          | ~ v10_lattices(X1)
          | v2_struct_0(X1)
          | ~ l3_lattices(sK0)
          | ~ v10_lattices(sK0)
          | v2_struct_0(sK0) )
        & l3_lattices(k7_filter_1(sK0,X1))
        & v10_lattices(k7_filter_1(sK0,X1))
        & ~ v2_struct_0(k7_filter_1(sK0,X1))
        & l3_lattices(X1)
        & ~ v2_struct_0(X1) )
   => ( ( ~ l3_lattices(sK1)
        | ~ v10_lattices(sK1)
        | v2_struct_0(sK1)
        | ~ l3_lattices(sK0)
        | ~ v10_lattices(sK0)
        | v2_struct_0(sK0) )
      & l3_lattices(k7_filter_1(sK0,sK1))
      & v10_lattices(k7_filter_1(sK0,sK1))
      & ~ v2_struct_0(k7_filter_1(sK0,sK1))
      & l3_lattices(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ l3_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(X0)
            | ~ v10_lattices(X0)
            | v2_struct_0(X0) )
          & l3_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1))
          & l3_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ l3_lattices(X1)
            | ~ v10_lattices(X1)
            | v2_struct_0(X1)
            | ~ l3_lattices(X0)
            | ~ v10_lattices(X0)
            | v2_struct_0(X0) )
          & l3_lattices(k7_filter_1(X0,X1))
          & v10_lattices(k7_filter_1(X0,X1))
          & ~ v2_struct_0(k7_filter_1(X0,X1))
          & l3_lattices(X1)
          & ~ v2_struct_0(X1) )
      & l3_lattices(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0] :
        ( ( l3_lattices(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( l3_lattices(X1)
              & ~ v2_struct_0(X1) )
           => ( ( l3_lattices(k7_filter_1(X0,X1))
                & v10_lattices(k7_filter_1(X0,X1))
                & ~ v2_struct_0(k7_filter_1(X0,X1)) )
             => ( l3_lattices(X1)
                & v10_lattices(X1)
                & ~ v2_struct_0(X1)
                & l3_lattices(X0)
                & v10_lattices(X0)
                & ~ v2_struct_0(X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0] :
      ( ( l3_lattices(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l3_lattices(X1)
            & ~ v2_struct_0(X1) )
         => ( ( l3_lattices(k7_filter_1(X0,X1))
              & v10_lattices(k7_filter_1(X0,X1))
              & ~ v2_struct_0(k7_filter_1(X0,X1)) )
           => ( l3_lattices(X1)
              & v10_lattices(X1)
              & ~ v2_struct_0(X1)
              & l3_lattices(X0)
              & v10_lattices(X0)
              & ~ v2_struct_0(X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_filter_1)).

fof(f168,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f76,f139])).

fof(f76,plain,(
    l3_lattices(sK0) ),
    inference(cnf_transformation,[],[f68])).

fof(f166,plain,(
    ~ spl2_4 ),
    inference(avatar_split_clause,[],[f77,f142])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f164,plain,(
    spl2_6 ),
    inference(avatar_split_clause,[],[f78,f148])).

fof(f78,plain,(
    l3_lattices(sK1) ),
    inference(cnf_transformation,[],[f68])).

fof(f162,plain,(
    ~ spl2_9 ),
    inference(avatar_split_clause,[],[f79,f160])).

fof(f79,plain,(
    ~ v2_struct_0(k7_filter_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f68])).

fof(f158,plain,(
    spl2_8 ),
    inference(avatar_split_clause,[],[f80,f156])).

fof(f80,plain,(
    v10_lattices(k7_filter_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f68])).

fof(f154,plain,(
    spl2_7 ),
    inference(avatar_split_clause,[],[f81,f152])).

fof(f81,plain,(
    l3_lattices(k7_filter_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f68])).

fof(f150,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | spl2_4
    | ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f82,f148,f145,f142,f139,f136,f133])).

fof(f82,plain,
    ( ~ l3_lattices(sK1)
    | ~ v10_lattices(sK1)
    | v2_struct_0(sK1)
    | ~ l3_lattices(sK0)
    | ~ v10_lattices(sK0)
    | v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

%------------------------------------------------------------------------------
