%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1132+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:08 EST 2020

% Result     : Theorem 17.95s
% Output     : Refutation 18.15s
% Verified   : 
% Statistics : Number of formulae       :  208 ( 701 expanded)
%              Number of leaves         :   36 ( 276 expanded)
%              Depth                    :   21
%              Number of atoms          : 1119 (5182 expanded)
%              Number of equality atoms :   37 ( 404 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16445,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2428,f2433,f2438,f2443,f2511,f2573,f2614,f2671,f2680,f2686,f3044,f3230,f5067,f6119,f7123,f7163,f7386,f13554,f15564,f15820,f15877,f16225,f16234,f16365,f16440])).

% (3817)Time limit reached!
% (3817)------------------------------
% (3817)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f16440,plain,
    ( ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_394
    | spl39_397
    | ~ spl39_417 ),
    inference(avatar_contradiction_clause,[],[f16439])).

fof(f16439,plain,
    ( $false
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_394
    | spl39_397
    | ~ spl39_417 ),
    inference(subsumption_resolution,[],[f16438,f15876])).

fof(f15876,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2)
    | spl39_397 ),
    inference(avatar_component_clause,[],[f15874])).

fof(f15874,plain,
    ( spl39_397
  <=> v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_397])])).

fof(f16438,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2)
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_394
    | ~ spl39_417 ),
    inference(subsumption_resolution,[],[f16433,f15563])).

fof(f15563,plain,
    ( m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl39_394 ),
    inference(avatar_component_clause,[],[f15561])).

fof(f15561,plain,
    ( spl39_394
  <=> m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_394])])).

fof(f16433,plain,
    ( ~ m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2)
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11
    | ~ spl39_417 ),
    inference(resolution,[],[f16425,f16224])).

fof(f16224,plain,
    ( v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),sK3)
    | ~ spl39_417 ),
    inference(avatar_component_clause,[],[f16222])).

fof(f16222,plain,
    ( spl39_417
  <=> v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_417])])).

fof(f16425,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2) )
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f16424,f2510])).

fof(f2510,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl39_6 ),
    inference(avatar_component_clause,[],[f2508])).

fof(f2508,plain,
    ( spl39_6
  <=> v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_6])])).

fof(f16424,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2)
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) )
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_7
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f14472,f2572])).

fof(f2572,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl39_7 ),
    inference(avatar_component_clause,[],[f2570])).

fof(f2570,plain,
    ( spl39_7
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_7])])).

fof(f14472,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) )
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f14471,f2427])).

fof(f2427,plain,
    ( l1_pre_topc(sK2)
    | ~ spl39_2 ),
    inference(avatar_component_clause,[],[f2425])).

fof(f2425,plain,
    ( spl39_2
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_2])])).

fof(f14471,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ l1_pre_topc(sK2) )
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f5758,f2437])).

fof(f2437,plain,
    ( l1_pre_topc(sK3)
    | ~ spl39_4 ),
    inference(avatar_component_clause,[],[f2435])).

fof(f2435,plain,
    ( spl39_4
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_4])])).

fof(f5758,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ l1_pre_topc(sK3)
        | ~ l1_pre_topc(sK2) )
    | ~ spl39_5
    | ~ spl39_11 ),
    inference(subsumption_resolution,[],[f2687,f2442])).

fof(f2442,plain,
    ( v1_funct_1(sK5)
    | ~ spl39_5 ),
    inference(avatar_component_clause,[],[f2440])).

fof(f2440,plain,
    ( spl39_5
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_5])])).

fof(f2687,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(sK3)
        | ~ l1_pre_topc(sK2) )
    | ~ spl39_11 ),
    inference(resolution,[],[f2674,f2137])).

fof(f2137,plain,(
    ! [X4,X2,X0,X1] :
      ( ~ v5_pre_topc(X2,X0,X1)
      | ~ v4_pre_topc(X4,X1)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2033])).

fof(f2033,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2)),X0)
                    & v4_pre_topc(sK6(X0,X1,X2),X1)
                    & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6])],[f2031,f2032])).

fof(f2032,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
          & v4_pre_topc(X3,X1)
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2)),X0)
        & v4_pre_topc(sK6(X0,X1,X2),X1)
        & m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f2031,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X4),X0)
                      | ~ v4_pre_topc(X4,X1)
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f2030])).

fof(f2030,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v5_pre_topc(X2,X0,X1)
                  | ? [X3] :
                      ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      & v4_pre_topc(X3,X1)
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                      | ~ v4_pre_topc(X3,X1)
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v5_pre_topc(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1865])).

fof(f1865,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1864])).

fof(f1864,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v4_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1769])).

fof(f1769,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( v4_pre_topc(X3,X1)
                     => v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d12_pre_topc)).

fof(f2674,plain,
    ( v5_pre_topc(sK5,sK2,sK3)
    | ~ spl39_11 ),
    inference(avatar_component_clause,[],[f2673])).

fof(f2673,plain,
    ( spl39_11
  <=> v5_pre_topc(sK5,sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_11])])).

fof(f16365,plain,
    ( ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_68
    | spl39_106
    | ~ spl39_116
    | ~ spl39_380
    | ~ spl39_419 ),
    inference(avatar_contradiction_clause,[],[f16364])).

fof(f16364,plain,
    ( $false
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_68
    | spl39_106
    | ~ spl39_116
    | ~ spl39_380
    | ~ spl39_419 ),
    inference(subsumption_resolution,[],[f16363,f7162])).

fof(f7162,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,sK3,sK5)),sK2)
    | spl39_106 ),
    inference(avatar_component_clause,[],[f7160])).

fof(f7160,plain,
    ( spl39_106
  <=> v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,sK3,sK5)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_106])])).

fof(f16363,plain,
    ( v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,sK3,sK5)),sK2)
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_68
    | ~ spl39_116
    | ~ spl39_380
    | ~ spl39_419 ),
    inference(subsumption_resolution,[],[f16356,f3487])).

fof(f3487,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl39_68 ),
    inference(avatar_component_clause,[],[f3485])).

fof(f3485,plain,
    ( spl39_68
  <=> m1_subset_1(sK6(sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_68])])).

fof(f16356,plain,
    ( ~ m1_subset_1(sK6(sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,sK3,sK5)),sK2)
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_116
    | ~ spl39_380
    | ~ spl39_419 ),
    inference(resolution,[],[f16233,f15152])).

fof(f15152,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2) )
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_116
    | ~ spl39_380 ),
    inference(subsumption_resolution,[],[f15151,f14991])).

fof(f14991,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl39_9
    | ~ spl39_52
    | ~ spl39_380 ),
    inference(forward_demodulation,[],[f2613,f13761])).

fof(f13761,plain,
    ( u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_52
    | ~ spl39_380 ),
    inference(trivial_inequality_removal,[],[f13758])).

fof(f13758,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))
    | u1_struct_0(sK3) = u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_52
    | ~ spl39_380 ),
    inference(superposition,[],[f3283,f13553])).

fof(f13553,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_380 ),
    inference(avatar_component_clause,[],[f13551])).

fof(f13551,plain,
    ( spl39_380
  <=> g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_380])])).

fof(f3283,plain,
    ( ! [X4,X3] :
        ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) != g1_pre_topc(X3,X4)
        | u1_struct_0(sK3) = X3 )
    | ~ spl39_52 ),
    inference(resolution,[],[f3229,f2159])).

fof(f2159,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | X0 = X2 ) ),
    inference(cnf_transformation,[],[f1874])).

fof(f1874,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1806])).

fof(f1806,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f3229,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl39_52 ),
    inference(avatar_component_clause,[],[f3227])).

fof(f3227,plain,
    ( spl39_52
  <=> m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_52])])).

fof(f2613,plain,
    ( v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_9 ),
    inference(avatar_component_clause,[],[f2611])).

fof(f2611,plain,
    ( spl39_9
  <=> v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_9])])).

fof(f15151,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) )
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_116
    | ~ spl39_380 ),
    inference(forward_demodulation,[],[f15150,f13761])).

fof(f15150,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) )
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_10
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_116
    | ~ spl39_380 ),
    inference(subsumption_resolution,[],[f15149,f14997])).

fof(f14997,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | ~ spl39_10
    | ~ spl39_52
    | ~ spl39_380 ),
    inference(forward_demodulation,[],[f2670,f13761])).

fof(f2670,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | ~ spl39_10 ),
    inference(avatar_component_clause,[],[f2668])).

fof(f2668,plain,
    ( spl39_10
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_10])])).

fof(f15149,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) )
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_116
    | ~ spl39_380 ),
    inference(forward_demodulation,[],[f15148,f13761])).

fof(f15148,plain,
    ( ! [X0] :
        ( v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,X0),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) )
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_116
    | ~ spl39_380 ),
    inference(forward_demodulation,[],[f15147,f13761])).

fof(f15147,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK3)))
        | ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,X0),sK2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) )
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_52
    | ~ spl39_116
    | ~ spl39_380 ),
    inference(forward_demodulation,[],[f15146,f13761])).

fof(f15146,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,X0),sK2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) )
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_116 ),
    inference(subsumption_resolution,[],[f15145,f2427])).

fof(f15145,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,X0),sK2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
        | ~ l1_pre_topc(sK2) )
    | ~ spl39_5
    | ~ spl39_12
    | ~ spl39_116 ),
    inference(subsumption_resolution,[],[f15144,f7385])).

fof(f7385,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_116 ),
    inference(avatar_component_clause,[],[f7383])).

fof(f7383,plain,
    ( spl39_116
  <=> l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_116])])).

fof(f15144,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,X0),sK2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ l1_pre_topc(sK2) )
    | ~ spl39_5
    | ~ spl39_12 ),
    inference(subsumption_resolution,[],[f7155,f2442])).

fof(f7155,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
        | v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,X0),sK2)
        | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
        | ~ v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
        | ~ v1_funct_1(sK5)
        | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ l1_pre_topc(sK2) )
    | ~ spl39_12 ),
    inference(resolution,[],[f2678,f2137])).

fof(f2678,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_12 ),
    inference(avatar_component_clause,[],[f2677])).

fof(f2677,plain,
    ( spl39_12
  <=> v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_12])])).

fof(f16233,plain,
    ( v4_pre_topc(sK6(sK2,sK3,sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_419 ),
    inference(avatar_component_clause,[],[f16231])).

fof(f16231,plain,
    ( spl39_419
  <=> v4_pre_topc(sK6(sK2,sK3,sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_419])])).

fof(f16234,plain,
    ( spl39_419
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_64
    | ~ spl39_68 ),
    inference(avatar_split_clause,[],[f15096,f3485,f3443,f2435,f2430,f16231])).

fof(f2430,plain,
    ( spl39_3
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_3])])).

fof(f3443,plain,
    ( spl39_64
  <=> v4_pre_topc(sK6(sK2,sK3,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_64])])).

fof(f15096,plain,
    ( v4_pre_topc(sK6(sK2,sK3,sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_64
    | ~ spl39_68 ),
    inference(subsumption_resolution,[],[f15095,f2432])).

fof(f2432,plain,
    ( v2_pre_topc(sK3)
    | ~ spl39_3 ),
    inference(avatar_component_clause,[],[f2430])).

fof(f15095,plain,
    ( v4_pre_topc(sK6(sK2,sK3,sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v2_pre_topc(sK3)
    | ~ spl39_4
    | ~ spl39_64
    | ~ spl39_68 ),
    inference(subsumption_resolution,[],[f15094,f2437])).

fof(f15094,plain,
    ( v4_pre_topc(sK6(sK2,sK3,sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl39_64
    | ~ spl39_68 ),
    inference(subsumption_resolution,[],[f6868,f3487])).

fof(f6868,plain,
    ( ~ m1_subset_1(sK6(sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(sK6(sK2,sK3,sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl39_64 ),
    inference(resolution,[],[f3445,f2163])).

fof(f2163,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2054])).

fof(f2054,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2053])).

fof(f2053,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v4_pre_topc(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            | ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
              & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            | ~ v4_pre_topc(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1877])).

fof(f1877,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1876])).

fof(f1876,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1851])).

fof(f1851,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v4_pre_topc(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
            & v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_pre_topc)).

fof(f3445,plain,
    ( v4_pre_topc(sK6(sK2,sK3,sK5),sK3)
    | ~ spl39_64 ),
    inference(avatar_component_clause,[],[f3443])).

fof(f16225,plain,
    ( spl39_417
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_52
    | ~ spl39_86
    | ~ spl39_105
    | ~ spl39_380 ),
    inference(avatar_split_clause,[],[f15049,f13551,f7120,f4930,f3227,f2435,f2430,f16222])).

fof(f4930,plain,
    ( spl39_86
  <=> v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_86])])).

fof(f7120,plain,
    ( spl39_105
  <=> m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_105])])).

fof(f15049,plain,
    ( v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),sK3)
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_52
    | ~ spl39_86
    | ~ spl39_105
    | ~ spl39_380 ),
    inference(subsumption_resolution,[],[f15048,f14233])).

fof(f14233,plain,
    ( m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ spl39_52
    | ~ spl39_105
    | ~ spl39_380 ),
    inference(forward_demodulation,[],[f7122,f13761])).

fof(f7122,plain,
    ( m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ spl39_105 ),
    inference(avatar_component_clause,[],[f7120])).

fof(f15048,plain,
    ( ~ m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),sK3)
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_52
    | ~ spl39_86
    | ~ spl39_380 ),
    inference(forward_demodulation,[],[f7140,f13761])).

fof(f7140,plain,
    ( ~ m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),sK3)
    | ~ spl39_3
    | ~ spl39_4
    | ~ spl39_86 ),
    inference(subsumption_resolution,[],[f7139,f2432])).

fof(f7139,plain,
    ( ~ m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl39_4
    | ~ spl39_86 ),
    inference(subsumption_resolution,[],[f7042,f2437])).

fof(f7042,plain,
    ( ~ m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),sK3)
    | ~ l1_pre_topc(sK3)
    | ~ v2_pre_topc(sK3)
    | ~ spl39_86 ),
    inference(resolution,[],[f4932,f2165])).

fof(f2165,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))
      | v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2054])).

fof(f4932,plain,
    ( v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_86 ),
    inference(avatar_component_clause,[],[f4930])).

fof(f15877,plain,
    ( spl39_12
    | ~ spl39_397
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10
    | ~ spl39_52
    | ~ spl39_380 ),
    inference(avatar_split_clause,[],[f14912,f13551,f3227,f2668,f2611,f2440,f2425,f15874,f2677])).

fof(f14912,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2)
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10
    | ~ spl39_52
    | ~ spl39_380 ),
    inference(forward_demodulation,[],[f7144,f13761])).

fof(f7144,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2)
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10
    | ~ spl39_52 ),
    inference(subsumption_resolution,[],[f7143,f2427])).

fof(f7143,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2)
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10
    | ~ spl39_52 ),
    inference(subsumption_resolution,[],[f7142,f3286])).

fof(f3286,plain,
    ( l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_52 ),
    inference(resolution,[],[f3229,f2162])).

fof(f2162,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | l1_pre_topc(g1_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f1875])).

fof(f1875,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1777])).

fof(f1777,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ( l1_pre_topc(g1_pre_topc(X0,X1))
        & v1_pre_topc(g1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

fof(f7142,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2)
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_9
    | ~ spl39_10 ),
    inference(subsumption_resolution,[],[f7141,f2442])).

fof(f7141,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2)
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_9
    | ~ spl39_10 ),
    inference(subsumption_resolution,[],[f6801,f2670])).

fof(f6801,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),sK5,sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5)),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_9 ),
    inference(resolution,[],[f2613,f2140])).

fof(f2140,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v4_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK6(X0,X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2033])).

fof(f15820,plain,
    ( ~ spl39_5
    | spl39_11
    | ~ spl39_7
    | spl39_64
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_6 ),
    inference(avatar_split_clause,[],[f14828,f2508,f2435,f2425,f3443,f2570,f2673,f2440])).

fof(f14828,plain,
    ( v4_pre_topc(sK6(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_6 ),
    inference(subsumption_resolution,[],[f14827,f2427])).

fof(f14827,plain,
    ( v4_pre_topc(sK6(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_4
    | ~ spl39_6 ),
    inference(subsumption_resolution,[],[f5795,f2437])).

fof(f5795,plain,
    ( v4_pre_topc(sK6(sK2,sK3,sK5),sK3)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_6 ),
    inference(resolution,[],[f2510,f2139])).

fof(f2139,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | v4_pre_topc(sK6(X0,X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2033])).

fof(f15564,plain,
    ( spl39_394
    | ~ spl39_52
    | ~ spl39_105
    | ~ spl39_380 ),
    inference(avatar_split_clause,[],[f14233,f13551,f7120,f3227,f15561])).

fof(f13554,plain,
    ( spl39_380
    | ~ spl39_46
    | ~ spl39_52 ),
    inference(avatar_split_clause,[],[f3990,f3227,f3041,f13551])).

fof(f3041,plain,
    ( spl39_46
  <=> v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl39_46])])).

fof(f3990,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ spl39_46
    | ~ spl39_52 ),
    inference(subsumption_resolution,[],[f3149,f3286])).

fof(f3149,plain,
    ( g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)) = g1_pre_topc(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))),u1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_46 ),
    inference(resolution,[],[f3043,f2176])).

fof(f2176,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f1888])).

fof(f1888,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f1887])).

fof(f1887,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1759])).

fof(f1759,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f3043,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_46 ),
    inference(avatar_component_clause,[],[f3041])).

fof(f7386,plain,
    ( spl39_116
    | ~ spl39_52 ),
    inference(avatar_split_clause,[],[f3286,f3227,f7383])).

fof(f7163,plain,
    ( spl39_11
    | ~ spl39_106
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(avatar_split_clause,[],[f7127,f2570,f2508,f2440,f2435,f2425,f7160,f2673])).

fof(f7127,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,sK3,sK5)),sK2)
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(subsumption_resolution,[],[f7126,f2427])).

fof(f7126,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,sK3,sK5)),sK2)
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(subsumption_resolution,[],[f7125,f2437])).

fof(f7125,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,sK3,sK5)),sK2)
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(subsumption_resolution,[],[f7124,f2442])).

fof(f7124,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,sK3,sK5)),sK2)
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(subsumption_resolution,[],[f6754,f2572])).

fof(f6754,plain,
    ( ~ v4_pre_topc(k8_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK5,sK6(sK2,sK3,sK5)),sK2)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_6 ),
    inference(resolution,[],[f2510,f2140])).

fof(f7123,plain,
    ( spl39_105
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | spl39_12
    | ~ spl39_52 ),
    inference(avatar_split_clause,[],[f4000,f3227,f2677,f2611,f2440,f2425,f7120])).

fof(f4000,plain,
    ( m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | spl39_12
    | ~ spl39_52 ),
    inference(subsumption_resolution,[],[f3999,f3286])).

fof(f3999,plain,
    ( m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | spl39_12 ),
    inference(subsumption_resolution,[],[f2634,f2679])).

fof(f2679,plain,
    ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | spl39_12 ),
    inference(avatar_component_clause,[],[f2677])).

fof(f2634,plain,
    ( m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9 ),
    inference(subsumption_resolution,[],[f2633,f2427])).

fof(f2633,plain,
    ( m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_9 ),
    inference(subsumption_resolution,[],[f2632,f2442])).

fof(f2632,plain,
    ( m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_9 ),
    inference(subsumption_resolution,[],[f2615,f2129])).

fof(f2129,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2028,plain,
    ( ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | ~ v5_pre_topc(sK4,sK2,sK3) )
    & ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
      | v5_pre_topc(sK4,sK2,sK3) )
    & sK4 = sK5
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_pre_topc(sK3)
    & v2_pre_topc(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f2023,f2027,f2026,f2025,f2024])).

fof(f2024,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | ~ v5_pre_topc(X2,X0,X1) )
                    & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                      | v5_pre_topc(X2,X0,X1) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_pre_topc(X1)
            & v2_pre_topc(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,sK2,X1) )
                  & ( v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,sK2,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f2025,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | ~ v5_pre_topc(X2,sK2,X1) )
                & ( v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                  | v5_pre_topc(X2,sK2,X1) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                & v1_funct_1(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_pre_topc(X1)
        & v2_pre_topc(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                | ~ v5_pre_topc(X2,sK2,sK3) )
              & ( v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
                | v5_pre_topc(X2,sK2,sK3) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
              & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
              & v1_funct_1(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
          & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
          & v1_funct_1(X2) )
      & l1_pre_topc(sK3)
      & v2_pre_topc(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f2026,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
              | ~ v5_pre_topc(X2,sK2,sK3) )
            & ( v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
              | v5_pre_topc(X2,sK2,sK3) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
            & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
        & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(sK3))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
            | ~ v5_pre_topc(sK4,sK2,sK3) )
          & ( v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
            | v5_pre_topc(sK4,sK2,sK3) )
          & sK4 = X3
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
          & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
          & v1_funct_1(X3) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
      & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f2027,plain,
    ( ? [X3] :
        ( ( ~ v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
          | ~ v5_pre_topc(sK4,sK2,sK3) )
        & ( v5_pre_topc(X3,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
          | v5_pre_topc(sK4,sK2,sK3) )
        & sK4 = X3
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
        & v1_funct_2(X3,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
        & v1_funct_1(X3) )
   => ( ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | ~ v5_pre_topc(sK4,sK2,sK3) )
      & ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
        | v5_pre_topc(sK4,sK2,sK3) )
      & sK4 = sK5
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
      & v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f2023,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2022])).

fof(f2022,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | ~ v5_pre_topc(X2,X0,X1) )
                  & ( v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
                    | v5_pre_topc(X2,X0,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f1857])).

fof(f1857,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1856])).

fof(f1856,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <~> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                  & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                  & v1_funct_1(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1854])).

fof(f1854,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                      & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                      & v1_funct_1(X3) )
                   => ( X2 = X3
                     => ( v5_pre_topc(X2,X0,X1)
                      <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1853])).

fof(f1853,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))
                    & v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_pre_topc)).

fof(f2615,plain,
    ( m1_subset_1(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_9 ),
    inference(resolution,[],[f2613,f2138])).

fof(f2138,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | m1_subset_1(sK6(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | v5_pre_topc(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2033])).

fof(f6119,plain,
    ( spl39_86
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | spl39_12
    | ~ spl39_52 ),
    inference(avatar_split_clause,[],[f3998,f3227,f2677,f2611,f2440,f2425,f4930])).

fof(f3998,plain,
    ( v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | spl39_12
    | ~ spl39_52 ),
    inference(subsumption_resolution,[],[f3997,f3286])).

fof(f3997,plain,
    ( v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9
    | spl39_12 ),
    inference(subsumption_resolution,[],[f2637,f2679])).

fof(f2637,plain,
    ( v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_2
    | ~ spl39_5
    | ~ spl39_9 ),
    inference(subsumption_resolution,[],[f2636,f2427])).

fof(f2636,plain,
    ( v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_9 ),
    inference(subsumption_resolution,[],[f2635,f2442])).

fof(f2635,plain,
    ( v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_9 ),
    inference(subsumption_resolution,[],[f2616,f2129])).

fof(f2616,plain,
    ( v4_pre_topc(sK6(sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)),sK5),g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3))))))
    | v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ l1_pre_topc(sK2)
    | ~ spl39_9 ),
    inference(resolution,[],[f2613,f2139])).

fof(f5067,plain,
    ( spl39_11
    | spl39_68
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(avatar_split_clause,[],[f4945,f2570,f2508,f2440,f2435,f2425,f3485,f2673])).

fof(f4945,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ spl39_2
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(subsumption_resolution,[],[f4944,f2427])).

fof(f4944,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_4
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(subsumption_resolution,[],[f4943,f2437])).

fof(f4943,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_5
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(subsumption_resolution,[],[f4942,f2442])).

fof(f4942,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_6
    | ~ spl39_7 ),
    inference(subsumption_resolution,[],[f4663,f2572])).

fof(f4663,plain,
    ( m1_subset_1(sK6(sK2,sK3,sK5),k1_zfmisc_1(u1_struct_0(sK3)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v5_pre_topc(sK5,sK2,sK3)
    | ~ v1_funct_1(sK5)
    | ~ l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl39_6 ),
    inference(resolution,[],[f2510,f2138])).

fof(f3230,plain,
    ( spl39_52
    | ~ spl39_4 ),
    inference(avatar_split_clause,[],[f2500,f2435,f3227])).

fof(f2500,plain,
    ( m1_subset_1(u1_pre_topc(sK3),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK3))))
    | ~ spl39_4 ),
    inference(resolution,[],[f2437,f2212])).

fof(f2212,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f1897])).

fof(f1897,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1786])).

fof(f1786,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f3044,plain,
    ( spl39_46
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(avatar_split_clause,[],[f2486,f2435,f2430,f3041])).

fof(f2486,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_3
    | ~ spl39_4 ),
    inference(subsumption_resolution,[],[f2473,f2437])).

fof(f2473,plain,
    ( ~ l1_pre_topc(sK3)
    | v1_pre_topc(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ spl39_3 ),
    inference(resolution,[],[f2432,f2171])).

fof(f2171,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(cnf_transformation,[],[f1881])).

fof(f1881,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f1880])).

fof(f1880,plain,(
    ! [X0] :
      ( ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1801])).

fof(f1801,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_pre_topc)).

fof(f2686,plain,
    ( spl39_11
    | spl39_12 ),
    inference(avatar_split_clause,[],[f2384,f2677,f2673])).

fof(f2384,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK5,sK2,sK3) ),
    inference(definition_unfolding,[],[f2131,f2130])).

fof(f2130,plain,(
    sK4 = sK5 ),
    inference(cnf_transformation,[],[f2028])).

fof(f2131,plain,
    ( v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2680,plain,
    ( ~ spl39_11
    | ~ spl39_12 ),
    inference(avatar_split_clause,[],[f2383,f2677,f2673])).

fof(f2383,plain,
    ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK5,sK2,sK3) ),
    inference(definition_unfolding,[],[f2132,f2130])).

fof(f2132,plain,
    ( ~ v5_pre_topc(sK5,sK2,g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))
    | ~ v5_pre_topc(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2671,plain,(
    spl39_10 ),
    inference(avatar_split_clause,[],[f2129,f2668])).

fof(f2614,plain,(
    spl39_9 ),
    inference(avatar_split_clause,[],[f2128,f2611])).

fof(f2128,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(g1_pre_topc(u1_struct_0(sK3),u1_pre_topc(sK3)))) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2573,plain,(
    spl39_7 ),
    inference(avatar_split_clause,[],[f2385,f2570])).

fof(f2385,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(definition_unfolding,[],[f2126,f2130])).

fof(f2126,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2511,plain,(
    spl39_6 ),
    inference(avatar_split_clause,[],[f2386,f2508])).

fof(f2386,plain,(
    v1_funct_2(sK5,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(definition_unfolding,[],[f2125,f2130])).

fof(f2125,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2443,plain,(
    spl39_5 ),
    inference(avatar_split_clause,[],[f2127,f2440])).

fof(f2127,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2438,plain,(
    spl39_4 ),
    inference(avatar_split_clause,[],[f2123,f2435])).

fof(f2123,plain,(
    l1_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2433,plain,(
    spl39_3 ),
    inference(avatar_split_clause,[],[f2122,f2430])).

fof(f2122,plain,(
    v2_pre_topc(sK3) ),
    inference(cnf_transformation,[],[f2028])).

fof(f2428,plain,(
    spl39_2 ),
    inference(avatar_split_clause,[],[f2121,f2425])).

fof(f2121,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f2028])).
%------------------------------------------------------------------------------
