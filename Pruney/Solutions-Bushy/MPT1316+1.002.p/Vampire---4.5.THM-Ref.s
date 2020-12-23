%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1316+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:43 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 197 expanded)
%              Number of leaves         :   19 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :  383 ( 737 expanded)
%              Number of equality atoms :   11 (  40 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f147,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f40,f45,f50,f55,f61,f67,f72,f88,f92,f116,f129,f134,f141,f146])).

fof(f146,plain,
    ( spl5_6
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl5_6
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f144,f60])).

fof(f60,plain,
    ( ~ v1_tops_2(sK1,sK2)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl5_6
  <=> v1_tops_2(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f144,plain,
    ( v1_tops_2(sK1,sK2)
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f143,f86])).

fof(f86,plain,
    ( l1_pre_topc(sK2)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl5_10
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f143,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_8
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f142,f71])).

fof(f71,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl5_8
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f142,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_11 ),
    inference(resolution,[],[f105,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK4(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r2_hidden(X2,X1)
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_2)).

fof(f105,plain,
    ( v3_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_11
  <=> v3_pre_topc(sK4(sK2,sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f141,plain,
    ( ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl5_5
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f139,f60])).

fof(f139,plain,
    ( v1_tops_2(sK1,sK2)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f138,f86])).

fof(f138,plain,
    ( ~ l1_pre_topc(sK2)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f137,f71])).

fof(f137,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_5
    | ~ spl5_7
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f136,f66])).

fof(f66,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f64])).

fof(f64,plain,
    ( spl5_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_5
    | ~ spl5_15 ),
    inference(subsumption_resolution,[],[f135,f54])).

fof(f54,plain,
    ( v1_tops_2(sK1,sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl5_5
  <=> v1_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f135,plain,
    ( ~ v1_tops_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | v1_tops_2(sK1,sK2)
    | ~ spl5_15 ),
    inference(resolution,[],[f128,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f128,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(sK2,sK1),X0)
        | ~ v1_tops_2(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f127])).

fof(f127,plain,
    ( spl5_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X0,sK0)
        | ~ r2_hidden(sK4(sK2,sK1),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f134,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | ~ spl5_9
    | spl5_11
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_9
    | spl5_11
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f132,f104])).

fof(f104,plain,
    ( ~ v3_pre_topc(sK4(sK2,sK1),sK2)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f132,plain,
    ( v3_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f131,f83])).

fof(f83,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl5_9
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f131,plain,
    ( ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v3_pre_topc(sK4(sK2,sK1),sK2)
    | ~ spl5_1
    | ~ spl5_4
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(resolution,[],[f130,f49])).

fof(f49,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f47])).

fof(f47,plain,
    ( spl5_4
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f130,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X1)))
        | v3_pre_topc(sK4(sK2,sK1),X1) )
    | ~ spl5_1
    | ~ spl5_13
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f121,f125])).

fof(f125,plain,
    ( v3_pre_topc(sK4(sK2,sK1),sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl5_14
  <=> v3_pre_topc(sK4(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f121,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | ~ v3_pre_topc(sK4(sK2,sK1),sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X1)))
        | v3_pre_topc(sK4(sK2,sK1),X1) )
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f118,f34])).

fof(f34,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f32])).

fof(f32,plain,
    ( spl5_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f118,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v3_pre_topc(sK4(sK2,sK1),sK0)
        | ~ m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(X1)))
        | v3_pre_topc(sK4(sK2,sK1),X1) )
    | ~ spl5_13 ),
    inference(resolution,[],[f115,f30])).

fof(f30,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f24])).

fof(f24,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f115,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_13
  <=> m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f129,plain,
    ( spl5_14
    | spl5_15
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f120,f113,f32,f127,f123])).

fof(f120,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r2_hidden(sK4(sK2,sK1),X0)
        | v3_pre_topc(sK4(sK2,sK1),sK0)
        | ~ v1_tops_2(X0,sK0) )
    | ~ spl5_1
    | ~ spl5_13 ),
    inference(subsumption_resolution,[],[f117,f34])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ l1_pre_topc(sK0)
        | ~ r2_hidden(sK4(sK2,sK1),X0)
        | v3_pre_topc(sK4(sK2,sK1),sK0)
        | ~ v1_tops_2(X0,sK0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f115,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X2,X1)
      | v3_pre_topc(X2,X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f116,plain,
    ( spl5_13
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f100,f85,f69,f64,f58,f113])).

fof(f100,plain,
    ( m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f99,f86])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_6
    | ~ spl5_7
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f98,f71])).

fof(f98,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ l1_pre_topc(sK2)
    | m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl5_6
    | ~ spl5_7 ),
    inference(resolution,[],[f78,f60])).

fof(f78,plain,
    ( ! [X0] :
        ( v1_tops_2(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
        | ~ l1_pre_topc(X0)
        | m1_subset_1(sK4(X0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_7 ),
    inference(resolution,[],[f74,f27])).

fof(f74,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK1)
        | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_7 ),
    inference(resolution,[],[f66,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f92,plain,
    ( ~ spl5_1
    | ~ spl5_4
    | spl5_10 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | ~ spl5_1
    | ~ spl5_4
    | spl5_10 ),
    inference(subsumption_resolution,[],[f90,f34])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl5_4
    | spl5_10 ),
    inference(resolution,[],[f89,f49])).

fof(f89,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0) )
    | spl5_10 ),
    inference(resolution,[],[f87,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f87,plain,
    ( ~ l1_pre_topc(sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f85])).

fof(f88,plain,
    ( spl5_9
    | ~ spl5_10
    | spl5_6
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f77,f69,f58,f85,f81])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | spl5_6
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f75,f60])).

fof(f75,plain,
    ( ~ l1_pre_topc(sK2)
    | m1_subset_1(sK4(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK2)))
    | v1_tops_2(sK1,sK2)
    | ~ spl5_8 ),
    inference(resolution,[],[f71,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f72,plain,
    ( spl5_8
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f62,f37,f69])).

fof(f37,plain,
    ( spl5_2
  <=> sK1 = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2))))
    | ~ spl5_2 ),
    inference(forward_demodulation,[],[f16,f39])).

fof(f39,plain,
    ( sK1 = sK3
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f37])).

fof(f16,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ v1_tops_2(X3,X2)
                  & X1 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2)))) )
              & v1_tops_2(X1,X0)
              & m1_pre_topc(X2,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ! [X2] :
                ( m1_pre_topc(X2,X0)
               => ( v1_tops_2(X1,X0)
                 => ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                     => ( X1 = X3
                       => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v1_tops_2(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X2))))
                   => ( X1 = X3
                     => v1_tops_2(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tops_2)).

fof(f67,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f21,f64])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f8])).

fof(f61,plain,
    ( ~ spl5_6
    | ~ spl5_2
    | spl5_3 ),
    inference(avatar_split_clause,[],[f56,f42,f37,f58])).

fof(f42,plain,
    ( spl5_3
  <=> v1_tops_2(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f56,plain,
    ( ~ v1_tops_2(sK1,sK2)
    | ~ spl5_2
    | spl5_3 ),
    inference(forward_demodulation,[],[f44,f39])).

fof(f44,plain,
    ( ~ v1_tops_2(sK3,sK2)
    | spl5_3 ),
    inference(avatar_component_clause,[],[f42])).

fof(f55,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f20,f52])).

fof(f20,plain,(
    v1_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f50,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f19,f47])).

fof(f19,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f8])).

fof(f45,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f18,f42])).

fof(f18,plain,(
    ~ v1_tops_2(sK3,sK2) ),
    inference(cnf_transformation,[],[f8])).

fof(f40,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f17,f37])).

fof(f17,plain,(
    sK1 = sK3 ),
    inference(cnf_transformation,[],[f8])).

fof(f35,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f22,f32])).

fof(f22,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f8])).

%------------------------------------------------------------------------------
