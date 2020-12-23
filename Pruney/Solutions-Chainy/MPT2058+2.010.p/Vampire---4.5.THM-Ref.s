%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 459 expanded)
%              Number of leaves         :   39 ( 180 expanded)
%              Depth                    :   16
%              Number of atoms          : 1170 (2106 expanded)
%              Number of equality atoms :   25 (  36 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f406,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f122,f127,f132,f138,f143,f148,f157,f159,f180,f197,f207,f210,f268,f311,f327,f349,f350,f359,f369,f388,f396,f405])).

fof(f405,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_12
    | ~ spl6_35 ),
    inference(avatar_contradiction_clause,[],[f404])).

fof(f404,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_12
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f403,f82])).

fof(f82,plain,
    ( ~ v1_xboole_0(sK1)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f80,plain,
    ( spl6_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f403,plain,
    ( v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_12
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f402,f147])).

fof(f147,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f145,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f402,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_12
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f401,f137])).

fof(f137,plain,
    ( v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f135,plain,
    ( spl6_8
  <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f401,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | spl6_12
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f400,f131])).

fof(f131,plain,
    ( v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_7
  <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f400,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_9
    | spl6_12
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f399,f142])).

fof(f142,plain,
    ( v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f140,plain,
    ( spl6_9
  <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f399,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_4
    | spl6_12
    | ~ spl6_35 ),
    inference(subsumption_resolution,[],[f398,f155])).

fof(f155,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl6_12
  <=> r1_waybel_7(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f398,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v1_xboole_0(sK1)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_35 ),
    inference(superposition,[],[f395,f117])).

fof(f117,plain,
    ( ! [X0] :
        ( k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0
        | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | v1_xboole_0(X0) )
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f99,f113])).

fof(f113,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_4 ),
    inference(resolution,[],[f97,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f97,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f95,plain,
    ( spl6_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK0)
        | v1_xboole_0(X0)
        | ~ v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 )
    | spl6_2 ),
    inference(resolution,[],[f87,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
      | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          | ~ v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          | ~ v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          | v1_xboole_0(X1) )
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).

fof(f87,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f395,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f393])).

fof(f393,plain,
    ( spl6_35
  <=> r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f396,plain,
    ( spl6_35
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_30 ),
    inference(avatar_split_clause,[],[f391,f317,f150,f119,f393])).

fof(f119,plain,
    ( spl6_5
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f150,plain,
    ( spl6_11
  <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f317,plain,
    ( spl6_30
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f391,plain,
    ( r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ spl6_5
    | ~ spl6_11
    | ~ spl6_30 ),
    inference(subsumption_resolution,[],[f390,f121])).

fof(f121,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f119])).

fof(f390,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)
    | ~ spl6_11
    | ~ spl6_30 ),
    inference(resolution,[],[f152,f318])).

fof(f318,plain,
    ( ! [X0] :
        ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) )
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f317])).

fof(f152,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f388,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_33 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f386,f121])).

fof(f386,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f385,f151])).

fof(f151,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f385,plain,
    ( r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_12
    | ~ spl6_33 ),
    inference(resolution,[],[f376,f156])).

fof(f156,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f154])).

fof(f376,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f375,f82])).

fof(f375,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v1_xboole_0(sK1) )
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f374,f147])).

fof(f374,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | v1_xboole_0(sK1) )
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f373,f137])).

fof(f373,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | v1_xboole_0(sK1) )
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f372,f131])).

fof(f372,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | v1_xboole_0(sK1) )
    | spl6_2
    | ~ spl6_4
    | ~ spl6_9
    | ~ spl6_33 ),
    inference(subsumption_resolution,[],[f371,f142])).

fof(f371,plain,
    ( ! [X0] :
        ( ~ r1_waybel_7(sK0,sK1,X0)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
        | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
        | v1_xboole_0(sK1) )
    | spl6_2
    | ~ spl6_4
    | ~ spl6_33 ),
    inference(superposition,[],[f348,f117])).

fof(f348,plain,
    ( ! [X1] :
        ( ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f347])).

fof(f347,plain,
    ( spl6_33
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f369,plain,
    ( spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_14
    | ~ spl6_15
    | spl6_32 ),
    inference(avatar_contradiction_clause,[],[f368])).

fof(f368,plain,
    ( $false
    | spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_14
    | ~ spl6_15
    | spl6_32 ),
    inference(subsumption_resolution,[],[f367,f87])).

fof(f367,plain,
    ( v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10
    | spl6_14
    | ~ spl6_15
    | spl6_32 ),
    inference(subsumption_resolution,[],[f366,f147])).

fof(f366,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | spl6_14
    | ~ spl6_15
    | spl6_32 ),
    inference(subsumption_resolution,[],[f365,f137])).

fof(f365,plain,
    ( ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | spl6_14
    | ~ spl6_15
    | spl6_32 ),
    inference(subsumption_resolution,[],[f364,f131])).

fof(f364,plain,
    ( ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_6
    | spl6_14
    | ~ spl6_15
    | spl6_32 ),
    inference(subsumption_resolution,[],[f363,f82])).

fof(f363,plain,
    ( v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_14
    | ~ spl6_15
    | spl6_32 ),
    inference(subsumption_resolution,[],[f362,f178])).

fof(f178,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f177,plain,
    ( spl6_15
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f362,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_14
    | spl6_32 ),
    inference(subsumption_resolution,[],[f361,f174])).

fof(f174,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | spl6_14 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl6_14
  <=> v1_xboole_0(k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f361,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_32 ),
    inference(subsumption_resolution,[],[f360,f126])).

fof(f126,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f124])).

fof(f124,plain,
    ( spl6_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

% (9555)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
fof(f360,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl6_32 ),
    inference(resolution,[],[f326,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v4_orders_2(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v4_orders_2(k3_yellow19(X0,X1,X2))
        & v3_orders_2(k3_yellow19(X0,X1,X2))
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).

fof(f326,plain,
    ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl6_32 ),
    inference(avatar_component_clause,[],[f324])).

fof(f324,plain,
    ( spl6_32
  <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f359,plain,
    ( spl6_2
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(avatar_contradiction_clause,[],[f358])).

fof(f358,plain,
    ( $false
    | spl6_2
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f357,f87])).

fof(f357,plain,
    ( v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_29 ),
    inference(subsumption_resolution,[],[f355,f126])).

fof(f355,plain,
    ( ~ l1_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ spl6_29 ),
    inference(resolution,[],[f310,f55])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f310,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f308])).

fof(f308,plain,
    ( spl6_29
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f350,plain,
    ( spl6_14
    | spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_15
    | spl6_31 ),
    inference(avatar_split_clause,[],[f345,f320,f177,f145,f140,f135,f129,f124,f85,f80,f173])).

fof(f320,plain,
    ( spl6_31
  <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f345,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | spl6_1
    | spl6_2
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_15
    | spl6_31 ),
    inference(subsumption_resolution,[],[f344,f87])).

fof(f344,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_10
    | ~ spl6_15
    | spl6_31 ),
    inference(subsumption_resolution,[],[f343,f147])).

fof(f343,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_15
    | spl6_31 ),
    inference(subsumption_resolution,[],[f342,f137])).

fof(f342,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_15
    | spl6_31 ),
    inference(subsumption_resolution,[],[f341,f131])).

fof(f341,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_9
    | ~ spl6_15
    | spl6_31 ),
    inference(subsumption_resolution,[],[f340,f142])).

fof(f340,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl6_1
    | ~ spl6_6
    | ~ spl6_15
    | spl6_31 ),
    inference(subsumption_resolution,[],[f339,f82])).

fof(f339,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | ~ spl6_15
    | spl6_31 ),
    inference(subsumption_resolution,[],[f329,f178])).

fof(f329,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | ~ spl6_6
    | spl6_31 ),
    inference(subsumption_resolution,[],[f328,f126])).

fof(f328,plain,
    ( ~ l1_struct_0(sK0)
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | v2_struct_0(sK0)
    | spl6_31 ),
    inference(resolution,[],[f322,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v7_waybel_0(k3_yellow19(X0,X1,X2))
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1)))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( v7_waybel_0(k3_yellow19(X0,X1,X2))
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).

fof(f322,plain,
    ( ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl6_31 ),
    inference(avatar_component_clause,[],[f320])).

fof(f349,plain,
    ( spl6_33
    | ~ spl6_31
    | ~ spl6_32
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_13
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f315,f204,f169,f95,f90,f85,f324,f320,f347])).

fof(f90,plain,
    ( spl6_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f169,plain,
    ( spl6_13
  <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f204,plain,
    ( spl6_18
  <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f315,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_13
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f313,f171])).

fof(f171,plain,
    ( ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl6_13 ),
    inference(avatar_component_clause,[],[f169])).

fof(f313,plain,
    ( ! [X1] :
        ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1)
        | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(resolution,[],[f206,f110])).

fof(f110,plain,
    ( ! [X0,X1] :
        ( ~ l1_waybel_0(X0,sK0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | v2_struct_0(X0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
        | r3_waybel_9(sK0,X0,X1) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f109,f97])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
        | r3_waybel_9(sK0,X0,X1) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f107,f87])).

fof(f107,plain,
    ( ! [X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ v4_orders_2(X0)
        | ~ v7_waybel_0(X0)
        | ~ l1_waybel_0(X0,sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1)
        | r3_waybel_9(sK0,X0,X1) )
    | ~ spl6_3 ),
    inference(resolution,[],[f92,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ l1_waybel_0(X1,X0)
          | ~ v7_waybel_0(X1)
          | ~ v4_orders_2(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_waybel_0(X1,X0)
            & v7_waybel_0(X1)
            & v4_orders_2(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,X1,X2)
              <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).

fof(f92,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f206,plain,
    ( l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f204])).

fof(f327,plain,
    ( spl6_30
    | ~ spl6_31
    | ~ spl6_32
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_13
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f314,f204,f169,f95,f90,f85,f324,f320,f317])).

fof(f314,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | spl6_13
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f312,f171])).

fof(f312,plain,
    ( ! [X0] :
        ( ~ v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)
        | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_18 ),
    inference(resolution,[],[f206,f112])).

fof(f112,plain,
    ( ! [X2,X3] :
        ( ~ l1_waybel_0(X2,sK0)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | v2_struct_0(X2)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3)
        | ~ r3_waybel_9(sK0,X2,X3) )
    | spl6_2
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f111,f97])).

fof(f111,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3)
        | ~ r3_waybel_9(sK0,X2,X3) )
    | spl6_2
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f108,f87])).

fof(f108,plain,
    ( ! [X2,X3] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ v4_orders_2(X2)
        | ~ v7_waybel_0(X2)
        | ~ l1_waybel_0(X2,sK0)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3)
        | ~ r3_waybel_9(sK0,X2,X3) )
    | ~ spl6_3 ),
    inference(resolution,[],[f92,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v4_orders_2(X1)
      | ~ v7_waybel_0(X1)
      | ~ l1_waybel_0(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_waybel_7(X0,k2_yellow19(X0,X1),X2)
      | ~ r3_waybel_9(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f311,plain,
    ( spl6_29
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(avatar_split_clause,[],[f296,f265,f173,f308])).

fof(f265,plain,
    ( spl6_25
  <=> u1_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f296,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | ~ spl6_14
    | ~ spl6_25 ),
    inference(superposition,[],[f228,f267])).

fof(f267,plain,
    ( u1_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f265])).

fof(f228,plain,
    ( ! [X0] : v1_xboole_0(k4_xboole_0(k2_struct_0(sK0),X0))
    | ~ spl6_14 ),
    inference(resolution,[],[f222,f57])).

fof(f57,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f222,plain,
    ( ! [X4,X5] : ~ r2_hidden(X4,k4_xboole_0(k2_struct_0(sK0),X5))
    | ~ spl6_14 ),
    inference(resolution,[],[f214,f77])).

fof(f77,plain,(
    ! [X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,k4_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k4_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( ~ r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

fof(f214,plain,
    ( ! [X0,X1] : ~ sP5(X0,X1,k2_struct_0(sK0))
    | ~ spl6_14 ),
    inference(resolution,[],[f211,f71])).

fof(f71,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | ~ sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f211,plain,
    ( ! [X0] : ~ r2_hidden(X0,k2_struct_0(sK0))
    | ~ spl6_14 ),
    inference(resolution,[],[f175,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | ~ r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f175,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f173])).

fof(f268,plain,
    ( spl6_25
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f219,f194,f177,f265])).

fof(f194,plain,
    ( spl6_16
  <=> u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f219,plain,
    ( u1_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl6_15
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f216,f178])).

fof(f216,plain,
    ( u1_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(superposition,[],[f196,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f196,plain,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f194])).

fof(f210,plain,
    ( ~ spl6_6
    | spl6_15 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | ~ spl6_6
    | spl6_15 ),
    inference(subsumption_resolution,[],[f208,f126])).

fof(f208,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_15 ),
    inference(resolution,[],[f179,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f179,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_15 ),
    inference(avatar_component_clause,[],[f177])).

fof(f207,plain,
    ( spl6_18
    | spl6_14
    | ~ spl6_15
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f184,f145,f135,f129,f95,f85,f80,f177,f173,f204])).

fof(f184,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f183,f147])).

fof(f183,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f182,f131])).

fof(f182,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f181,f82])).

fof(f181,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(resolution,[],[f114,f137])).

fof(f114,plain,
    ( ! [X10,X9] :
        ( ~ v13_waybel_0(X10,k3_yellow_1(X9))
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X10)
        | ~ v2_waybel_0(X10,k3_yellow_1(X9))
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9))))
        | l1_waybel_0(k3_yellow19(sK0,X9,X10),sK0) )
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f104,f113])).

fof(f104,plain,
    ( ! [X10,X9] :
        ( ~ l1_struct_0(sK0)
        | v1_xboole_0(X9)
        | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X10)
        | ~ v2_waybel_0(X10,k3_yellow_1(X9))
        | ~ v13_waybel_0(X10,k3_yellow_1(X9))
        | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9))))
        | l1_waybel_0(k3_yellow19(sK0,X9,X10),sK0) )
    | spl6_2 ),
    inference(resolution,[],[f87,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | l1_waybel_0(k3_yellow19(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        & v13_waybel_0(X2,k3_yellow_1(X1))
        & v2_waybel_0(X2,k3_yellow_1(X1))
        & ~ v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & ~ v1_xboole_0(X1)
        & l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & v6_waybel_0(k3_yellow19(X0,X1,X2),X0)
        & ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).

fof(f197,plain,
    ( spl6_16
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f162,f124,f194])).

fof(f162,plain,
    ( u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f160,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f160,plain,
    ( k2_subset_1(u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_subset_1(u1_struct_0(sK0))))
    | ~ spl6_6 ),
    inference(resolution,[],[f133,f48])).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0 )
    | ~ spl6_6 ),
    inference(resolution,[],[f126,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).

fof(f180,plain,
    ( ~ spl6_13
    | spl6_14
    | ~ spl6_15
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f167,f145,f135,f129,f95,f85,f80,f177,f173,f169])).

fof(f167,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f166,f147])).

fof(f166,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_7
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f165,f131])).

fof(f165,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl6_1
    | spl6_2
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f164,f82])).

fof(f164,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_xboole_0(sK1)
    | ~ v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))
    | v1_xboole_0(k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))
    | ~ v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))
    | spl6_2
    | ~ spl6_4
    | ~ spl6_8 ),
    inference(resolution,[],[f116,f137])).

fof(f116,plain,
    ( ! [X2,X1] :
        ( ~ v13_waybel_0(X2,k3_yellow_1(X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X2)
        | ~ v2_waybel_0(X2,k3_yellow_1(X1))
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        | ~ v2_struct_0(k3_yellow19(sK0,X1,X2)) )
    | spl6_2
    | ~ spl6_4 ),
    inference(subsumption_resolution,[],[f100,f113])).

fof(f100,plain,
    ( ! [X2,X1] :
        ( ~ l1_struct_0(sK0)
        | v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_xboole_0(X2)
        | ~ v2_waybel_0(X2,k3_yellow_1(X1))
        | ~ v13_waybel_0(X2,k3_yellow_1(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
        | ~ v2_struct_0(k3_yellow19(sK0,X1,X2)) )
    | spl6_2 ),
    inference(resolution,[],[f87,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X2)
      | ~ v2_waybel_0(X2,k3_yellow_1(X1))
      | ~ v13_waybel_0(X2,k3_yellow_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1))))
      | ~ v2_struct_0(k3_yellow19(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f159,plain,
    ( ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f158,f154,f150])).

fof(f158,plain,
    ( ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f37,f156])).

fof(f37,plain,
    ( ~ r1_waybel_7(sK0,sK1,sK2)
    | ~ r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <~> r1_waybel_7(X0,X1,X2) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
          & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
          & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
              & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
              & ~ v1_xboole_0(X1) )
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
                <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
            & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0)))
            & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
            & ~ v1_xboole_0(X1) )
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2)
              <=> r1_waybel_7(X0,X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).

fof(f157,plain,
    ( spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f36,f154,f150])).

fof(f36,plain,
    ( r1_waybel_7(sK0,sK1,sK2)
    | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) ),
    inference(cnf_transformation,[],[f19])).

fof(f148,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f43,f145])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) ),
    inference(cnf_transformation,[],[f19])).

fof(f143,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f40,f140])).

fof(f40,plain,(
    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f19])).

fof(f138,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f42,f135])).

fof(f42,plain,(
    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f132,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f41,f129])).

fof(f41,plain,(
    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f19])).

fof(f127,plain,
    ( spl6_6
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f113,f95,f124])).

fof(f122,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f38,f119])).

fof(f38,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f19])).

fof(f98,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f46,f95])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f93,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f45,f90])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f44,f85])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f19])).

fof(f83,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f39,f80])).

fof(f39,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 09:39:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (9527)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.53  % (9533)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.21/0.54  % (9542)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.21/0.54  % (9531)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (9530)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (9534)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.21/0.54  % (9526)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.54  % (9548)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.54  % (9528)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.55  % (9529)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.55  % (9540)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.55  % (9528)Refutation not found, incomplete strategy% (9528)------------------------------
% 0.21/0.55  % (9528)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9528)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9528)Memory used [KB]: 10746
% 0.21/0.55  % (9528)Time elapsed: 0.133 s
% 0.21/0.55  % (9528)------------------------------
% 0.21/0.55  % (9528)------------------------------
% 0.21/0.55  % (9554)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.55  % (9534)Refutation not found, incomplete strategy% (9534)------------------------------
% 0.21/0.55  % (9534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (9532)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.55  % (9539)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.21/0.55  % (9550)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (9549)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.21/0.55  % (9546)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.55  % (9534)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (9534)Memory used [KB]: 10746
% 0.21/0.55  % (9534)Time elapsed: 0.135 s
% 0.21/0.55  % (9534)------------------------------
% 0.21/0.55  % (9534)------------------------------
% 0.21/0.56  % (9552)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.21/0.56  % (9543)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.56  % (9551)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.21/0.56  % (9538)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.56  % (9545)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.21/0.56  % (9535)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.56  % (9544)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.56  % (9547)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.56  % (9541)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.21/0.56  % (9543)Refutation not found, incomplete strategy% (9543)------------------------------
% 0.21/0.56  % (9543)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (9543)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (9543)Memory used [KB]: 10746
% 0.21/0.56  % (9543)Time elapsed: 0.144 s
% 0.21/0.56  % (9543)------------------------------
% 0.21/0.56  % (9543)------------------------------
% 0.21/0.57  % (9548)Refutation not found, incomplete strategy% (9548)------------------------------
% 0.21/0.57  % (9548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9548)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9548)Memory used [KB]: 10874
% 0.21/0.57  % (9548)Time elapsed: 0.107 s
% 0.21/0.57  % (9548)------------------------------
% 0.21/0.57  % (9548)------------------------------
% 0.21/0.57  % (9536)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.57  % (9530)Refutation not found, incomplete strategy% (9530)------------------------------
% 0.21/0.57  % (9530)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9530)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9530)Memory used [KB]: 6396
% 0.21/0.57  % (9530)Time elapsed: 0.152 s
% 0.21/0.57  % (9530)------------------------------
% 0.21/0.57  % (9530)------------------------------
% 0.21/0.57  % (9536)Refutation not found, incomplete strategy% (9536)------------------------------
% 0.21/0.57  % (9536)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9536)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9536)Memory used [KB]: 10618
% 0.21/0.57  % (9536)Time elapsed: 0.155 s
% 0.21/0.57  % (9536)------------------------------
% 0.21/0.57  % (9536)------------------------------
% 0.21/0.57  % (9537)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (9537)Refutation not found, incomplete strategy% (9537)------------------------------
% 0.21/0.57  % (9537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (9537)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (9537)Memory used [KB]: 10618
% 0.21/0.57  % (9537)Time elapsed: 0.158 s
% 0.21/0.57  % (9537)------------------------------
% 0.21/0.57  % (9537)------------------------------
% 0.21/0.57  % (9553)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.58  % (9535)Refutation not found, incomplete strategy% (9535)------------------------------
% 0.21/0.58  % (9535)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9535)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.58  
% 0.21/0.58  % (9535)Memory used [KB]: 10746
% 0.21/0.58  % (9535)Time elapsed: 0.150 s
% 0.21/0.58  % (9535)------------------------------
% 0.21/0.58  % (9535)------------------------------
% 0.21/0.58  % (9546)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f406,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f122,f127,f132,f138,f143,f148,f157,f159,f180,f197,f207,f210,f268,f311,f327,f349,f350,f359,f369,f388,f396,f405])).
% 0.21/0.58  fof(f405,plain,(
% 0.21/0.58    spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_12 | ~spl6_35),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f404])).
% 0.21/0.58  fof(f404,plain,(
% 0.21/0.58    $false | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_12 | ~spl6_35)),
% 0.21/0.58    inference(subsumption_resolution,[],[f403,f82])).
% 0.21/0.58  fof(f82,plain,(
% 0.21/0.58    ~v1_xboole_0(sK1) | spl6_1),
% 0.21/0.58    inference(avatar_component_clause,[],[f80])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    spl6_1 <=> v1_xboole_0(sK1)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.58  fof(f403,plain,(
% 0.21/0.58    v1_xboole_0(sK1) | (spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_12 | ~spl6_35)),
% 0.21/0.58    inference(subsumption_resolution,[],[f402,f147])).
% 0.21/0.58  fof(f147,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~spl6_10),
% 0.21/0.58    inference(avatar_component_clause,[],[f145])).
% 0.21/0.58  fof(f145,plain,(
% 0.21/0.58    spl6_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.58  fof(f402,plain,(
% 0.21/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_12 | ~spl6_35)),
% 0.21/0.58    inference(subsumption_resolution,[],[f401,f137])).
% 0.21/0.58  fof(f137,plain,(
% 0.21/0.58    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl6_8),
% 0.21/0.58    inference(avatar_component_clause,[],[f135])).
% 0.21/0.58  fof(f135,plain,(
% 0.21/0.58    spl6_8 <=> v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.58  fof(f401,plain,(
% 0.21/0.58    ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_9 | spl6_12 | ~spl6_35)),
% 0.21/0.58    inference(subsumption_resolution,[],[f400,f131])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~spl6_7),
% 0.21/0.58    inference(avatar_component_clause,[],[f129])).
% 0.21/0.58  fof(f129,plain,(
% 0.21/0.58    spl6_7 <=> v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.58  fof(f400,plain,(
% 0.21/0.58    ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_4 | ~spl6_9 | spl6_12 | ~spl6_35)),
% 0.21/0.58    inference(subsumption_resolution,[],[f399,f142])).
% 0.21/0.58  fof(f142,plain,(
% 0.21/0.58    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~spl6_9),
% 0.21/0.58    inference(avatar_component_clause,[],[f140])).
% 0.21/0.58  fof(f140,plain,(
% 0.21/0.58    spl6_9 <=> v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.58  fof(f399,plain,(
% 0.21/0.58    ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_4 | spl6_12 | ~spl6_35)),
% 0.21/0.58    inference(subsumption_resolution,[],[f398,f155])).
% 0.21/0.58  fof(f155,plain,(
% 0.21/0.58    ~r1_waybel_7(sK0,sK1,sK2) | spl6_12),
% 0.21/0.58    inference(avatar_component_clause,[],[f154])).
% 0.21/0.58  fof(f154,plain,(
% 0.21/0.58    spl6_12 <=> r1_waybel_7(sK0,sK1,sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.58  fof(f398,plain,(
% 0.21/0.58    r1_waybel_7(sK0,sK1,sK2) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(sK1) | (spl6_2 | ~spl6_4 | ~spl6_35)),
% 0.21/0.58    inference(superposition,[],[f395,f117])).
% 0.21/0.58  fof(f117,plain,(
% 0.21/0.58    ( ! [X0] : (k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0 | ~v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(X0)) ) | (spl6_2 | ~spl6_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f99,f113])).
% 0.21/0.58  fof(f113,plain,(
% 0.21/0.58    l1_struct_0(sK0) | ~spl6_4),
% 0.21/0.58    inference(resolution,[],[f97,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.58  fof(f97,plain,(
% 0.21/0.58    l1_pre_topc(sK0) | ~spl6_4),
% 0.21/0.58    inference(avatar_component_clause,[],[f95])).
% 0.21/0.58  fof(f95,plain,(
% 0.21/0.58    spl6_4 <=> l1_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.58  fof(f99,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_struct_0(sK0) | v1_xboole_0(X0) | ~v1_subset_1(X0,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(X0,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),X0)) = X0) ) | spl6_2),
% 0.21/0.58    inference(resolution,[],[f87,f56])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f27])).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1 | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) | ~v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) | v1_xboole_0(X1))) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f15])).
% 0.21/0.58  fof(f15,axiom,(
% 0.21/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => k2_yellow19(X0,k3_yellow19(X0,k2_struct_0(X0),X1)) = X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_yellow19)).
% 0.21/0.58  fof(f87,plain,(
% 0.21/0.58    ~v2_struct_0(sK0) | spl6_2),
% 0.21/0.58    inference(avatar_component_clause,[],[f85])).
% 0.21/0.58  fof(f85,plain,(
% 0.21/0.58    spl6_2 <=> v2_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.58  fof(f395,plain,(
% 0.21/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | ~spl6_35),
% 0.21/0.58    inference(avatar_component_clause,[],[f393])).
% 0.21/0.58  fof(f393,plain,(
% 0.21/0.58    spl6_35 <=> r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.58  fof(f396,plain,(
% 0.21/0.58    spl6_35 | ~spl6_5 | ~spl6_11 | ~spl6_30),
% 0.21/0.58    inference(avatar_split_clause,[],[f391,f317,f150,f119,f393])).
% 0.21/0.58  fof(f119,plain,(
% 0.21/0.58    spl6_5 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.58  fof(f150,plain,(
% 0.21/0.58    spl6_11 <=> r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.58  fof(f317,plain,(
% 0.21/0.58    spl6_30 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.58  fof(f391,plain,(
% 0.21/0.58    r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | (~spl6_5 | ~spl6_11 | ~spl6_30)),
% 0.21/0.58    inference(subsumption_resolution,[],[f390,f121])).
% 0.21/0.58  fof(f121,plain,(
% 0.21/0.58    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_5),
% 0.21/0.58    inference(avatar_component_clause,[],[f119])).
% 0.21/0.58  fof(f390,plain,(
% 0.21/0.58    ~m1_subset_1(sK2,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),sK2) | (~spl6_11 | ~spl6_30)),
% 0.21/0.58    inference(resolution,[],[f152,f318])).
% 0.21/0.58  fof(f318,plain,(
% 0.21/0.58    ( ! [X0] : (~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0)) ) | ~spl6_30),
% 0.21/0.58    inference(avatar_component_clause,[],[f317])).
% 0.21/0.58  fof(f152,plain,(
% 0.21/0.58    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~spl6_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f150])).
% 0.21/0.58  fof(f388,plain,(
% 0.21/0.58    spl6_1 | spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_33),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f387])).
% 0.21/0.58  fof(f387,plain,(
% 0.21/0.58    $false | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_5 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_33)),
% 0.21/0.58    inference(subsumption_resolution,[],[f386,f121])).
% 0.21/0.58  fof(f386,plain,(
% 0.21/0.58    ~m1_subset_1(sK2,u1_struct_0(sK0)) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | spl6_11 | ~spl6_12 | ~spl6_33)),
% 0.21/0.58    inference(subsumption_resolution,[],[f385,f151])).
% 0.21/0.58  fof(f151,plain,(
% 0.21/0.58    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | spl6_11),
% 0.21/0.58    inference(avatar_component_clause,[],[f150])).
% 0.21/0.58  fof(f385,plain,(
% 0.21/0.58    r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~m1_subset_1(sK2,u1_struct_0(sK0)) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_12 | ~spl6_33)),
% 0.21/0.58    inference(resolution,[],[f376,f156])).
% 0.21/0.58  fof(f156,plain,(
% 0.21/0.58    r1_waybel_7(sK0,sK1,sK2) | ~spl6_12),
% 0.21/0.58    inference(avatar_component_clause,[],[f154])).
% 0.21/0.58  fof(f376,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_33)),
% 0.21/0.58    inference(subsumption_resolution,[],[f375,f82])).
% 0.21/0.58  fof(f375,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | v1_xboole_0(sK1)) ) | (spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_33)),
% 0.21/0.58    inference(subsumption_resolution,[],[f374,f147])).
% 0.21/0.58  fof(f374,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(sK1)) ) | (spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_33)),
% 0.21/0.58    inference(subsumption_resolution,[],[f373,f137])).
% 0.21/0.58  fof(f373,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(sK1)) ) | (spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_9 | ~spl6_33)),
% 0.21/0.58    inference(subsumption_resolution,[],[f372,f131])).
% 0.21/0.58  fof(f372,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(sK1)) ) | (spl6_2 | ~spl6_4 | ~spl6_9 | ~spl6_33)),
% 0.21/0.58    inference(subsumption_resolution,[],[f371,f142])).
% 0.21/0.58  fof(f371,plain,(
% 0.21/0.58    ( ! [X0] : (~r1_waybel_7(sK0,sK1,X0) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v1_xboole_0(sK1)) ) | (spl6_2 | ~spl6_4 | ~spl6_33)),
% 0.21/0.58    inference(superposition,[],[f348,f117])).
% 0.21/0.58  fof(f348,plain,(
% 0.21/0.58    ( ! [X1] : (~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_33),
% 0.21/0.58    inference(avatar_component_clause,[],[f347])).
% 0.21/0.58  fof(f347,plain,(
% 0.21/0.58    spl6_33 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.58  fof(f369,plain,(
% 0.21/0.58    spl6_1 | spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | spl6_14 | ~spl6_15 | spl6_32),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f368])).
% 0.21/0.58  fof(f368,plain,(
% 0.21/0.58    $false | (spl6_1 | spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | spl6_14 | ~spl6_15 | spl6_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f367,f87])).
% 0.21/0.58  fof(f367,plain,(
% 0.21/0.58    v2_struct_0(sK0) | (spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_10 | spl6_14 | ~spl6_15 | spl6_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f366,f147])).
% 0.21/0.58  fof(f366,plain,(
% 0.21/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_8 | spl6_14 | ~spl6_15 | spl6_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f365,f137])).
% 0.21/0.58  fof(f365,plain,(
% 0.21/0.58    ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_6 | ~spl6_7 | spl6_14 | ~spl6_15 | spl6_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f364,f131])).
% 0.21/0.58  fof(f364,plain,(
% 0.21/0.58    ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_6 | spl6_14 | ~spl6_15 | spl6_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f363,f82])).
% 0.21/0.58  fof(f363,plain,(
% 0.21/0.58    v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (~spl6_6 | spl6_14 | ~spl6_15 | spl6_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f362,f178])).
% 0.21/0.58  fof(f178,plain,(
% 0.21/0.58    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f177])).
% 0.21/0.58  fof(f177,plain,(
% 0.21/0.58    spl6_15 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.58  fof(f362,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (~spl6_6 | spl6_14 | spl6_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f361,f174])).
% 0.21/0.58  fof(f174,plain,(
% 0.21/0.58    ~v1_xboole_0(k2_struct_0(sK0)) | spl6_14),
% 0.21/0.58    inference(avatar_component_clause,[],[f173])).
% 0.21/0.58  fof(f173,plain,(
% 0.21/0.58    spl6_14 <=> v1_xboole_0(k2_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.58  fof(f361,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (~spl6_6 | spl6_32)),
% 0.21/0.58    inference(subsumption_resolution,[],[f360,f126])).
% 0.21/0.58  fof(f126,plain,(
% 0.21/0.58    l1_struct_0(sK0) | ~spl6_6),
% 0.21/0.58    inference(avatar_component_clause,[],[f124])).
% 0.21/0.58  fof(f124,plain,(
% 0.21/0.58    spl6_6 <=> l1_struct_0(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.58  % (9555)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.58  fof(f360,plain,(
% 0.21/0.58    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl6_32),
% 0.21/0.58    inference(resolution,[],[f326,f62])).
% 0.21/0.58  fof(f62,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v4_orders_2(k3_yellow19(X0,X1,X2)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f12])).
% 0.21/0.58  fof(f12,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & v4_orders_2(k3_yellow19(X0,X1,X2)) & v3_orders_2(k3_yellow19(X0,X1,X2)) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_yellow19)).
% 0.21/0.58  fof(f326,plain,(
% 0.21/0.58    ~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl6_32),
% 0.21/0.58    inference(avatar_component_clause,[],[f324])).
% 0.21/0.58  fof(f324,plain,(
% 0.21/0.58    spl6_32 <=> v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).
% 0.21/0.58  fof(f359,plain,(
% 0.21/0.58    spl6_2 | ~spl6_6 | ~spl6_29),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f358])).
% 0.21/0.58  fof(f358,plain,(
% 0.21/0.58    $false | (spl6_2 | ~spl6_6 | ~spl6_29)),
% 0.21/0.58    inference(subsumption_resolution,[],[f357,f87])).
% 0.21/0.58  fof(f357,plain,(
% 0.21/0.58    v2_struct_0(sK0) | (~spl6_6 | ~spl6_29)),
% 0.21/0.58    inference(subsumption_resolution,[],[f355,f126])).
% 0.21/0.58  fof(f355,plain,(
% 0.21/0.58    ~l1_struct_0(sK0) | v2_struct_0(sK0) | ~spl6_29),
% 0.21/0.58    inference(resolution,[],[f310,f55])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.58  fof(f310,plain,(
% 0.21/0.58    v1_xboole_0(u1_struct_0(sK0)) | ~spl6_29),
% 0.21/0.58    inference(avatar_component_clause,[],[f308])).
% 0.21/0.58  fof(f308,plain,(
% 0.21/0.58    spl6_29 <=> v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.58  fof(f350,plain,(
% 0.21/0.58    spl6_14 | spl6_1 | spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_15 | spl6_31),
% 0.21/0.58    inference(avatar_split_clause,[],[f345,f320,f177,f145,f140,f135,f129,f124,f85,f80,f173])).
% 0.21/0.58  fof(f320,plain,(
% 0.21/0.58    spl6_31 <=> v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.58  fof(f345,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | (spl6_1 | spl6_2 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_15 | spl6_31)),
% 0.21/0.58    inference(subsumption_resolution,[],[f344,f87])).
% 0.21/0.58  fof(f344,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | v2_struct_0(sK0) | (spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_10 | ~spl6_15 | spl6_31)),
% 0.21/0.58    inference(subsumption_resolution,[],[f343,f147])).
% 0.21/0.58  fof(f343,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_15 | spl6_31)),
% 0.21/0.58    inference(subsumption_resolution,[],[f342,f137])).
% 0.21/0.58  fof(f342,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_15 | spl6_31)),
% 0.21/0.58    inference(subsumption_resolution,[],[f341,f131])).
% 0.21/0.58  fof(f341,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_6 | ~spl6_9 | ~spl6_15 | spl6_31)),
% 0.21/0.58    inference(subsumption_resolution,[],[f340,f142])).
% 0.21/0.58  fof(f340,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (spl6_1 | ~spl6_6 | ~spl6_15 | spl6_31)),
% 0.21/0.58    inference(subsumption_resolution,[],[f339,f82])).
% 0.21/0.58  fof(f339,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (~spl6_6 | ~spl6_15 | spl6_31)),
% 0.21/0.58    inference(subsumption_resolution,[],[f329,f178])).
% 0.21/0.58  fof(f329,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | (~spl6_6 | spl6_31)),
% 0.21/0.58    inference(subsumption_resolution,[],[f328,f126])).
% 0.21/0.58  fof(f328,plain,(
% 0.21/0.58    ~l1_struct_0(sK0) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | v2_struct_0(sK0) | spl6_31),
% 0.21/0.58    inference(resolution,[],[f322,f69])).
% 0.21/0.58  fof(f69,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v7_waybel_0(k3_yellow19(X0,X1,X2)) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | v2_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & v1_subset_1(X2,u1_struct_0(k3_yellow_1(X1))) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (v7_waybel_0(k3_yellow19(X0,X1,X2)) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_yellow19)).
% 0.21/0.58  fof(f322,plain,(
% 0.21/0.58    ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl6_31),
% 0.21/0.58    inference(avatar_component_clause,[],[f320])).
% 0.21/0.58  fof(f349,plain,(
% 0.21/0.58    spl6_33 | ~spl6_31 | ~spl6_32 | spl6_2 | ~spl6_3 | ~spl6_4 | spl6_13 | ~spl6_18),
% 0.21/0.58    inference(avatar_split_clause,[],[f315,f204,f169,f95,f90,f85,f324,f320,f347])).
% 0.21/0.58  fof(f90,plain,(
% 0.21/0.58    spl6_3 <=> v2_pre_topc(sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.58  fof(f169,plain,(
% 0.21/0.58    spl6_13 <=> v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.21/0.58  fof(f204,plain,(
% 0.21/0.58    spl6_18 <=> l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0)),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.21/0.58  fof(f315,plain,(
% 0.21/0.58    ( ! [X1] : (~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | spl6_13 | ~spl6_18)),
% 0.21/0.58    inference(subsumption_resolution,[],[f313,f171])).
% 0.21/0.58  fof(f171,plain,(
% 0.21/0.58    ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | spl6_13),
% 0.21/0.58    inference(avatar_component_clause,[],[f169])).
% 0.21/0.58  fof(f313,plain,(
% 0.21/0.58    ( ! [X1] : (~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X1) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X1)) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_18)),
% 0.21/0.58    inference(resolution,[],[f206,f110])).
% 0.21/0.58  fof(f110,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~l1_waybel_0(X0,sK0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | v2_struct_0(X0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1) | r3_waybel_9(sK0,X0,X1)) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f109,f97])).
% 0.21/0.58  fof(f109,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1) | r3_waybel_9(sK0,X0,X1)) ) | (spl6_2 | ~spl6_3)),
% 0.21/0.58    inference(subsumption_resolution,[],[f107,f87])).
% 0.21/0.58  fof(f107,plain,(
% 0.21/0.58    ( ! [X0,X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X0) | ~v4_orders_2(X0) | ~v7_waybel_0(X0) | ~l1_waybel_0(X0,sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r1_waybel_7(sK0,k2_yellow19(sK0,X0),X1) | r3_waybel_9(sK0,X0,X1)) ) | ~spl6_3),
% 0.21/0.58    inference(resolution,[],[f92,f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | r3_waybel_9(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (! [X2] : ((r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | (~l1_waybel_0(X1,X0) | ~v7_waybel_0(X1) | ~v4_orders_2(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_waybel_0(X1,X0) & v7_waybel_0(X1) & v4_orders_2(X1) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,X1,X2) <=> r1_waybel_7(X0,k2_yellow19(X0,X1),X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_yellow19)).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    v2_pre_topc(sK0) | ~spl6_3),
% 0.21/0.58    inference(avatar_component_clause,[],[f90])).
% 0.21/0.58  fof(f206,plain,(
% 0.21/0.58    l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | ~spl6_18),
% 0.21/0.58    inference(avatar_component_clause,[],[f204])).
% 0.21/0.58  fof(f327,plain,(
% 0.21/0.58    spl6_30 | ~spl6_31 | ~spl6_32 | spl6_2 | ~spl6_3 | ~spl6_4 | spl6_13 | ~spl6_18),
% 0.21/0.58    inference(avatar_split_clause,[],[f314,f204,f169,f95,f90,f85,f324,f320,f317])).
% 0.21/0.58  fof(f314,plain,(
% 0.21/0.58    ( ! [X0] : (~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | spl6_13 | ~spl6_18)),
% 0.21/0.58    inference(subsumption_resolution,[],[f312,f171])).
% 0.21/0.58  fof(f312,plain,(
% 0.21/0.58    ( ! [X0] : (~v4_orders_2(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~v7_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1)),X0) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),X0)) ) | (spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_18)),
% 0.21/0.58    inference(resolution,[],[f206,f112])).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    ( ! [X2,X3] : (~l1_waybel_0(X2,sK0) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | v2_struct_0(X2) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3) | ~r3_waybel_9(sK0,X2,X3)) ) | (spl6_2 | ~spl6_3 | ~spl6_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f111,f97])).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    ( ! [X2,X3] : (~l1_pre_topc(sK0) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3) | ~r3_waybel_9(sK0,X2,X3)) ) | (spl6_2 | ~spl6_3)),
% 0.21/0.58    inference(subsumption_resolution,[],[f108,f87])).
% 0.21/0.58  fof(f108,plain,(
% 0.21/0.58    ( ! [X2,X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(X2) | ~v4_orders_2(X2) | ~v7_waybel_0(X2) | ~l1_waybel_0(X2,sK0) | ~m1_subset_1(X3,u1_struct_0(sK0)) | r1_waybel_7(sK0,k2_yellow19(sK0,X2),X3) | ~r3_waybel_9(sK0,X2,X3)) ) | ~spl6_3),
% 0.21/0.58    inference(resolution,[],[f92,f54])).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v4_orders_2(X1) | ~v7_waybel_0(X1) | ~l1_waybel_0(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | r1_waybel_7(X0,k2_yellow19(X0,X1),X2) | ~r3_waybel_9(X0,X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f311,plain,(
% 0.21/0.58    spl6_29 | ~spl6_14 | ~spl6_25),
% 0.21/0.58    inference(avatar_split_clause,[],[f296,f265,f173,f308])).
% 0.21/0.58  fof(f265,plain,(
% 0.21/0.58    spl6_25 <=> u1_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.21/0.58  fof(f296,plain,(
% 0.21/0.58    v1_xboole_0(u1_struct_0(sK0)) | (~spl6_14 | ~spl6_25)),
% 0.21/0.58    inference(superposition,[],[f228,f267])).
% 0.21/0.58  fof(f267,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) | ~spl6_25),
% 0.21/0.58    inference(avatar_component_clause,[],[f265])).
% 0.21/0.58  fof(f228,plain,(
% 0.21/0.58    ( ! [X0] : (v1_xboole_0(k4_xboole_0(k2_struct_0(sK0),X0))) ) | ~spl6_14),
% 0.21/0.58    inference(resolution,[],[f222,f57])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ( ! [X0] : (r2_hidden(sK3(X0),X0) | v1_xboole_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.21/0.58  fof(f222,plain,(
% 0.21/0.58    ( ! [X4,X5] : (~r2_hidden(X4,k4_xboole_0(k2_struct_0(sK0),X5))) ) | ~spl6_14),
% 0.21/0.58    inference(resolution,[],[f214,f77])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,k4_xboole_0(X0,X1))) )),
% 0.21/0.58    inference(equality_resolution,[],[f74])).
% 0.21/0.58  fof(f74,plain,(
% 0.21/0.58    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k4_xboole_0(X0,X1) != X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (k4_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (~r2_hidden(X3,X1) & r2_hidden(X3,X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).
% 0.21/0.58  fof(f214,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~sP5(X0,X1,k2_struct_0(sK0))) ) | ~spl6_14),
% 0.21/0.58    inference(resolution,[],[f211,f71])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ( ! [X0,X3,X1] : (r2_hidden(X3,X0) | ~sP5(X3,X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f2])).
% 0.21/0.58  fof(f211,plain,(
% 0.21/0.58    ( ! [X0] : (~r2_hidden(X0,k2_struct_0(sK0))) ) | ~spl6_14),
% 0.21/0.58    inference(resolution,[],[f175,f58])).
% 0.21/0.58  fof(f58,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v1_xboole_0(X0) | ~r2_hidden(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f1])).
% 0.21/0.58  fof(f175,plain,(
% 0.21/0.58    v1_xboole_0(k2_struct_0(sK0)) | ~spl6_14),
% 0.21/0.58    inference(avatar_component_clause,[],[f173])).
% 0.21/0.58  fof(f268,plain,(
% 0.21/0.58    spl6_25 | ~spl6_15 | ~spl6_16),
% 0.21/0.58    inference(avatar_split_clause,[],[f219,f194,f177,f265])).
% 0.21/0.58  fof(f194,plain,(
% 0.21/0.58    spl6_16 <=> u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0)))),
% 0.21/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.21/0.58  fof(f219,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) | (~spl6_15 | ~spl6_16)),
% 0.21/0.58    inference(subsumption_resolution,[],[f216,f178])).
% 0.21/0.58  fof(f216,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k4_xboole_0(k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_16),
% 0.21/0.58    inference(superposition,[],[f196,f59])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.58  fof(f196,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) | ~spl6_16),
% 0.21/0.58    inference(avatar_component_clause,[],[f194])).
% 0.21/0.58  fof(f210,plain,(
% 0.21/0.58    ~spl6_6 | spl6_15),
% 0.21/0.58    inference(avatar_contradiction_clause,[],[f209])).
% 0.21/0.58  fof(f209,plain,(
% 0.21/0.58    $false | (~spl6_6 | spl6_15)),
% 0.21/0.58    inference(subsumption_resolution,[],[f208,f126])).
% 0.21/0.58  fof(f208,plain,(
% 0.21/0.58    ~l1_struct_0(sK0) | spl6_15),
% 0.21/0.58    inference(resolution,[],[f179,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.58  fof(f179,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | spl6_15),
% 0.21/0.58    inference(avatar_component_clause,[],[f177])).
% 0.21/0.58  fof(f207,plain,(
% 0.21/0.58    spl6_18 | spl6_14 | ~spl6_15 | spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f184,f145,f135,f129,f95,f85,f80,f177,f173,f204])).
% 0.21/0.58  fof(f184,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_10)),
% 0.21/0.58    inference(subsumption_resolution,[],[f183,f147])).
% 0.21/0.58  fof(f183,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8)),
% 0.21/0.58    inference(subsumption_resolution,[],[f182,f131])).
% 0.21/0.58  fof(f182,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_8)),
% 0.21/0.58    inference(subsumption_resolution,[],[f181,f82])).
% 0.21/0.58  fof(f181,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | l1_waybel_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK0) | (spl6_2 | ~spl6_4 | ~spl6_8)),
% 0.21/0.58    inference(resolution,[],[f114,f137])).
% 0.21/0.58  fof(f114,plain,(
% 0.21/0.58    ( ! [X10,X9] : (~v13_waybel_0(X10,k3_yellow_1(X9)) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X10) | ~v2_waybel_0(X10,k3_yellow_1(X9)) | v1_xboole_0(X9) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9)))) | l1_waybel_0(k3_yellow19(sK0,X9,X10),sK0)) ) | (spl6_2 | ~spl6_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f104,f113])).
% 0.21/0.58  fof(f104,plain,(
% 0.21/0.58    ( ! [X10,X9] : (~l1_struct_0(sK0) | v1_xboole_0(X9) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X10) | ~v2_waybel_0(X10,k3_yellow_1(X9)) | ~v13_waybel_0(X10,k3_yellow_1(X9)) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X9)))) | l1_waybel_0(k3_yellow19(sK0,X9,X10),sK0)) ) | spl6_2),
% 0.21/0.58    inference(resolution,[],[f87,f66])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | l1_waybel_0(k3_yellow19(X0,X1,X2),X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    ! [X0,X1,X2] : ((l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,axiom,(
% 0.21/0.58    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) & v13_waybel_0(X2,k3_yellow_1(X1)) & v2_waybel_0(X2,k3_yellow_1(X1)) & ~v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1) & l1_struct_0(X0) & ~v2_struct_0(X0)) => (l1_waybel_0(k3_yellow19(X0,X1,X2),X0) & v6_waybel_0(k3_yellow19(X0,X1,X2),X0) & ~v2_struct_0(k3_yellow19(X0,X1,X2))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow19)).
% 0.21/0.58  fof(f197,plain,(
% 0.21/0.58    spl6_16 | ~spl6_6),
% 0.21/0.58    inference(avatar_split_clause,[],[f162,f124,f194])).
% 0.21/0.58  fof(f162,plain,(
% 0.21/0.58    u1_struct_0(sK0) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),u1_struct_0(sK0))) | ~spl6_6),
% 0.21/0.58    inference(forward_demodulation,[],[f160,f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.58    inference(cnf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.58  fof(f160,plain,(
% 0.21/0.58    k2_subset_1(u1_struct_0(sK0)) = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_subset_1(u1_struct_0(sK0)))) | ~spl6_6),
% 0.21/0.58    inference(resolution,[],[f133,f48])).
% 0.21/0.58  fof(f48,plain,(
% 0.21/0.58    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.58  fof(f133,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0)) = X0) ) | ~spl6_6),
% 0.21/0.58    inference(resolution,[],[f126,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) )),
% 0.21/0.58    inference(cnf_transformation,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_pre_topc)).
% 0.21/0.58  fof(f180,plain,(
% 0.21/0.58    ~spl6_13 | spl6_14 | ~spl6_15 | spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f167,f145,f135,f129,f95,f85,f80,f177,f173,f169])).
% 0.21/0.58  fof(f167,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8 | ~spl6_10)),
% 0.21/0.58    inference(subsumption_resolution,[],[f166,f147])).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_7 | ~spl6_8)),
% 0.21/0.58    inference(subsumption_resolution,[],[f165,f131])).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (spl6_1 | spl6_2 | ~spl6_4 | ~spl6_8)),
% 0.21/0.58    inference(subsumption_resolution,[],[f164,f82])).
% 0.21/0.58  fof(f164,plain,(
% 0.21/0.58    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(sK1) | ~v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0))) | v1_xboole_0(k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))) | ~v2_struct_0(k3_yellow19(sK0,k2_struct_0(sK0),sK1)) | (spl6_2 | ~spl6_4 | ~spl6_8)),
% 0.21/0.58    inference(resolution,[],[f116,f137])).
% 0.21/0.58  fof(f116,plain,(
% 0.21/0.58    ( ! [X2,X1] : (~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v2_struct_0(k3_yellow19(sK0,X1,X2))) ) | (spl6_2 | ~spl6_4)),
% 0.21/0.58    inference(subsumption_resolution,[],[f100,f113])).
% 0.21/0.58  fof(f100,plain,(
% 0.21/0.58    ( ! [X2,X1] : (~l1_struct_0(sK0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v2_struct_0(k3_yellow19(sK0,X1,X2))) ) | spl6_2),
% 0.21/0.58    inference(resolution,[],[f87,f60])).
% 0.21/0.58  fof(f60,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X2) | ~v2_waybel_0(X2,k3_yellow_1(X1)) | ~v13_waybel_0(X2,k3_yellow_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(X1)))) | ~v2_struct_0(k3_yellow19(X0,X1,X2))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f31])).
% 0.21/0.58  fof(f159,plain,(
% 0.21/0.58    ~spl6_11 | ~spl6_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f158,f154,f150])).
% 0.21/0.58  fof(f158,plain,(
% 0.21/0.58    ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2) | ~spl6_12),
% 0.21/0.58    inference(subsumption_resolution,[],[f37,f156])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ~r1_waybel_7(sK0,sK1,sK2) | ~r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : (? [X2] : ((r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <~> r1_waybel_7(X0,X1,X2)) & m1_subset_1(X2,u1_struct_0(X0))) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f17])).
% 0.21/0.58  fof(f17,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.58    inference(negated_conjecture,[],[f16])).
% 0.21/0.58  fof(f16,conjecture,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(X1,k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(X1,u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (r3_waybel_9(X0,k3_yellow19(X0,k2_struct_0(X0),X1),X2) <=> r1_waybel_7(X0,X1,X2)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_yellow19)).
% 0.21/0.58  fof(f157,plain,(
% 0.21/0.58    spl6_11 | spl6_12),
% 0.21/0.58    inference(avatar_split_clause,[],[f36,f154,f150])).
% 0.21/0.58  fof(f36,plain,(
% 0.21/0.58    r1_waybel_7(sK0,sK1,sK2) | r3_waybel_9(sK0,k3_yellow19(sK0,k2_struct_0(sK0),sK1),sK2)),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f148,plain,(
% 0.21/0.58    spl6_10),
% 0.21/0.58    inference(avatar_split_clause,[],[f43,f145])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK0)))))),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f143,plain,(
% 0.21/0.58    spl6_9),
% 0.21/0.58    inference(avatar_split_clause,[],[f40,f140])).
% 0.21/0.58  fof(f40,plain,(
% 0.21/0.58    v1_subset_1(sK1,u1_struct_0(k3_yellow_1(k2_struct_0(sK0))))),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f138,plain,(
% 0.21/0.58    spl6_8),
% 0.21/0.58    inference(avatar_split_clause,[],[f42,f135])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    v13_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f132,plain,(
% 0.21/0.58    spl6_7),
% 0.21/0.58    inference(avatar_split_clause,[],[f41,f129])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    v2_waybel_0(sK1,k3_yellow_1(k2_struct_0(sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f127,plain,(
% 0.21/0.58    spl6_6 | ~spl6_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f113,f95,f124])).
% 0.21/0.58  fof(f122,plain,(
% 0.21/0.58    spl6_5),
% 0.21/0.58    inference(avatar_split_clause,[],[f38,f119])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f98,plain,(
% 0.21/0.58    spl6_4),
% 0.21/0.58    inference(avatar_split_clause,[],[f46,f95])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    l1_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    spl6_3),
% 0.21/0.58    inference(avatar_split_clause,[],[f45,f90])).
% 0.21/0.58  fof(f45,plain,(
% 0.21/0.58    v2_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f88,plain,(
% 0.21/0.58    ~spl6_2),
% 0.21/0.58    inference(avatar_split_clause,[],[f44,f85])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ~v2_struct_0(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f83,plain,(
% 0.21/0.58    ~spl6_1),
% 0.21/0.58    inference(avatar_split_clause,[],[f39,f80])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ~v1_xboole_0(sK1)),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (9546)------------------------------
% 0.21/0.58  % (9546)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (9546)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (9546)Memory used [KB]: 11001
% 0.21/0.58  % (9546)Time elapsed: 0.173 s
% 0.21/0.58  % (9546)------------------------------
% 0.21/0.58  % (9546)------------------------------
% 0.21/0.59  % (9517)Success in time 0.215 s
%------------------------------------------------------------------------------
