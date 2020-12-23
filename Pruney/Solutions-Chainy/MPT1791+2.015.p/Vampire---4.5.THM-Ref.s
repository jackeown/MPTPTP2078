%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:23 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 452 expanded)
%              Number of leaves         :   36 ( 184 expanded)
%              Depth                    :   13
%              Number of atoms          :  898 (1781 expanded)
%              Number of equality atoms :   88 ( 229 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f380,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f101,f103,f140,f162,f177,f183,f187,f204,f211,f215,f220,f258,f263,f279,f288,f295,f302,f310,f329,f331,f347,f367,f379])).

fof(f379,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_5
    | ~ spl2_27 ),
    inference(avatar_contradiction_clause,[],[f378])).

fof(f378,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_5
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f377,f85])).

fof(f85,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f377,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | spl2_5
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f376,f90])).

fof(f90,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f88,plain,
    ( spl2_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f376,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_5
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f374,f95])).

fof(f95,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | spl2_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl2_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f374,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_27 ),
    inference(resolution,[],[f309,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) )
            & ( r2_hidden(X1,u1_pre_topc(X0))
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f309,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl2_27 ),
    inference(avatar_component_clause,[],[f307])).

fof(f307,plain,
    ( spl2_27
  <=> r2_hidden(sK1,u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).

fof(f367,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_27
    | ~ spl2_28 ),
    inference(avatar_contradiction_clause,[],[f366])).

fof(f366,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_27
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f365,f75])).

fof(f75,plain,
    ( ~ v2_struct_0(sK0)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl2_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f365,plain,
    ( v2_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_27
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f364,f80])).

fof(f80,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl2_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f364,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_3
    | ~ spl2_4
    | spl2_27
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f363,f85])).

fof(f363,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_4
    | spl2_27
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f362,f90])).

fof(f362,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl2_27
    | ~ spl2_28 ),
    inference(subsumption_resolution,[],[f360,f308])).

fof(f308,plain,
    ( ~ r2_hidden(sK1,u1_pre_topc(sK0))
    | spl2_27 ),
    inference(avatar_component_clause,[],[f307])).

fof(f360,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_28 ),
    inference(trivial_inequality_removal,[],[f358])).

fof(f358,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_28 ),
    inference(superposition,[],[f58,f328])).

fof(f328,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_28 ),
    inference(avatar_component_clause,[],[f326])).

fof(f326,plain,
    ( spl2_28
  <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).

fof(f58,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X1,u1_pre_topc(X0))
              | u1_pre_topc(X0) != k5_tmap_1(X0,X1) )
            & ( u1_pre_topc(X0) = k5_tmap_1(X0,X1)
              | ~ r2_hidden(X1,u1_pre_topc(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f347,plain,
    ( spl2_28
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(avatar_split_clause,[],[f344,f270,f88,f83,f78,f73,f326])).

fof(f270,plain,
    ( spl2_23
  <=> r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f344,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f343,f90])).

fof(f343,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f342,f75])).

fof(f342,plain,
    ( v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f341,f80])).

fof(f341,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_23 ),
    inference(subsumption_resolution,[],[f339,f85])).

fof(f339,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ spl2_23 ),
    inference(resolution,[],[f271,f121])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k5_tmap_1(X1,X0),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | u1_pre_topc(X1) = k5_tmap_1(X1,X0) ) ),
    inference(resolution,[],[f53,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f53,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_tmap_1)).

fof(f271,plain,
    ( r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | ~ spl2_23 ),
    inference(avatar_component_clause,[],[f270])).

fof(f331,plain,
    ( spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_6
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(avatar_contradiction_clause,[],[f330])).

fof(f330,plain,
    ( $false
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | spl2_6
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f319,f99])).

fof(f99,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | spl2_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl2_6
  <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f319,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_21
    | ~ spl2_27 ),
    inference(backward_demodulation,[],[f262,f316])).

fof(f316,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f315,f75])).

fof(f315,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | v2_struct_0(sK0)
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f314,f80])).

fof(f314,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f313,f85])).

fof(f313,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_4
    | ~ spl2_27 ),
    inference(subsumption_resolution,[],[f311,f90])).

fof(f311,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl2_27 ),
    inference(resolution,[],[f309,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f262,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f260])).

fof(f260,plain,
    ( spl2_21
  <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f329,plain,
    ( spl2_28
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_27 ),
    inference(avatar_split_clause,[],[f316,f307,f88,f83,f78,f73,f326])).

fof(f310,plain,
    ( spl2_27
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f305,f94,f88,f83,f307])).

fof(f305,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f304,f85])).

fof(f304,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f303,f90])).

fof(f303,plain,
    ( r2_hidden(sK1,u1_pre_topc(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(resolution,[],[f96,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f302,plain,
    ( ~ spl2_19
    | ~ spl2_20
    | spl2_22
    | ~ spl2_26 ),
    inference(avatar_contradiction_clause,[],[f301])).

fof(f301,plain,
    ( $false
    | ~ spl2_19
    | ~ spl2_20
    | spl2_22
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f300,f267])).

fof(f267,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | spl2_22 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl2_22
  <=> v1_tops_2(k5_tmap_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f300,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | ~ spl2_19
    | ~ spl2_20
    | ~ spl2_26 ),
    inference(subsumption_resolution,[],[f298,f219])).

fof(f219,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_19 ),
    inference(avatar_component_clause,[],[f217])).

fof(f217,plain,
    ( spl2_19
  <=> m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).

fof(f298,plain,
    ( ~ m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | ~ spl2_20
    | ~ spl2_26 ),
    inference(resolution,[],[f294,f257])).

fof(f257,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(X0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X0,sK0) )
    | ~ spl2_20 ),
    inference(avatar_component_clause,[],[f256])).

fof(f256,plain,
    ( spl2_20
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X0,k6_tmap_1(sK0,sK1))
        | v1_tops_2(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).

fof(f294,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl2_26 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl2_26
  <=> v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f295,plain,
    ( spl2_26
    | ~ spl2_19
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f290,f286,f217,f292])).

fof(f286,plain,
    ( spl2_25
  <=> ! [X3] :
        ( ~ r1_tarski(X3,k5_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X3,k6_tmap_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f290,plain,
    ( v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl2_19
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f289,f70])).

fof(f70,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f289,plain,
    ( ~ r1_tarski(k5_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1))
    | v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ spl2_19
    | ~ spl2_25 ),
    inference(resolution,[],[f287,f219])).

fof(f287,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X3,k5_tmap_1(sK0,sK1))
        | v1_tops_2(X3,k6_tmap_1(sK0,sK1)) )
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f286])).

fof(f288,plain,
    ( spl2_25
    | ~ spl2_12
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f284,f208,f180,f159,f286])).

fof(f159,plain,
    ( spl2_12
  <=> l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f180,plain,
    ( spl2_14
  <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f208,plain,
    ( spl2_17
  <=> u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f284,plain,
    ( ! [X3] :
        ( ~ r1_tarski(X3,k5_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v1_tops_2(X3,k6_tmap_1(sK0,sK1)) )
    | ~ spl2_12
    | ~ spl2_14
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f199,f210])).

fof(f210,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1)
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f208])).

fof(f199,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X3,u1_pre_topc(k6_tmap_1(sK0,sK1)))
        | v1_tops_2(X3,k6_tmap_1(sK0,sK1)) )
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f191,f161])).

fof(f161,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f159])).

fof(f191,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ r1_tarski(X3,u1_pre_topc(k6_tmap_1(sK0,sK1)))
        | v1_tops_2(X3,k6_tmap_1(sK0,sK1))
        | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) )
    | ~ spl2_14 ),
    inference(superposition,[],[f52,f182])).

fof(f182,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f180])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_2(X1,X0)
              | ~ r1_tarski(X1,u1_pre_topc(X0)) )
            & ( r1_tarski(X1,u1_pre_topc(X0))
              | ~ v1_tops_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f279,plain,
    ( ~ spl2_22
    | ~ spl2_3
    | ~ spl2_19
    | spl2_23 ),
    inference(avatar_split_clause,[],[f278,f270,f217,f83,f266])).

fof(f278,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_19
    | spl2_23 ),
    inference(subsumption_resolution,[],[f254,f272])).

fof(f272,plain,
    ( ~ r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f270])).

fof(f254,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | ~ spl2_3
    | ~ spl2_19 ),
    inference(subsumption_resolution,[],[f243,f85])).

fof(f243,plain,
    ( ~ v1_tops_2(k5_tmap_1(sK0,sK1),sK0)
    | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_19 ),
    inference(resolution,[],[f219,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ v1_tops_2(X1,X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f263,plain,
    ( spl2_21
    | ~ spl2_4
    | ~ spl2_18 ),
    inference(avatar_split_clause,[],[f221,f213,f88,f260])).

fof(f213,plain,
    ( spl2_18
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).

fof(f221,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_18 ),
    inference(resolution,[],[f214,f90])).

fof(f214,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) )
    | ~ spl2_18 ),
    inference(avatar_component_clause,[],[f213])).

fof(f258,plain,
    ( spl2_20
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f239,f180,f98,f83,f78,f73,f256])).

fof(f239,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | ~ v1_tops_2(X0,k6_tmap_1(sK0,sK1))
        | v1_tops_2(X0,sK0) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6
    | ~ spl2_14 ),
    inference(forward_demodulation,[],[f167,f182])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ v1_tops_2(X0,k6_tmap_1(sK0,sK1))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | v1_tops_2(X0,sK0) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f166,f100])).

fof(f100,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f166,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))))
        | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_tops_2(X0,sK0) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_6 ),
    inference(forward_demodulation,[],[f165,f100])).

fof(f165,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_tops_2(X0,sK0) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f164,f75])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_tops_2(X0,sK0)
        | v2_struct_0(sK0) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f163,f80])).

fof(f163,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))))))
        | ~ v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
        | v1_tops_2(X0,sK0)
        | ~ v2_pre_topc(sK0)
        | v2_struct_0(sK0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f61,f85])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
      | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | v1_tops_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
              & v1_tops_2(X1,X0) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            | ~ v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
          & ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
              & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
            | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            | ~ v1_tops_2(X1,X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) )
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
          ( ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
            & v1_tops_2(X1,X0) )
        <=> ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))
            & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).

fof(f220,plain,
    ( spl2_19
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f206,f202,f88,f217])).

fof(f202,plain,
    ( spl2_16
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f206,plain,
    ( m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_4
    | ~ spl2_16 ),
    inference(resolution,[],[f203,f90])).

fof(f203,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f202])).

fof(f215,plain,
    ( spl2_18
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f143,f83,f78,f73,f213])).

fof(f143,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f142,f75])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f141,f85])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f54,f80])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).

fof(f211,plain,
    ( spl2_17
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f205,f185,f88,f208])).

fof(f185,plain,
    ( spl2_15
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f205,plain,
    ( u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1)
    | ~ spl2_4
    | ~ spl2_15 ),
    inference(resolution,[],[f186,f90])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) )
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f185])).

fof(f204,plain,
    ( spl2_16
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f136,f83,f78,f73,f202])).

fof(f136,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f135,f75])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f134,f85])).

fof(f134,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
        | v2_struct_0(sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f63,f80])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).

fof(f187,plain,
    ( spl2_15
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f133,f83,f78,f73,f185])).

fof(f133,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f132,f75])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f131,f85])).

fof(f131,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f56,f80])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f183,plain,
    ( spl2_14
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(avatar_split_clause,[],[f178,f175,f88,f180])).

fof(f175,plain,
    ( spl2_13
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f178,plain,
    ( u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_13 ),
    inference(resolution,[],[f176,f90])).

fof(f176,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) )
    | ~ spl2_13 ),
    inference(avatar_component_clause,[],[f175])).

fof(f177,plain,
    ( spl2_13
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f125,f83,f78,f73,f175])).

fof(f125,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f124,f75])).

fof(f124,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f123,f85])).

fof(f123,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f55,f80])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f162,plain,
    ( spl2_12
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f157,f138,f88,f159])).

fof(f138,plain,
    ( spl2_10
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k6_tmap_1(sK0,X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f157,plain,
    ( l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ spl2_4
    | ~ spl2_10 ),
    inference(resolution,[],[f139,f90])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k6_tmap_1(sK0,X0)) )
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl2_10
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f116,f83,f78,f73,f138])).

fof(f116,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k6_tmap_1(sK0,X0)) )
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f115,f75])).

fof(f115,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | l1_pre_topc(k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_2
    | ~ spl2_3 ),
    inference(subsumption_resolution,[],[f114,f85])).

fof(f114,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | l1_pre_topc(k6_tmap_1(sK0,X0))
        | v2_struct_0(sK0) )
    | ~ spl2_2 ),
    inference(resolution,[],[f66,f80])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f103,plain,
    ( ~ spl2_5
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f102,f98,f94])).

fof(f102,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f48,f100])).

fof(f48,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
    ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).

fof(f33,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,
    ( ? [X1] :
        ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f101,plain,
    ( spl2_5
    | spl2_6 ),
    inference(avatar_split_clause,[],[f47,f98,f94])).

fof(f47,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f46,f88])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f35])).

fof(f86,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f45,f83])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f81,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f44,f78])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f35])).

fof(f76,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f43,f73])).

fof(f43,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 20:54:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.48  % (23783)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.49  % (23777)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.50  % (23785)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (23776)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.50  % (23777)Refutation not found, incomplete strategy% (23777)------------------------------
% 0.22/0.50  % (23777)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23777)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (23777)Memory used [KB]: 6140
% 0.22/0.50  % (23777)Time elapsed: 0.085 s
% 0.22/0.50  % (23777)------------------------------
% 0.22/0.50  % (23777)------------------------------
% 0.22/0.50  % (23783)Refutation not found, incomplete strategy% (23783)------------------------------
% 0.22/0.50  % (23783)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (23783)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (23783)Memory used [KB]: 10618
% 0.22/0.50  % (23783)Time elapsed: 0.091 s
% 0.22/0.50  % (23783)------------------------------
% 0.22/0.50  % (23783)------------------------------
% 0.22/0.51  % (23785)Refutation not found, incomplete strategy% (23785)------------------------------
% 0.22/0.51  % (23785)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (23785)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (23785)Memory used [KB]: 6140
% 0.22/0.51  % (23785)Time elapsed: 0.099 s
% 0.22/0.51  % (23785)------------------------------
% 0.22/0.51  % (23785)------------------------------
% 0.22/0.51  % (23795)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.22/0.51  % (23774)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (23772)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.51  % (23787)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.51  % (23792)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.22/0.51  % (23791)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.22/0.51  % (23775)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.51  % (23774)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % SZS output start Proof for theBenchmark
% 0.22/0.51  fof(f380,plain,(
% 0.22/0.51    $false),
% 0.22/0.51    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f101,f103,f140,f162,f177,f183,f187,f204,f211,f215,f220,f258,f263,f279,f288,f295,f302,f310,f329,f331,f347,f367,f379])).
% 0.22/0.51  fof(f379,plain,(
% 0.22/0.51    ~spl2_3 | ~spl2_4 | spl2_5 | ~spl2_27),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f378])).
% 0.22/0.51  fof(f378,plain,(
% 0.22/0.51    $false | (~spl2_3 | ~spl2_4 | spl2_5 | ~spl2_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f377,f85])).
% 0.22/0.51  fof(f85,plain,(
% 0.22/0.51    l1_pre_topc(sK0) | ~spl2_3),
% 0.22/0.51    inference(avatar_component_clause,[],[f83])).
% 0.22/0.51  fof(f83,plain,(
% 0.22/0.51    spl2_3 <=> l1_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.51  fof(f377,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | (~spl2_4 | spl2_5 | ~spl2_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f376,f90])).
% 0.22/0.51  fof(f90,plain,(
% 0.22/0.51    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_4),
% 0.22/0.51    inference(avatar_component_clause,[],[f88])).
% 0.22/0.51  fof(f88,plain,(
% 0.22/0.51    spl2_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.51  fof(f376,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_5 | ~spl2_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f374,f95])).
% 0.22/0.51  fof(f95,plain,(
% 0.22/0.51    ~v3_pre_topc(sK1,sK0) | spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f94])).
% 0.22/0.51  fof(f94,plain,(
% 0.22/0.51    spl2_5 <=> v3_pre_topc(sK1,sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 0.22/0.51  fof(f374,plain,(
% 0.22/0.51    v3_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_27),
% 0.22/0.51    inference(resolution,[],[f309,f50])).
% 0.22/0.51  fof(f50,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f36,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~r2_hidden(X1,u1_pre_topc(X0))) & (r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f15])).
% 0.22/0.51  fof(f15,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.51    inference(ennf_transformation,[],[f2])).
% 0.22/0.51  fof(f2,axiom,(
% 0.22/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.22/0.51  fof(f309,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | ~spl2_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f307])).
% 0.22/0.51  fof(f307,plain,(
% 0.22/0.51    spl2_27 <=> r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_27])])).
% 0.22/0.51  fof(f367,plain,(
% 0.22/0.51    spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_27 | ~spl2_28),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f366])).
% 0.22/0.51  fof(f366,plain,(
% 0.22/0.51    $false | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_27 | ~spl2_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f365,f75])).
% 0.22/0.51  fof(f75,plain,(
% 0.22/0.51    ~v2_struct_0(sK0) | spl2_1),
% 0.22/0.51    inference(avatar_component_clause,[],[f73])).
% 0.22/0.51  fof(f73,plain,(
% 0.22/0.51    spl2_1 <=> v2_struct_0(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.51  fof(f365,plain,(
% 0.22/0.51    v2_struct_0(sK0) | (~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_27 | ~spl2_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f364,f80])).
% 0.22/0.51  fof(f80,plain,(
% 0.22/0.51    v2_pre_topc(sK0) | ~spl2_2),
% 0.22/0.51    inference(avatar_component_clause,[],[f78])).
% 0.22/0.51  fof(f78,plain,(
% 0.22/0.51    spl2_2 <=> v2_pre_topc(sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.51  fof(f364,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl2_3 | ~spl2_4 | spl2_27 | ~spl2_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f363,f85])).
% 0.22/0.51  fof(f363,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl2_4 | spl2_27 | ~spl2_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f362,f90])).
% 0.22/0.51  fof(f362,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (spl2_27 | ~spl2_28)),
% 0.22/0.51    inference(subsumption_resolution,[],[f360,f308])).
% 0.22/0.51  fof(f308,plain,(
% 0.22/0.51    ~r2_hidden(sK1,u1_pre_topc(sK0)) | spl2_27),
% 0.22/0.51    inference(avatar_component_clause,[],[f307])).
% 0.22/0.51  fof(f360,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_28),
% 0.22/0.51    inference(trivial_inequality_removal,[],[f358])).
% 0.22/0.51  fof(f358,plain,(
% 0.22/0.51    u1_pre_topc(sK0) != u1_pre_topc(sK0) | r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_28),
% 0.22/0.51    inference(superposition,[],[f58,f328])).
% 0.22/0.51  fof(f328,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~spl2_28),
% 0.22/0.51    inference(avatar_component_clause,[],[f326])).
% 0.22/0.51  fof(f326,plain,(
% 0.22/0.51    spl2_28 <=> u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_28])])).
% 0.22/0.51  fof(f58,plain,(
% 0.22/0.51    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f38,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (((r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) != k5_tmap_1(X0,X1)) & (u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(nnf_transformation,[],[f24])).
% 0.22/0.51  fof(f24,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f23])).
% 0.22/0.51  fof(f23,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f8])).
% 0.22/0.51  fof(f8,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.22/0.51  fof(f347,plain,(
% 0.22/0.51    spl2_28 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_23),
% 0.22/0.51    inference(avatar_split_clause,[],[f344,f270,f88,f83,f78,f73,f326])).
% 0.22/0.51  fof(f270,plain,(
% 0.22/0.51    spl2_23 <=> r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.22/0.51  fof(f344,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f343,f90])).
% 0.22/0.51  fof(f343,plain,(
% 0.22/0.51    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f342,f75])).
% 0.22/0.51  fof(f342,plain,(
% 0.22/0.51    v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (~spl2_2 | ~spl2_3 | ~spl2_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f341,f80])).
% 0.22/0.51  fof(f341,plain,(
% 0.22/0.51    ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (~spl2_3 | ~spl2_23)),
% 0.22/0.51    inference(subsumption_resolution,[],[f339,f85])).
% 0.22/0.51  fof(f339,plain,(
% 0.22/0.51    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~spl2_23),
% 0.22/0.51    inference(resolution,[],[f271,f121])).
% 0.22/0.51  fof(f121,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(k5_tmap_1(X1,X0),u1_pre_topc(X1)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | u1_pre_topc(X1) = k5_tmap_1(X1,X0)) )),
% 0.22/0.51    inference(resolution,[],[f53,f69])).
% 0.22/0.51  fof(f69,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f42,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(flattening,[],[f41])).
% 0.22/0.51  fof(f41,plain,(
% 0.22/0.51    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 0.22/0.51    inference(nnf_transformation,[],[f1])).
% 0.22/0.51  fof(f1,axiom,(
% 0.22/0.51    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.51  fof(f53,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f18])).
% 0.22/0.51  fof(f18,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.51    inference(flattening,[],[f17])).
% 0.22/0.51  fof(f17,plain,(
% 0.22/0.51    ! [X0] : (! [X1] : (r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.51    inference(ennf_transformation,[],[f10])).
% 0.22/0.51  fof(f10,axiom,(
% 0.22/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(u1_pre_topc(X0),k5_tmap_1(X0,X1))))),
% 0.22/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_tmap_1)).
% 0.22/0.51  fof(f271,plain,(
% 0.22/0.51    r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) | ~spl2_23),
% 0.22/0.51    inference(avatar_component_clause,[],[f270])).
% 0.22/0.51  fof(f331,plain,(
% 0.22/0.51    spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_6 | ~spl2_21 | ~spl2_27),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f330])).
% 0.22/0.51  fof(f330,plain,(
% 0.22/0.51    $false | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | spl2_6 | ~spl2_21 | ~spl2_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f319,f99])).
% 0.22/0.51  fof(f99,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | spl2_6),
% 0.22/0.51    inference(avatar_component_clause,[],[f98])).
% 0.22/0.51  fof(f98,plain,(
% 0.22/0.51    spl2_6 <=> g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.51  fof(f319,plain,(
% 0.22/0.51    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_21 | ~spl2_27)),
% 0.22/0.51    inference(backward_demodulation,[],[f262,f316])).
% 0.22/0.51  fof(f316,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f315,f75])).
% 0.22/0.51  fof(f315,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | v2_struct_0(sK0) | (~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f314,f80])).
% 0.22/0.51  fof(f314,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl2_3 | ~spl2_4 | ~spl2_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f313,f85])).
% 0.22/0.51  fof(f313,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl2_4 | ~spl2_27)),
% 0.22/0.51    inference(subsumption_resolution,[],[f311,f90])).
% 0.22/0.51  fof(f311,plain,(
% 0.22/0.51    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~spl2_27),
% 0.22/0.51    inference(resolution,[],[f309,f57])).
% 0.22/0.51  fof(f57,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f38])).
% 0.22/0.51  fof(f262,plain,(
% 0.22/0.51    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | ~spl2_21),
% 0.22/0.51    inference(avatar_component_clause,[],[f260])).
% 0.22/0.51  fof(f260,plain,(
% 0.22/0.51    spl2_21 <=> k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 0.22/0.51  fof(f329,plain,(
% 0.22/0.51    spl2_28 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_27),
% 0.22/0.51    inference(avatar_split_clause,[],[f316,f307,f88,f83,f78,f73,f326])).
% 0.22/0.51  fof(f310,plain,(
% 0.22/0.51    spl2_27 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 0.22/0.51    inference(avatar_split_clause,[],[f305,f94,f88,f83,f307])).
% 0.22/0.51  fof(f305,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f304,f85])).
% 0.22/0.51  fof(f304,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | (~spl2_4 | ~spl2_5)),
% 0.22/0.51    inference(subsumption_resolution,[],[f303,f90])).
% 0.22/0.51  fof(f303,plain,(
% 0.22/0.51    r2_hidden(sK1,u1_pre_topc(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_5),
% 0.22/0.51    inference(resolution,[],[f96,f49])).
% 0.22/0.51  fof(f49,plain,(
% 0.22/0.51    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.51    inference(cnf_transformation,[],[f36])).
% 0.22/0.51  fof(f96,plain,(
% 0.22/0.51    v3_pre_topc(sK1,sK0) | ~spl2_5),
% 0.22/0.51    inference(avatar_component_clause,[],[f94])).
% 0.22/0.51  fof(f302,plain,(
% 0.22/0.51    ~spl2_19 | ~spl2_20 | spl2_22 | ~spl2_26),
% 0.22/0.51    inference(avatar_contradiction_clause,[],[f301])).
% 0.22/0.51  fof(f301,plain,(
% 0.22/0.51    $false | (~spl2_19 | ~spl2_20 | spl2_22 | ~spl2_26)),
% 0.22/0.51    inference(subsumption_resolution,[],[f300,f267])).
% 0.22/0.51  fof(f267,plain,(
% 0.22/0.51    ~v1_tops_2(k5_tmap_1(sK0,sK1),sK0) | spl2_22),
% 0.22/0.51    inference(avatar_component_clause,[],[f266])).
% 0.22/0.51  fof(f266,plain,(
% 0.22/0.51    spl2_22 <=> v1_tops_2(k5_tmap_1(sK0,sK1),sK0)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.22/0.51  fof(f300,plain,(
% 0.22/0.51    v1_tops_2(k5_tmap_1(sK0,sK1),sK0) | (~spl2_19 | ~spl2_20 | ~spl2_26)),
% 0.22/0.51    inference(subsumption_resolution,[],[f298,f219])).
% 0.22/0.51  fof(f219,plain,(
% 0.22/0.51    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_19),
% 0.22/0.51    inference(avatar_component_clause,[],[f217])).
% 0.22/0.51  fof(f217,plain,(
% 0.22/0.51    spl2_19 <=> m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_19])])).
% 0.22/0.51  fof(f298,plain,(
% 0.22/0.51    ~m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k5_tmap_1(sK0,sK1),sK0) | (~spl2_20 | ~spl2_26)),
% 0.22/0.51    inference(resolution,[],[f294,f257])).
% 0.22/0.51  fof(f257,plain,(
% 0.22/0.51    ( ! [X0] : (~v1_tops_2(X0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X0,sK0)) ) | ~spl2_20),
% 0.22/0.51    inference(avatar_component_clause,[],[f256])).
% 0.22/0.51  fof(f256,plain,(
% 0.22/0.51    spl2_20 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X0,k6_tmap_1(sK0,sK1)) | v1_tops_2(X0,sK0))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_20])])).
% 0.22/0.51  fof(f294,plain,(
% 0.22/0.51    v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~spl2_26),
% 0.22/0.51    inference(avatar_component_clause,[],[f292])).
% 0.22/0.51  fof(f292,plain,(
% 0.22/0.51    spl2_26 <=> v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 0.22/0.51  fof(f295,plain,(
% 0.22/0.51    spl2_26 | ~spl2_19 | ~spl2_25),
% 0.22/0.51    inference(avatar_split_clause,[],[f290,f286,f217,f292])).
% 0.22/0.51  fof(f286,plain,(
% 0.22/0.51    spl2_25 <=> ! [X3] : (~r1_tarski(X3,k5_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X3,k6_tmap_1(sK0,sK1)))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 0.22/0.51  fof(f290,plain,(
% 0.22/0.51    v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl2_19 | ~spl2_25)),
% 0.22/0.51    inference(subsumption_resolution,[],[f289,f70])).
% 0.22/0.51  fof(f70,plain,(
% 0.22/0.51    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.22/0.51    inference(equality_resolution,[],[f68])).
% 0.22/0.51  fof(f68,plain,(
% 0.22/0.51    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.22/0.51    inference(cnf_transformation,[],[f42])).
% 0.22/0.51  fof(f289,plain,(
% 0.22/0.51    ~r1_tarski(k5_tmap_1(sK0,sK1),k5_tmap_1(sK0,sK1)) | v1_tops_2(k5_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | (~spl2_19 | ~spl2_25)),
% 0.22/0.51    inference(resolution,[],[f287,f219])).
% 0.22/0.51  fof(f287,plain,(
% 0.22/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X3,k5_tmap_1(sK0,sK1)) | v1_tops_2(X3,k6_tmap_1(sK0,sK1))) ) | ~spl2_25),
% 0.22/0.51    inference(avatar_component_clause,[],[f286])).
% 0.22/0.51  fof(f288,plain,(
% 0.22/0.51    spl2_25 | ~spl2_12 | ~spl2_14 | ~spl2_17),
% 0.22/0.51    inference(avatar_split_clause,[],[f284,f208,f180,f159,f286])).
% 0.22/0.51  fof(f159,plain,(
% 0.22/0.51    spl2_12 <=> l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).
% 0.22/0.51  fof(f180,plain,(
% 0.22/0.51    spl2_14 <=> u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.51  fof(f208,plain,(
% 0.22/0.51    spl2_17 <=> u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1)),
% 0.22/0.51    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.51  fof(f284,plain,(
% 0.22/0.51    ( ! [X3] : (~r1_tarski(X3,k5_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(X3,k6_tmap_1(sK0,sK1))) ) | (~spl2_12 | ~spl2_14 | ~spl2_17)),
% 0.22/0.51    inference(forward_demodulation,[],[f199,f210])).
% 0.22/0.51  fof(f210,plain,(
% 0.22/0.51    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) | ~spl2_17),
% 0.22/0.51    inference(avatar_component_clause,[],[f208])).
% 0.22/0.51  fof(f199,plain,(
% 0.22/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X3,u1_pre_topc(k6_tmap_1(sK0,sK1))) | v1_tops_2(X3,k6_tmap_1(sK0,sK1))) ) | (~spl2_12 | ~spl2_14)),
% 0.22/0.51    inference(subsumption_resolution,[],[f191,f161])).
% 0.22/0.51  fof(f161,plain,(
% 0.22/0.51    l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~spl2_12),
% 0.22/0.51    inference(avatar_component_clause,[],[f159])).
% 0.22/0.51  fof(f191,plain,(
% 0.22/0.51    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(X3,u1_pre_topc(k6_tmap_1(sK0,sK1))) | v1_tops_2(X3,k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1))) ) | ~spl2_14),
% 0.22/0.51    inference(superposition,[],[f52,f182])).
% 0.22/0.52  fof(f182,plain,(
% 0.22/0.52    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | ~spl2_14),
% 0.22/0.52    inference(avatar_component_clause,[],[f180])).
% 0.22/0.52  fof(f52,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f37,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((v1_tops_2(X1,X0) | ~r1_tarski(X1,u1_pre_topc(X0))) & (r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f16])).
% 0.22/0.52  fof(f16,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.52    inference(ennf_transformation,[],[f3])).
% 0.22/0.52  fof(f3,axiom,(
% 0.22/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.22/0.52  fof(f279,plain,(
% 0.22/0.52    ~spl2_22 | ~spl2_3 | ~spl2_19 | spl2_23),
% 0.22/0.52    inference(avatar_split_clause,[],[f278,f270,f217,f83,f266])).
% 0.22/0.52  fof(f278,plain,(
% 0.22/0.52    ~v1_tops_2(k5_tmap_1(sK0,sK1),sK0) | (~spl2_3 | ~spl2_19 | spl2_23)),
% 0.22/0.52    inference(subsumption_resolution,[],[f254,f272])).
% 0.22/0.52  fof(f272,plain,(
% 0.22/0.52    ~r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) | spl2_23),
% 0.22/0.52    inference(avatar_component_clause,[],[f270])).
% 0.22/0.52  fof(f254,plain,(
% 0.22/0.52    ~v1_tops_2(k5_tmap_1(sK0,sK1),sK0) | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) | (~spl2_3 | ~spl2_19)),
% 0.22/0.52    inference(subsumption_resolution,[],[f243,f85])).
% 0.22/0.52  fof(f243,plain,(
% 0.22/0.52    ~v1_tops_2(k5_tmap_1(sK0,sK1),sK0) | r1_tarski(k5_tmap_1(sK0,sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0) | ~spl2_19),
% 0.22/0.52    inference(resolution,[],[f219,f51])).
% 0.22/0.52  fof(f51,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f37])).
% 0.22/0.52  fof(f263,plain,(
% 0.22/0.52    spl2_21 | ~spl2_4 | ~spl2_18),
% 0.22/0.52    inference(avatar_split_clause,[],[f221,f213,f88,f260])).
% 0.22/0.52  fof(f213,plain,(
% 0.22/0.52    spl2_18 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_18])])).
% 0.22/0.52  fof(f221,plain,(
% 0.22/0.52    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) | (~spl2_4 | ~spl2_18)),
% 0.22/0.52    inference(resolution,[],[f214,f90])).
% 0.22/0.52  fof(f214,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))) ) | ~spl2_18),
% 0.22/0.52    inference(avatar_component_clause,[],[f213])).
% 0.22/0.52  fof(f258,plain,(
% 0.22/0.52    spl2_20 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_14),
% 0.22/0.52    inference(avatar_split_clause,[],[f239,f180,f98,f83,f78,f73,f256])).
% 0.22/0.52  fof(f239,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(X0,k6_tmap_1(sK0,sK1)) | v1_tops_2(X0,sK0)) ) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6 | ~spl2_14)),
% 0.22/0.52    inference(forward_demodulation,[],[f167,f182])).
% 0.22/0.52  fof(f167,plain,(
% 0.22/0.52    ( ! [X0] : (~v1_tops_2(X0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) | v1_tops_2(X0,sK0)) ) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6)),
% 0.22/0.52    inference(forward_demodulation,[],[f166,f100])).
% 0.22/0.52  fof(f100,plain,(
% 0.22/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | ~spl2_6),
% 0.22/0.52    inference(avatar_component_clause,[],[f98])).
% 0.22/0.52  fof(f166,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_tops_2(X0,sK0)) ) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_6)),
% 0.22/0.52    inference(forward_demodulation,[],[f165,f100])).
% 0.22/0.52  fof(f165,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_tops_2(X0,sK0)) ) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f164,f75])).
% 0.22/0.52  fof(f164,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_tops_2(X0,sK0) | v2_struct_0(sK0)) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f163,f80])).
% 0.22/0.52  fof(f163,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))))) | ~v1_tops_2(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | v1_tops_2(X0,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0)) ) | ~spl2_3),
% 0.22/0.52    inference(resolution,[],[f61,f85])).
% 0.22/0.52  fof(f61,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | v1_tops_2(X1,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f40])).
% 0.22/0.52  fof(f40,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f39])).
% 0.22/0.52  fof(f39,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) | ~v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) & ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_2(X1,X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f26])).
% 0.22/0.52  fof(f26,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f25])).
% 0.22/0.52  fof(f25,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f4])).
% 0.22/0.52  fof(f4,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) & v1_tops_2(X1,X0)) <=> (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))))) & v1_tops_2(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_compts_1)).
% 0.22/0.52  fof(f220,plain,(
% 0.22/0.52    spl2_19 | ~spl2_4 | ~spl2_16),
% 0.22/0.52    inference(avatar_split_clause,[],[f206,f202,f88,f217])).
% 0.22/0.52  fof(f202,plain,(
% 0.22/0.52    spl2_16 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.52  fof(f206,plain,(
% 0.22/0.52    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | (~spl2_4 | ~spl2_16)),
% 0.22/0.52    inference(resolution,[],[f203,f90])).
% 0.22/0.52  fof(f203,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl2_16),
% 0.22/0.52    inference(avatar_component_clause,[],[f202])).
% 0.22/0.52  fof(f215,plain,(
% 0.22/0.52    spl2_18 | spl2_1 | ~spl2_2 | ~spl2_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f143,f83,f78,f73,f213])).
% 0.22/0.52  fof(f143,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0))) ) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f142,f75])).
% 0.22/0.52  fof(f142,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f141,f85])).
% 0.22/0.52  fof(f141,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl2_2),
% 0.22/0.52    inference(resolution,[],[f54,f80])).
% 0.22/0.52  fof(f54,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f20])).
% 0.22/0.52  fof(f20,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f19])).
% 0.22/0.52  fof(f19,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : (k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f5])).
% 0.22/0.52  fof(f5,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k6_tmap_1(X0,X1) = g1_pre_topc(u1_struct_0(X0),k5_tmap_1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_tmap_1)).
% 0.22/0.52  fof(f211,plain,(
% 0.22/0.52    spl2_17 | ~spl2_4 | ~spl2_15),
% 0.22/0.52    inference(avatar_split_clause,[],[f205,f185,f88,f208])).
% 0.22/0.52  fof(f185,plain,(
% 0.22/0.52    spl2_15 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.52  fof(f205,plain,(
% 0.22/0.52    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) | (~spl2_4 | ~spl2_15)),
% 0.22/0.52    inference(resolution,[],[f186,f90])).
% 0.22/0.52  fof(f186,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))) ) | ~spl2_15),
% 0.22/0.52    inference(avatar_component_clause,[],[f185])).
% 0.22/0.52  fof(f204,plain,(
% 0.22/0.52    spl2_16 | spl2_1 | ~spl2_2 | ~spl2_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f136,f83,f78,f73,f202])).
% 0.22/0.52  fof(f136,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f135,f75])).
% 0.22/0.52  fof(f135,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_struct_0(sK0)) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f134,f85])).
% 0.22/0.52  fof(f134,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(k5_tmap_1(sK0,X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v2_struct_0(sK0)) ) | ~spl2_2),
% 0.22/0.52    inference(resolution,[],[f63,f80])).
% 0.22/0.52  fof(f63,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f28])).
% 0.22/0.52  fof(f28,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f27])).
% 0.22/0.52  fof(f27,plain,(
% 0.22/0.52    ! [X0,X1] : (m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f6])).
% 0.22/0.52  fof(f6,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k5_tmap_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_tmap_1)).
% 0.22/0.52  fof(f187,plain,(
% 0.22/0.52    spl2_15 | spl2_1 | ~spl2_2 | ~spl2_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f133,f83,f78,f73,f185])).
% 0.22/0.52  fof(f133,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0))) ) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f132,f75])).
% 0.22/0.52  fof(f132,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f131,f85])).
% 0.22/0.52  fof(f131,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k5_tmap_1(sK0,X0) = u1_pre_topc(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl2_2),
% 0.22/0.52    inference(resolution,[],[f56,f80])).
% 0.22/0.52  fof(f56,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f22,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f21])).
% 0.22/0.52  fof(f21,plain,(
% 0.22/0.52    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f9])).
% 0.22/0.52  fof(f9,axiom,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.22/0.52  fof(f183,plain,(
% 0.22/0.52    spl2_14 | ~spl2_4 | ~spl2_13),
% 0.22/0.52    inference(avatar_split_clause,[],[f178,f175,f88,f180])).
% 0.22/0.52  fof(f175,plain,(
% 0.22/0.52    spl2_13 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 0.22/0.52  fof(f178,plain,(
% 0.22/0.52    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) | (~spl2_4 | ~spl2_13)),
% 0.22/0.52    inference(resolution,[],[f176,f90])).
% 0.22/0.52  fof(f176,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) ) | ~spl2_13),
% 0.22/0.52    inference(avatar_component_clause,[],[f175])).
% 0.22/0.52  fof(f177,plain,(
% 0.22/0.52    spl2_13 | spl2_1 | ~spl2_2 | ~spl2_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f125,f83,f78,f73,f175])).
% 0.22/0.52  fof(f125,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0))) ) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f124,f75])).
% 0.22/0.52  fof(f124,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f123,f85])).
% 0.22/0.52  fof(f123,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl2_2),
% 0.22/0.52    inference(resolution,[],[f55,f80])).
% 0.22/0.52  fof(f55,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f22])).
% 0.22/0.52  fof(f162,plain,(
% 0.22/0.52    spl2_12 | ~spl2_4 | ~spl2_10),
% 0.22/0.52    inference(avatar_split_clause,[],[f157,f138,f88,f159])).
% 0.22/0.52  fof(f138,plain,(
% 0.22/0.52    spl2_10 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X0)))),
% 0.22/0.52    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.52  fof(f157,plain,(
% 0.22/0.52    l1_pre_topc(k6_tmap_1(sK0,sK1)) | (~spl2_4 | ~spl2_10)),
% 0.22/0.52    inference(resolution,[],[f139,f90])).
% 0.22/0.52  fof(f139,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X0))) ) | ~spl2_10),
% 0.22/0.52    inference(avatar_component_clause,[],[f138])).
% 0.22/0.52  fof(f140,plain,(
% 0.22/0.52    spl2_10 | spl2_1 | ~spl2_2 | ~spl2_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f116,f83,f78,f73,f138])).
% 0.22/0.52  fof(f116,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X0))) ) | (spl2_1 | ~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f115,f75])).
% 0.22/0.52  fof(f115,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | (~spl2_2 | ~spl2_3)),
% 0.22/0.52    inference(subsumption_resolution,[],[f114,f85])).
% 0.22/0.52  fof(f114,plain,(
% 0.22/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | l1_pre_topc(k6_tmap_1(sK0,X0)) | v2_struct_0(sK0)) ) | ~spl2_2),
% 0.22/0.52    inference(resolution,[],[f66,f80])).
% 0.22/0.52  fof(f66,plain,(
% 0.22/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | l1_pre_topc(k6_tmap_1(X0,X1)) | v2_struct_0(X0)) )),
% 0.22/0.52    inference(cnf_transformation,[],[f30])).
% 0.22/0.52  fof(f30,plain,(
% 0.22/0.52    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f29])).
% 0.22/0.52  fof(f29,plain,(
% 0.22/0.52    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f7])).
% 0.22/0.52  fof(f7,axiom,(
% 0.22/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.22/0.52  fof(f103,plain,(
% 0.22/0.52    ~spl2_5 | ~spl2_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f102,f98,f94])).
% 0.22/0.52  fof(f102,plain,(
% 0.22/0.52    ~v3_pre_topc(sK1,sK0) | ~spl2_6),
% 0.22/0.52    inference(subsumption_resolution,[],[f48,f100])).
% 0.22/0.52  fof(f48,plain,(
% 0.22/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f35,plain,(
% 0.22/0.52    ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f32,f34,f33])).
% 0.22/0.52  fof(f33,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f34,plain,(
% 0.22/0.52    ? [X1] : ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X1) | ~v3_pre_topc(X1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)) & (g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.52    introduced(choice_axiom,[])).
% 0.22/0.52  fof(f32,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f31])).
% 0.22/0.52  fof(f31,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : (((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) & (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(nnf_transformation,[],[f14])).
% 0.22/0.52  fof(f14,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.52    inference(flattening,[],[f13])).
% 0.22/0.52  fof(f13,plain,(
% 0.22/0.52    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.52    inference(ennf_transformation,[],[f12])).
% 0.22/0.52  fof(f12,negated_conjecture,(
% 0.22/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.22/0.52    inference(negated_conjecture,[],[f11])).
% 0.22/0.52  fof(f11,conjecture,(
% 0.22/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.22/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.22/0.52  fof(f101,plain,(
% 0.22/0.52    spl2_5 | spl2_6),
% 0.22/0.52    inference(avatar_split_clause,[],[f47,f98,f94])).
% 0.22/0.52  fof(f47,plain,(
% 0.22/0.52    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | v3_pre_topc(sK1,sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f91,plain,(
% 0.22/0.52    spl2_4),
% 0.22/0.52    inference(avatar_split_clause,[],[f46,f88])).
% 0.22/0.52  fof(f46,plain,(
% 0.22/0.52    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f86,plain,(
% 0.22/0.52    spl2_3),
% 0.22/0.52    inference(avatar_split_clause,[],[f45,f83])).
% 0.22/0.52  fof(f45,plain,(
% 0.22/0.52    l1_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f81,plain,(
% 0.22/0.52    spl2_2),
% 0.22/0.52    inference(avatar_split_clause,[],[f44,f78])).
% 0.22/0.52  fof(f44,plain,(
% 0.22/0.52    v2_pre_topc(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  fof(f76,plain,(
% 0.22/0.52    ~spl2_1),
% 0.22/0.52    inference(avatar_split_clause,[],[f43,f73])).
% 0.22/0.52  fof(f43,plain,(
% 0.22/0.52    ~v2_struct_0(sK0)),
% 0.22/0.52    inference(cnf_transformation,[],[f35])).
% 0.22/0.52  % SZS output end Proof for theBenchmark
% 0.22/0.52  % (23774)------------------------------
% 0.22/0.52  % (23774)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (23774)Termination reason: Refutation
% 0.22/0.52  
% 0.22/0.52  % (23774)Memory used [KB]: 6396
% 0.22/0.52  % (23774)Time elapsed: 0.105 s
% 0.22/0.52  % (23774)------------------------------
% 0.22/0.52  % (23774)------------------------------
% 1.26/0.52  % (23784)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.26/0.52  % (23771)Success in time 0.154 s
%------------------------------------------------------------------------------
