%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:06 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 366 expanded)
%              Number of leaves         :   35 ( 145 expanded)
%              Depth                    :   14
%              Number of atoms          :  874 (2033 expanded)
%              Number of equality atoms :   80 ( 122 expanded)
%              Maximal formula depth    :   13 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f320,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f116,f118,f124,f133,f145,f151,f187,f200,f211,f220,f227,f256,f263,f277,f292,f318,f319])).

fof(f319,plain,
    ( u1_struct_0(sK0) != sK4(sK0,sK1)
    | r1_tarski(sK1,sK4(sK0,sK1))
    | ~ r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f318,plain,
    ( ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | spl5_11
    | ~ spl5_27 ),
    inference(avatar_contradiction_clause,[],[f317])).

fof(f317,plain,
    ( $false
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | spl5_11
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f316,f86])).

fof(f86,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl5_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

% (23588)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f316,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | spl5_11
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f315,f96])).

fof(f96,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f315,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_6
    | spl5_11
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f314,f106])).

fof(f106,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl5_6
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f314,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl5_11
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f304,f139])).

fof(f139,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | spl5_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl5_11
  <=> v1_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f304,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_27 ),
    inference(trivial_inequality_removal,[],[f303])).

fof(f303,plain,
    ( k1_xboole_0 != k1_xboole_0
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl5_27 ),
    inference(superposition,[],[f72,f287])).

fof(f287,plain,
    ( k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f285])).

fof(f285,plain,
    ( spl5_27
  <=> k1_xboole_0 = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != sK4(X0,X1)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | ( r1_xboole_0(X1,sK4(X0,X1))
                & v3_pre_topc(sK4(X0,X1),X0)
                & k1_xboole_0 != sK4(X0,X1)
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( ~ r1_xboole_0(X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).

fof(f44,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( r1_xboole_0(X1,X2)
          & v3_pre_topc(X2,X0)
          & k1_xboole_0 != X2
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( r1_xboole_0(X1,sK4(X0,X1))
        & v3_pre_topc(sK4(X0,X1),X0)
        & k1_xboole_0 != sK4(X0,X1)
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | ? [X2] :
                  ( r1_xboole_0(X1,X2)
                  & v3_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X3] :
                  ( ~ r1_xboole_0(X1,X3)
                  | ~ v3_pre_topc(X3,X0)
                  | k1_xboole_0 = X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v1_tops_1(X1,X0)
              | ? [X2] :
                  ( r1_xboole_0(X1,X2)
                  & v3_pre_topc(X2,X0)
                  & k1_xboole_0 != X2
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
            & ( ! [X2] :
                  ( ~ r1_xboole_0(X1,X2)
                  | ~ v3_pre_topc(X2,X0)
                  | k1_xboole_0 = X2
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v1_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).

fof(f292,plain,
    ( spl5_27
    | spl5_28
    | ~ spl5_6
    | spl5_11
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f283,f275,f138,f104,f289,f285])).

fof(f289,plain,
    ( spl5_28
  <=> u1_struct_0(sK0) = sK4(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f275,plain,
    ( spl5_26
  <=> ! [X0] :
        ( k1_xboole_0 = sK4(sK0,X0)
        | u1_struct_0(sK0) = sK4(sK0,X0)
        | v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f283,plain,
    ( u1_struct_0(sK0) = sK4(sK0,sK1)
    | k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl5_6
    | spl5_11
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f279,f139])).

fof(f279,plain,
    ( u1_struct_0(sK0) = sK4(sK0,sK1)
    | v1_tops_1(sK1,sK0)
    | k1_xboole_0 = sK4(sK0,sK1)
    | ~ spl5_6
    | ~ spl5_26 ),
    inference(resolution,[],[f276,f106])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = sK4(sK0,X0)
        | v1_tops_1(X0,sK0)
        | k1_xboole_0 = sK4(sK0,X0) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f275])).

fof(f277,plain,
    ( spl5_26
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f192,f185,f149,f94,f84,f275])).

fof(f149,plain,
    ( spl5_13
  <=> ! [X0] :
        ( m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f185,plain,
    ( spl5_17
  <=> ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f192,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK4(sK0,X0)
        | u1_struct_0(sK0) = sK4(sK0,X0)
        | v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_13
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f191,f150])).

fof(f150,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f149])).

fof(f191,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK4(sK0,X0)
        | ~ m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = sK4(sK0,X0)
        | v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f190,f86])).

fof(f190,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK4(sK0,X0)
        | ~ m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = sK4(sK0,X0)
        | v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f189,f96])).

fof(f189,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK4(sK0,X0)
        | ~ m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = sK4(sK0,X0)
        | v1_tops_1(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_17 ),
    inference(resolution,[],[f186,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(sK4(X0,X1),X0)
      | v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f186,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X0 )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f185])).

fof(f263,plain,
    ( ~ spl5_23
    | spl5_5
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f243,f142,f99,f260])).

fof(f260,plain,
    ( spl5_23
  <=> r1_tarski(sK1,sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f99,plain,
    ( spl5_5
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f142,plain,
    ( spl5_12
  <=> r1_xboole_0(sK1,sK4(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f243,plain,
    ( ~ r1_tarski(sK1,sK4(sK0,sK1))
    | spl5_5
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f242,f101])).

fof(f101,plain,
    ( ~ v1_xboole_0(sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f242,plain,
    ( ~ r1_tarski(sK1,sK4(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ spl5_12 ),
    inference(resolution,[],[f144,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X1,X0)
      | ~ r1_tarski(X1,X0)
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ~ ( r1_xboole_0(X1,X0)
          & r1_tarski(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

fof(f144,plain,
    ( r1_xboole_0(sK1,sK4(sK0,sK1))
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f142])).

fof(f256,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f254])).

fof(f254,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_5
    | ~ spl5_6
    | spl5_8
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f81,f86,f91,f96,f101,f210,f106,f114,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | v1_zfmisc_1(X1)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tex_2(X1,X0)
              | ~ v1_zfmisc_1(X1) )
            & ( v1_zfmisc_1(X1)
              | ~ v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f114,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl5_8
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f210,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f208,plain,
    ( spl5_20
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f91,plain,
    ( v2_tdlat_3(sK0)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl5_3
  <=> v2_tdlat_3(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f81,plain,
    ( ~ v2_struct_0(sK0)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl5_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f227,plain,
    ( spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_11
    | ~ spl5_20 ),
    inference(avatar_contradiction_clause,[],[f222])).

fof(f222,plain,
    ( $false
    | spl5_1
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_6
    | spl5_7
    | ~ spl5_11
    | ~ spl5_20 ),
    inference(unit_resulting_resolution,[],[f81,f86,f96,f110,f140,f106,f210,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
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
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f140,plain,
    ( v1_tops_1(sK1,sK0)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f110,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f109,plain,
    ( spl5_7
  <=> v3_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f220,plain,
    ( spl5_20
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(avatar_split_clause,[],[f219,f198,f104,f94,f89,f84,f79,f208])).

fof(f198,plain,
    ( spl5_19
  <=> ! [X0] :
        ( v2_tex_2(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_tdlat_3(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f219,plain,
    ( v2_tex_2(sK1,sK0)
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f218,f81])).

fof(f218,plain,
    ( v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f217,f86])).

fof(f217,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f216,f91])).

fof(f216,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(subsumption_resolution,[],[f215,f96])).

fof(f215,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ spl5_6
    | ~ spl5_19 ),
    inference(resolution,[],[f199,f106])).

fof(f199,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | v2_tex_2(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_tdlat_3(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f198])).

fof(f211,plain,
    ( spl5_20
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(avatar_split_clause,[],[f206,f109,f104,f94,f208])).

fof(f206,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f205,f96])).

fof(f205,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ spl5_6
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f202,f106])).

fof(f202,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl5_7 ),
    inference(resolution,[],[f111,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ( sK2(X0,X1) != X1
                & r1_tarski(X1,sK2(X0,X1))
                & v2_tex_2(sK2(X0,X1),X0)
                & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).

fof(f35,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( X1 != X2
          & r1_tarski(X1,X2)
          & v2_tex_2(X2,X0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK2(X0,X1) != X1
        & r1_tarski(X1,sK2(X0,X1))
        & v2_tex_2(sK2(X0,X1),X0)
        & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X3] :
                    ( X1 = X3
                    | ~ r1_tarski(X1,X3)
                    | ~ v2_tex_2(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_tex_2(X1,X0)
              | ? [X2] :
                  ( X1 != X2
                  & r1_tarski(X1,X2)
                  & v2_tex_2(X2,X0)
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ v2_tex_2(X1,X0) )
            & ( ( ! [X2] :
                    ( X1 = X2
                    | ~ r1_tarski(X1,X2)
                    | ~ v2_tex_2(X2,X0)
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
                & v2_tex_2(X1,X0) )
              | ~ v3_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f111,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f109])).

fof(f200,plain,
    ( spl5_19
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f166,f113,f198])).

fof(f166,plain,
    ( ! [X0] :
        ( v2_tex_2(sK1,X0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_tdlat_3(X0)
        | ~ v2_pre_topc(X0)
        | v2_struct_0(X0) )
    | ~ spl5_8 ),
    inference(resolution,[],[f163,f115])).

fof(f115,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f113])).

fof(f163,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f62,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
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
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).

fof(f62,plain,(
    ! [X0,X1] :
      ( v2_tex_2(X1,X0)
      | ~ v1_zfmisc_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_xboole_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f187,plain,
    ( spl5_17
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f180,f94,f89,f84,f185])).

fof(f180,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X0 )
    | ~ spl5_2
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f179,f86])).

fof(f179,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X0
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_3
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f178,f96])).

fof(f178,plain,
    ( ! [X0] :
        ( k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | u1_struct_0(sK0) = X0
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_3 ),
    inference(resolution,[],[f65,f91])).

fof(f65,plain,(
    ! [X2,X0] :
      ( ~ v2_tdlat_3(X0)
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = X2
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ( u1_struct_0(X0) != sK3(X0)
            & k1_xboole_0 != sK3(X0)
            & v3_pre_topc(sK3(X0),X0)
            & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ? [X1] :
          ( u1_struct_0(X0) != X1
          & k1_xboole_0 != X1
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( u1_struct_0(X0) != sK3(X0)
        & k1_xboole_0 != sK3(X0)
        & v3_pre_topc(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X2] :
              ( u1_struct_0(X0) = X2
              | k1_xboole_0 = X2
              | ~ v3_pre_topc(X2,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( ( v2_tdlat_3(X0)
          | ? [X1] :
              ( u1_struct_0(X0) != X1
              & k1_xboole_0 != X1
              & v3_pre_topc(X1,X0)
              & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
        & ( ! [X1] :
              ( u1_struct_0(X0) = X1
              | k1_xboole_0 = X1
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ v2_tdlat_3(X0) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( u1_struct_0(X0) = X1
            | k1_xboole_0 = X1
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v2_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( u1_struct_0(X0) != X1
                & k1_xboole_0 != X1
                & v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tdlat_3)).

fof(f151,plain,
    ( spl5_13
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f147,f94,f84,f149])).

fof(f147,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f146,f86])).

fof(f146,plain,
    ( ! [X0] :
        ( m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f71,f96])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f145,plain,
    ( spl5_11
    | spl5_12
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f134,f131,f104,f142,f138])).

fof(f131,plain,
    ( spl5_10
  <=> ! [X0] :
        ( r1_xboole_0(X0,sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f134,plain,
    ( r1_xboole_0(sK1,sK4(sK0,sK1))
    | v1_tops_1(sK1,sK0)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(resolution,[],[f132,f106])).

fof(f132,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(X0,sK4(sK0,X0))
        | v1_tops_1(X0,sK0) )
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f133,plain,
    ( spl5_10
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(avatar_split_clause,[],[f129,f94,f84,f131])).

fof(f129,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0) )
    | ~ spl5_2
    | ~ spl5_4 ),
    inference(subsumption_resolution,[],[f128,f86])).

fof(f128,plain,
    ( ! [X0] :
        ( r1_xboole_0(X0,sK4(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v1_tops_1(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl5_4 ),
    inference(resolution,[],[f74,f96])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_xboole_0(X1,sK4(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f124,plain,
    ( spl5_9
    | ~ spl5_6 ),
    inference(avatar_split_clause,[],[f119,f104,f121])).

fof(f121,plain,
    ( spl5_9
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f119,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl5_6 ),
    inference(resolution,[],[f76,f106])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f118,plain,
    ( ~ spl5_7
    | ~ spl5_8 ),
    inference(avatar_split_clause,[],[f117,f113,f109])).

fof(f117,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f54,f115])).

fof(f54,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ v1_zfmisc_1(sK1)
      | ~ v3_tex_2(sK1,sK0) )
    & ( v1_zfmisc_1(sK1)
      | v3_tex_2(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & ~ v1_xboole_0(sK1)
    & l1_pre_topc(sK0)
    & v2_tdlat_3(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( ~ v1_zfmisc_1(X1)
              | ~ v3_tex_2(X1,X0) )
            & ( v1_zfmisc_1(X1)
              | v3_tex_2(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
        & l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,sK0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(sK0)
      & v2_tdlat_3(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X1] :
        ( ( ~ v1_zfmisc_1(X1)
          | ~ v3_tex_2(X1,sK0) )
        & ( v1_zfmisc_1(X1)
          | v3_tex_2(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        & ~ v1_xboole_0(X1) )
   => ( ( ~ v1_zfmisc_1(sK1)
        | ~ v3_tex_2(sK1,sK0) )
      & ( v1_zfmisc_1(sK1)
        | v3_tex_2(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ~ v1_zfmisc_1(X1)
            | ~ v3_tex_2(X1,X0) )
          & ( v1_zfmisc_1(X1)
            | v3_tex_2(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v3_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f116,plain,
    ( spl5_7
    | spl5_8 ),
    inference(avatar_split_clause,[],[f53,f113,f109])).

fof(f53,plain,
    ( v1_zfmisc_1(sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f107,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f52,f104])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f51,f99])).

fof(f51,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f49,f89])).

fof(f49,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f48,f84])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f47,f79])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:44:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.47  % (23567)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.47  % (23567)Refutation found. Thanks to Tanya!
% 0.19/0.47  % SZS status Theorem for theBenchmark
% 0.19/0.48  % (23582)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.19/0.48  % SZS output start Proof for theBenchmark
% 0.19/0.48  fof(f320,plain,(
% 0.19/0.48    $false),
% 0.19/0.48    inference(avatar_sat_refutation,[],[f82,f87,f92,f97,f102,f107,f116,f118,f124,f133,f145,f151,f187,f200,f211,f220,f227,f256,f263,f277,f292,f318,f319])).
% 0.19/0.48  fof(f319,plain,(
% 0.19/0.48    u1_struct_0(sK0) != sK4(sK0,sK1) | r1_tarski(sK1,sK4(sK0,sK1)) | ~r1_tarski(sK1,u1_struct_0(sK0))),
% 0.19/0.48    introduced(theory_tautology_sat_conflict,[])).
% 0.19/0.48  fof(f318,plain,(
% 0.19/0.48    ~spl5_2 | ~spl5_4 | ~spl5_6 | spl5_11 | ~spl5_27),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f317])).
% 0.19/0.48  fof(f317,plain,(
% 0.19/0.48    $false | (~spl5_2 | ~spl5_4 | ~spl5_6 | spl5_11 | ~spl5_27)),
% 0.19/0.48    inference(subsumption_resolution,[],[f316,f86])).
% 0.19/0.48  fof(f86,plain,(
% 0.19/0.48    v2_pre_topc(sK0) | ~spl5_2),
% 0.19/0.48    inference(avatar_component_clause,[],[f84])).
% 0.19/0.48  fof(f84,plain,(
% 0.19/0.48    spl5_2 <=> v2_pre_topc(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.19/0.48  % (23588)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.19/0.48  fof(f316,plain,(
% 0.19/0.48    ~v2_pre_topc(sK0) | (~spl5_4 | ~spl5_6 | spl5_11 | ~spl5_27)),
% 0.19/0.48    inference(subsumption_resolution,[],[f315,f96])).
% 0.19/0.48  fof(f96,plain,(
% 0.19/0.48    l1_pre_topc(sK0) | ~spl5_4),
% 0.19/0.48    inference(avatar_component_clause,[],[f94])).
% 0.19/0.48  fof(f94,plain,(
% 0.19/0.48    spl5_4 <=> l1_pre_topc(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.19/0.48  fof(f315,plain,(
% 0.19/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (~spl5_6 | spl5_11 | ~spl5_27)),
% 0.19/0.48    inference(subsumption_resolution,[],[f314,f106])).
% 0.19/0.48  fof(f106,plain,(
% 0.19/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl5_6),
% 0.19/0.48    inference(avatar_component_clause,[],[f104])).
% 0.19/0.48  fof(f104,plain,(
% 0.19/0.48    spl5_6 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.19/0.48  fof(f314,plain,(
% 0.19/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | (spl5_11 | ~spl5_27)),
% 0.19/0.48    inference(subsumption_resolution,[],[f304,f139])).
% 0.19/0.48  fof(f139,plain,(
% 0.19/0.48    ~v1_tops_1(sK1,sK0) | spl5_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f138])).
% 0.19/0.48  fof(f138,plain,(
% 0.19/0.48    spl5_11 <=> v1_tops_1(sK1,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.19/0.48  fof(f304,plain,(
% 0.19/0.48    v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl5_27),
% 0.19/0.48    inference(trivial_inequality_removal,[],[f303])).
% 0.19/0.48  fof(f303,plain,(
% 0.19/0.48    k1_xboole_0 != k1_xboole_0 | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl5_27),
% 0.19/0.48    inference(superposition,[],[f72,f287])).
% 0.19/0.48  fof(f287,plain,(
% 0.19/0.48    k1_xboole_0 = sK4(sK0,sK1) | ~spl5_27),
% 0.19/0.48    inference(avatar_component_clause,[],[f285])).
% 0.19/0.48  fof(f285,plain,(
% 0.19/0.48    spl5_27 <=> k1_xboole_0 = sK4(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.19/0.48  fof(f72,plain,(
% 0.19/0.48    ( ! [X0,X1] : (k1_xboole_0 != sK4(X0,X1) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f45])).
% 0.19/0.48  fof(f45,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | (r1_xboole_0(X1,sK4(X0,X1)) & v3_pre_topc(sK4(X0,X1),X0) & k1_xboole_0 != sK4(X0,X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f43,f44])).
% 0.19/0.48  fof(f44,plain,(
% 0.19/0.48    ! [X1,X0] : (? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (r1_xboole_0(X1,sK4(X0,X1)) & v3_pre_topc(sK4(X0,X1),X0) & k1_xboole_0 != sK4(X0,X1) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f43,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | ? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X3] : (~r1_xboole_0(X1,X3) | ~v3_pre_topc(X3,X0) | k1_xboole_0 = X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.48    inference(rectify,[],[f42])).
% 0.19/0.48  fof(f42,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (((v1_tops_1(X1,X0) | ? [X2] : (r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2 & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f24])).
% 0.19/0.48  fof(f24,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> ! [X2] : (~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.48    inference(flattening,[],[f23])).
% 0.19/0.48  fof(f23,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> ! [X2] : ((~r1_xboole_0(X1,X2) | ~v3_pre_topc(X2,X0) | k1_xboole_0 = X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f3])).
% 0.19/0.48  fof(f3,axiom,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_xboole_0(X1,X2) & v3_pre_topc(X2,X0) & k1_xboole_0 != X2)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_tops_1)).
% 0.19/0.48  fof(f292,plain,(
% 0.19/0.48    spl5_27 | spl5_28 | ~spl5_6 | spl5_11 | ~spl5_26),
% 0.19/0.48    inference(avatar_split_clause,[],[f283,f275,f138,f104,f289,f285])).
% 0.19/0.48  fof(f289,plain,(
% 0.19/0.48    spl5_28 <=> u1_struct_0(sK0) = sK4(sK0,sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.19/0.48  fof(f275,plain,(
% 0.19/0.48    spl5_26 <=> ! [X0] : (k1_xboole_0 = sK4(sK0,X0) | u1_struct_0(sK0) = sK4(sK0,X0) | v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.19/0.48  fof(f283,plain,(
% 0.19/0.48    u1_struct_0(sK0) = sK4(sK0,sK1) | k1_xboole_0 = sK4(sK0,sK1) | (~spl5_6 | spl5_11 | ~spl5_26)),
% 0.19/0.48    inference(subsumption_resolution,[],[f279,f139])).
% 0.19/0.48  fof(f279,plain,(
% 0.19/0.48    u1_struct_0(sK0) = sK4(sK0,sK1) | v1_tops_1(sK1,sK0) | k1_xboole_0 = sK4(sK0,sK1) | (~spl5_6 | ~spl5_26)),
% 0.19/0.48    inference(resolution,[],[f276,f106])).
% 0.19/0.48  fof(f276,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = sK4(sK0,X0) | v1_tops_1(X0,sK0) | k1_xboole_0 = sK4(sK0,X0)) ) | ~spl5_26),
% 0.19/0.48    inference(avatar_component_clause,[],[f275])).
% 0.19/0.48  fof(f277,plain,(
% 0.19/0.48    spl5_26 | ~spl5_2 | ~spl5_4 | ~spl5_13 | ~spl5_17),
% 0.19/0.48    inference(avatar_split_clause,[],[f192,f185,f149,f94,f84,f275])).
% 0.19/0.48  fof(f149,plain,(
% 0.19/0.48    spl5_13 <=> ! [X0] : (m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.19/0.48  fof(f185,plain,(
% 0.19/0.48    spl5_17 <=> ! [X0] : (k1_xboole_0 = X0 | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 0.19/0.48  fof(f192,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = sK4(sK0,X0) | u1_struct_0(sK0) = sK4(sK0,X0) | v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_13 | ~spl5_17)),
% 0.19/0.48    inference(subsumption_resolution,[],[f191,f150])).
% 0.19/0.48  fof(f150,plain,(
% 0.19/0.48    ( ! [X0] : (m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | ~spl5_13),
% 0.19/0.48    inference(avatar_component_clause,[],[f149])).
% 0.19/0.48  fof(f191,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = sK4(sK0,X0) | ~m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = sK4(sK0,X0) | v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl5_2 | ~spl5_4 | ~spl5_17)),
% 0.19/0.48    inference(subsumption_resolution,[],[f190,f86])).
% 0.19/0.48  fof(f190,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = sK4(sK0,X0) | ~m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = sK4(sK0,X0) | v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0)) ) | (~spl5_4 | ~spl5_17)),
% 0.19/0.48    inference(subsumption_resolution,[],[f189,f96])).
% 0.19/0.48  fof(f189,plain,(
% 0.19/0.48    ( ! [X0] : (k1_xboole_0 = sK4(sK0,X0) | ~m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = sK4(sK0,X0) | v1_tops_1(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl5_17),
% 0.19/0.48    inference(resolution,[],[f186,f73])).
% 0.19/0.48  fof(f73,plain,(
% 0.19/0.48    ( ! [X0,X1] : (v3_pre_topc(sK4(X0,X1),X0) | v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f45])).
% 0.19/0.48  fof(f186,plain,(
% 0.19/0.48    ( ! [X0] : (~v3_pre_topc(X0,sK0) | k1_xboole_0 = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X0) ) | ~spl5_17),
% 0.19/0.48    inference(avatar_component_clause,[],[f185])).
% 0.19/0.48  fof(f263,plain,(
% 0.19/0.48    ~spl5_23 | spl5_5 | ~spl5_12),
% 0.19/0.48    inference(avatar_split_clause,[],[f243,f142,f99,f260])).
% 0.19/0.48  fof(f260,plain,(
% 0.19/0.48    spl5_23 <=> r1_tarski(sK1,sK4(sK0,sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.19/0.48  fof(f99,plain,(
% 0.19/0.48    spl5_5 <=> v1_xboole_0(sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.19/0.48  fof(f142,plain,(
% 0.19/0.48    spl5_12 <=> r1_xboole_0(sK1,sK4(sK0,sK1))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.19/0.48  fof(f243,plain,(
% 0.19/0.48    ~r1_tarski(sK1,sK4(sK0,sK1)) | (spl5_5 | ~spl5_12)),
% 0.19/0.48    inference(subsumption_resolution,[],[f242,f101])).
% 0.19/0.48  fof(f101,plain,(
% 0.19/0.48    ~v1_xboole_0(sK1) | spl5_5),
% 0.19/0.48    inference(avatar_component_clause,[],[f99])).
% 0.19/0.48  fof(f242,plain,(
% 0.19/0.48    ~r1_tarski(sK1,sK4(sK0,sK1)) | v1_xboole_0(sK1) | ~spl5_12),
% 0.19/0.48    inference(resolution,[],[f144,f75])).
% 0.19/0.48  fof(f75,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f26])).
% 0.19/0.48  fof(f26,plain,(
% 0.19/0.48    ! [X0,X1] : (~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0) | v1_xboole_0(X1))),
% 0.19/0.48    inference(flattening,[],[f25])).
% 0.19/0.48  fof(f25,plain,(
% 0.19/0.48    ! [X0,X1] : ((~r1_xboole_0(X1,X0) | ~r1_tarski(X1,X0)) | v1_xboole_0(X1))),
% 0.19/0.48    inference(ennf_transformation,[],[f1])).
% 0.19/0.48  fof(f1,axiom,(
% 0.19/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ~(r1_xboole_0(X1,X0) & r1_tarski(X1,X0)))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).
% 0.19/0.48  fof(f144,plain,(
% 0.19/0.48    r1_xboole_0(sK1,sK4(sK0,sK1)) | ~spl5_12),
% 0.19/0.48    inference(avatar_component_clause,[],[f142])).
% 0.19/0.48  fof(f256,plain,(
% 0.19/0.48    spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6 | spl5_8 | ~spl5_20),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f254])).
% 0.19/0.48  fof(f254,plain,(
% 0.19/0.48    $false | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | spl5_5 | ~spl5_6 | spl5_8 | ~spl5_20)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f81,f86,f91,f96,f101,f210,f106,f114,f61])).
% 0.19/0.48  fof(f61,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | v1_zfmisc_1(X1) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f37])).
% 0.19/0.48  fof(f37,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (((v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1)) & (v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f16])).
% 0.19/0.48  fof(f16,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f15])).
% 0.19/0.48  fof(f15,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f7])).
% 0.19/0.48  fof(f7,axiom,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.19/0.48  fof(f114,plain,(
% 0.19/0.48    ~v1_zfmisc_1(sK1) | spl5_8),
% 0.19/0.48    inference(avatar_component_clause,[],[f113])).
% 0.19/0.48  fof(f113,plain,(
% 0.19/0.48    spl5_8 <=> v1_zfmisc_1(sK1)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.19/0.48  fof(f210,plain,(
% 0.19/0.48    v2_tex_2(sK1,sK0) | ~spl5_20),
% 0.19/0.48    inference(avatar_component_clause,[],[f208])).
% 0.19/0.48  fof(f208,plain,(
% 0.19/0.48    spl5_20 <=> v2_tex_2(sK1,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 0.19/0.48  fof(f91,plain,(
% 0.19/0.48    v2_tdlat_3(sK0) | ~spl5_3),
% 0.19/0.48    inference(avatar_component_clause,[],[f89])).
% 0.19/0.48  fof(f89,plain,(
% 0.19/0.48    spl5_3 <=> v2_tdlat_3(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.19/0.48  fof(f81,plain,(
% 0.19/0.48    ~v2_struct_0(sK0) | spl5_1),
% 0.19/0.48    inference(avatar_component_clause,[],[f79])).
% 0.19/0.48  fof(f79,plain,(
% 0.19/0.48    spl5_1 <=> v2_struct_0(sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.19/0.48  fof(f227,plain,(
% 0.19/0.48    spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_11 | ~spl5_20),
% 0.19/0.48    inference(avatar_contradiction_clause,[],[f222])).
% 0.19/0.48  fof(f222,plain,(
% 0.19/0.48    $false | (spl5_1 | ~spl5_2 | ~spl5_4 | ~spl5_6 | spl5_7 | ~spl5_11 | ~spl5_20)),
% 0.19/0.48    inference(unit_resulting_resolution,[],[f81,f86,f96,f110,f140,f106,f210,f63])).
% 0.19/0.48  fof(f63,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f18])).
% 0.19/0.48  fof(f18,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    inference(flattening,[],[f17])).
% 0.19/0.48  fof(f17,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.48    inference(ennf_transformation,[],[f8])).
% 0.19/0.48  fof(f8,axiom,(
% 0.19/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 0.19/0.48  fof(f140,plain,(
% 0.19/0.48    v1_tops_1(sK1,sK0) | ~spl5_11),
% 0.19/0.48    inference(avatar_component_clause,[],[f138])).
% 0.19/0.48  fof(f110,plain,(
% 0.19/0.48    ~v3_tex_2(sK1,sK0) | spl5_7),
% 0.19/0.48    inference(avatar_component_clause,[],[f109])).
% 0.19/0.48  fof(f109,plain,(
% 0.19/0.48    spl5_7 <=> v3_tex_2(sK1,sK0)),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.19/0.48  fof(f220,plain,(
% 0.19/0.48    spl5_20 | spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_19),
% 0.19/0.48    inference(avatar_split_clause,[],[f219,f198,f104,f94,f89,f84,f79,f208])).
% 0.19/0.48  fof(f198,plain,(
% 0.19/0.48    spl5_19 <=> ! [X0] : (v2_tex_2(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.19/0.48  fof(f219,plain,(
% 0.19/0.48    v2_tex_2(sK1,sK0) | (spl5_1 | ~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_19)),
% 0.19/0.48    inference(subsumption_resolution,[],[f218,f81])).
% 0.19/0.48  fof(f218,plain,(
% 0.19/0.48    v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | (~spl5_2 | ~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_19)),
% 0.19/0.48    inference(subsumption_resolution,[],[f217,f86])).
% 0.19/0.48  fof(f217,plain,(
% 0.19/0.48    v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_3 | ~spl5_4 | ~spl5_6 | ~spl5_19)),
% 0.19/0.48    inference(subsumption_resolution,[],[f216,f91])).
% 0.19/0.48  fof(f216,plain,(
% 0.19/0.48    v2_tex_2(sK1,sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_4 | ~spl5_6 | ~spl5_19)),
% 0.19/0.48    inference(subsumption_resolution,[],[f215,f96])).
% 0.19/0.48  fof(f215,plain,(
% 0.19/0.48    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~v2_pre_topc(sK0) | v2_struct_0(sK0) | (~spl5_6 | ~spl5_19)),
% 0.19/0.48    inference(resolution,[],[f199,f106])).
% 0.19/0.48  fof(f199,plain,(
% 0.19/0.48    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(sK1,X0) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_19),
% 0.19/0.48    inference(avatar_component_clause,[],[f198])).
% 0.19/0.48  fof(f211,plain,(
% 0.19/0.48    spl5_20 | ~spl5_4 | ~spl5_6 | ~spl5_7),
% 0.19/0.48    inference(avatar_split_clause,[],[f206,f109,f104,f94,f208])).
% 0.19/0.48  fof(f206,plain,(
% 0.19/0.48    v2_tex_2(sK1,sK0) | (~spl5_4 | ~spl5_6 | ~spl5_7)),
% 0.19/0.48    inference(subsumption_resolution,[],[f205,f96])).
% 0.19/0.48  fof(f205,plain,(
% 0.19/0.48    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | (~spl5_6 | ~spl5_7)),
% 0.19/0.48    inference(subsumption_resolution,[],[f202,f106])).
% 0.19/0.48  fof(f202,plain,(
% 0.19/0.48    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl5_7),
% 0.19/0.48    inference(resolution,[],[f111,f55])).
% 0.19/0.48  fof(f55,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.19/0.48    inference(cnf_transformation,[],[f36])).
% 0.19/0.48  fof(f36,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f34,f35])).
% 0.19/0.48  fof(f35,plain,(
% 0.19/0.48    ! [X1,X0] : (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) => (sK2(X0,X1) != X1 & r1_tarski(X1,sK2(X0,X1)) & v2_tex_2(sK2(X0,X1),X0) & m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.48    introduced(choice_axiom,[])).
% 0.19/0.48  fof(f34,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X3] : (X1 = X3 | ~r1_tarski(X1,X3) | ~v2_tex_2(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(rectify,[],[f33])).
% 0.19/0.48  fof(f33,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | ? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0)) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(flattening,[],[f32])).
% 0.19/0.48  fof(f32,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : (((v3_tex_2(X1,X0) | (? [X2] : (X1 != X2 & r1_tarski(X1,X2) & v2_tex_2(X2,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tex_2(X1,X0))) & ((! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0)) | ~v3_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(nnf_transformation,[],[f14])).
% 0.19/0.48  fof(f14,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(flattening,[],[f13])).
% 0.19/0.48  fof(f13,plain,(
% 0.19/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.19/0.48    inference(ennf_transformation,[],[f4])).
% 0.19/0.48  fof(f4,axiom,(
% 0.19/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.19/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.19/0.48  fof(f111,plain,(
% 0.19/0.48    v3_tex_2(sK1,sK0) | ~spl5_7),
% 0.19/0.48    inference(avatar_component_clause,[],[f109])).
% 0.19/0.48  fof(f200,plain,(
% 0.19/0.48    spl5_19 | ~spl5_8),
% 0.19/0.48    inference(avatar_split_clause,[],[f166,f113,f198])).
% 0.19/0.48  fof(f166,plain,(
% 0.19/0.48    ( ! [X0] : (v2_tex_2(sK1,X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) ) | ~spl5_8),
% 0.19/0.48    inference(resolution,[],[f163,f115])).
% 0.19/0.48  fof(f115,plain,(
% 0.19/0.48    v1_zfmisc_1(sK1) | ~spl5_8),
% 0.19/0.48    inference(avatar_component_clause,[],[f113])).
% 0.19/0.48  fof(f163,plain,(
% 0.19/0.48    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.48    inference(subsumption_resolution,[],[f62,f64])).
% 0.19/0.49  fof(f64,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f20])).
% 0.19/0.49  fof(f20,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f19])).
% 0.19/0.49  fof(f19,plain,(
% 0.19/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f6])).
% 0.19/0.49  fof(f6,axiom,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_tex_2)).
% 0.19/0.49  fof(f62,plain,(
% 0.19/0.49    ( ! [X0,X1] : (v2_tex_2(X1,X0) | ~v1_zfmisc_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f37])).
% 0.19/0.49  fof(f187,plain,(
% 0.19/0.49    spl5_17 | ~spl5_2 | ~spl5_3 | ~spl5_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f180,f94,f89,f84,f185])).
% 0.19/0.49  fof(f180,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X0) ) | (~spl5_2 | ~spl5_3 | ~spl5_4)),
% 0.19/0.49    inference(subsumption_resolution,[],[f179,f86])).
% 0.19/0.49  fof(f179,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X0 | ~v2_pre_topc(sK0)) ) | (~spl5_3 | ~spl5_4)),
% 0.19/0.49    inference(subsumption_resolution,[],[f178,f96])).
% 0.19/0.49  fof(f178,plain,(
% 0.19/0.49    ( ! [X0] : (k1_xboole_0 = X0 | ~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = X0 | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl5_3),
% 0.19/0.49    inference(resolution,[],[f65,f91])).
% 0.19/0.49  fof(f65,plain,(
% 0.19/0.49    ( ! [X2,X0] : (~v2_tdlat_3(X0) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = X2 | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f41])).
% 0.19/0.49  fof(f41,plain,(
% 0.19/0.49    ! [X0] : (((v2_tdlat_3(X0) | (u1_struct_0(X0) != sK3(X0) & k1_xboole_0 != sK3(X0) & v3_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (u1_struct_0(X0) = X2 | k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f39,f40])).
% 0.19/0.49  fof(f40,plain,(
% 0.19/0.49    ! [X0] : (? [X1] : (u1_struct_0(X0) != X1 & k1_xboole_0 != X1 & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) => (u1_struct_0(X0) != sK3(X0) & k1_xboole_0 != sK3(X0) & v3_pre_topc(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f39,plain,(
% 0.19/0.49    ! [X0] : (((v2_tdlat_3(X0) | ? [X1] : (u1_struct_0(X0) != X1 & k1_xboole_0 != X1 & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X2] : (u1_struct_0(X0) = X2 | k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.49    inference(rectify,[],[f38])).
% 0.19/0.49  fof(f38,plain,(
% 0.19/0.49    ! [X0] : (((v2_tdlat_3(X0) | ? [X1] : (u1_struct_0(X0) != X1 & k1_xboole_0 != X1 & v3_pre_topc(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) & (! [X1] : (u1_struct_0(X0) = X1 | k1_xboole_0 = X1 | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~v2_tdlat_3(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.49    inference(nnf_transformation,[],[f22])).
% 0.19/0.49  fof(f22,plain,(
% 0.19/0.49    ! [X0] : ((v2_tdlat_3(X0) <=> ! [X1] : (u1_struct_0(X0) = X1 | k1_xboole_0 = X1 | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.19/0.49    inference(flattening,[],[f21])).
% 0.19/0.49  fof(f21,plain,(
% 0.19/0.49    ! [X0] : ((v2_tdlat_3(X0) <=> ! [X1] : ((u1_struct_0(X0) = X1 | k1_xboole_0 = X1 | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f5])).
% 0.19/0.49  fof(f5,axiom,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v2_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(u1_struct_0(X0) != X1 & k1_xboole_0 != X1 & v3_pre_topc(X1,X0)))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_tdlat_3)).
% 0.19/0.49  fof(f151,plain,(
% 0.19/0.49    spl5_13 | ~spl5_2 | ~spl5_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f147,f94,f84,f149])).
% 0.19/0.49  fof(f147,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | (~spl5_2 | ~spl5_4)),
% 0.19/0.49    inference(subsumption_resolution,[],[f146,f86])).
% 0.19/0.49  fof(f146,plain,(
% 0.19/0.49    ( ! [X0] : (m1_subset_1(sK4(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0) | ~v2_pre_topc(sK0)) ) | ~spl5_4),
% 0.19/0.49    inference(resolution,[],[f71,f96])).
% 0.19/0.49  fof(f71,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f45])).
% 0.19/0.49  fof(f145,plain,(
% 0.19/0.49    spl5_11 | spl5_12 | ~spl5_6 | ~spl5_10),
% 0.19/0.49    inference(avatar_split_clause,[],[f134,f131,f104,f142,f138])).
% 0.19/0.49  fof(f131,plain,(
% 0.19/0.49    spl5_10 <=> ! [X0] : (r1_xboole_0(X0,sK4(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.19/0.49  fof(f134,plain,(
% 0.19/0.49    r1_xboole_0(sK1,sK4(sK0,sK1)) | v1_tops_1(sK1,sK0) | (~spl5_6 | ~spl5_10)),
% 0.19/0.49    inference(resolution,[],[f132,f106])).
% 0.19/0.49  fof(f132,plain,(
% 0.19/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_xboole_0(X0,sK4(sK0,X0)) | v1_tops_1(X0,sK0)) ) | ~spl5_10),
% 0.19/0.49    inference(avatar_component_clause,[],[f131])).
% 0.19/0.49  fof(f133,plain,(
% 0.19/0.49    spl5_10 | ~spl5_2 | ~spl5_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f129,f94,f84,f131])).
% 0.19/0.49  fof(f129,plain,(
% 0.19/0.49    ( ! [X0] : (r1_xboole_0(X0,sK4(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0)) ) | (~spl5_2 | ~spl5_4)),
% 0.19/0.49    inference(subsumption_resolution,[],[f128,f86])).
% 0.19/0.49  fof(f128,plain,(
% 0.19/0.49    ( ! [X0] : (r1_xboole_0(X0,sK4(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(X0,sK0) | ~v2_pre_topc(sK0)) ) | ~spl5_4),
% 0.19/0.49    inference(resolution,[],[f74,f96])).
% 0.19/0.49  fof(f74,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | r1_xboole_0(X1,sK4(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_tops_1(X1,X0) | ~v2_pre_topc(X0)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f45])).
% 0.19/0.49  fof(f124,plain,(
% 0.19/0.49    spl5_9 | ~spl5_6),
% 0.19/0.49    inference(avatar_split_clause,[],[f119,f104,f121])).
% 0.19/0.49  fof(f121,plain,(
% 0.19/0.49    spl5_9 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.19/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.19/0.49  fof(f119,plain,(
% 0.19/0.49    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl5_6),
% 0.19/0.49    inference(resolution,[],[f76,f106])).
% 0.19/0.49  fof(f76,plain,(
% 0.19/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.19/0.49    inference(cnf_transformation,[],[f46])).
% 0.19/0.49  fof(f46,plain,(
% 0.19/0.49    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.19/0.49    inference(nnf_transformation,[],[f2])).
% 0.19/0.49  fof(f2,axiom,(
% 0.19/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.19/0.49  fof(f118,plain,(
% 0.19/0.49    ~spl5_7 | ~spl5_8),
% 0.19/0.49    inference(avatar_split_clause,[],[f117,f113,f109])).
% 0.19/0.49  fof(f117,plain,(
% 0.19/0.49    ~v3_tex_2(sK1,sK0) | ~spl5_8),
% 0.19/0.49    inference(subsumption_resolution,[],[f54,f115])).
% 0.19/0.49  fof(f54,plain,(
% 0.19/0.49    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f31,plain,(
% 0.19/0.49    ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.19/0.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f28,f30,f29])).
% 0.19/0.49  fof(f29,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) & l1_pre_topc(sK0) & v2_tdlat_3(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f30,plain,(
% 0.19/0.49    ? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,sK0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(X1)) => ((~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)) & (v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) & ~v1_xboole_0(sK1))),
% 0.19/0.49    introduced(choice_axiom,[])).
% 0.19/0.49  fof(f28,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f27])).
% 0.19/0.49  fof(f27,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : (((~v1_zfmisc_1(X1) | ~v3_tex_2(X1,X0)) & (v1_zfmisc_1(X1) | v3_tex_2(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.49    inference(nnf_transformation,[],[f12])).
% 0.19/0.49  fof(f12,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.19/0.49    inference(flattening,[],[f11])).
% 0.19/0.49  fof(f11,plain,(
% 0.19/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.19/0.49    inference(ennf_transformation,[],[f10])).
% 0.19/0.49  fof(f10,negated_conjecture,(
% 0.19/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.19/0.49    inference(negated_conjecture,[],[f9])).
% 0.19/0.49  fof(f9,conjecture,(
% 0.19/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.19/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.19/0.49  fof(f116,plain,(
% 0.19/0.49    spl5_7 | spl5_8),
% 0.19/0.49    inference(avatar_split_clause,[],[f53,f113,f109])).
% 0.19/0.49  fof(f53,plain,(
% 0.19/0.49    v1_zfmisc_1(sK1) | v3_tex_2(sK1,sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f107,plain,(
% 0.19/0.49    spl5_6),
% 0.19/0.49    inference(avatar_split_clause,[],[f52,f104])).
% 0.19/0.49  fof(f52,plain,(
% 0.19/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f102,plain,(
% 0.19/0.49    ~spl5_5),
% 0.19/0.49    inference(avatar_split_clause,[],[f51,f99])).
% 0.19/0.49  fof(f51,plain,(
% 0.19/0.49    ~v1_xboole_0(sK1)),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f97,plain,(
% 0.19/0.49    spl5_4),
% 0.19/0.49    inference(avatar_split_clause,[],[f50,f94])).
% 0.19/0.49  fof(f50,plain,(
% 0.19/0.49    l1_pre_topc(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f92,plain,(
% 0.19/0.49    spl5_3),
% 0.19/0.49    inference(avatar_split_clause,[],[f49,f89])).
% 0.19/0.49  fof(f49,plain,(
% 0.19/0.49    v2_tdlat_3(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f87,plain,(
% 0.19/0.49    spl5_2),
% 0.19/0.49    inference(avatar_split_clause,[],[f48,f84])).
% 0.19/0.49  fof(f48,plain,(
% 0.19/0.49    v2_pre_topc(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  fof(f82,plain,(
% 0.19/0.49    ~spl5_1),
% 0.19/0.49    inference(avatar_split_clause,[],[f47,f79])).
% 0.19/0.49  fof(f47,plain,(
% 0.19/0.49    ~v2_struct_0(sK0)),
% 0.19/0.49    inference(cnf_transformation,[],[f31])).
% 0.19/0.49  % SZS output end Proof for theBenchmark
% 0.19/0.49  % (23567)------------------------------
% 0.19/0.49  % (23567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.49  % (23567)Termination reason: Refutation
% 0.19/0.49  
% 0.19/0.49  % (23567)Memory used [KB]: 6268
% 0.19/0.49  % (23567)Time elapsed: 0.069 s
% 0.19/0.49  % (23567)------------------------------
% 0.19/0.49  % (23567)------------------------------
% 0.19/0.49  % (23564)Success in time 0.131 s
%------------------------------------------------------------------------------
