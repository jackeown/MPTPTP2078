%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1268+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 334 expanded)
%              Number of leaves         :   25 ( 140 expanded)
%              Depth                    :   10
%              Number of atoms          :  501 (1204 expanded)
%              Number of equality atoms :   30 (  78 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f582,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f38,f42,f46,f72,f77,f165,f169,f182,f205,f212,f216,f217,f255,f298,f316,f320,f383,f399,f414,f464,f470,f581])).

fof(f581,plain,
    ( ~ spl4_19
    | spl4_25
    | ~ spl4_26
    | ~ spl4_35
    | ~ spl4_45 ),
    inference(avatar_contradiction_clause,[],[f580])).

fof(f580,plain,
    ( $false
    | ~ spl4_19
    | spl4_25
    | ~ spl4_26
    | ~ spl4_35
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f579,f211])).

fof(f211,plain,
    ( k1_xboole_0 != sK2
    | spl4_25 ),
    inference(avatar_component_clause,[],[f210])).

fof(f210,plain,
    ( spl4_25
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f579,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_19
    | ~ spl4_26
    | ~ spl4_35
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f578,f181])).

fof(f181,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl4_19
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f578,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | k1_xboole_0 = sK2
    | ~ spl4_26
    | ~ spl4_35
    | ~ spl4_45 ),
    inference(subsumption_resolution,[],[f577,f215])).

fof(f215,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f214])).

fof(f214,plain,
    ( spl4_26
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f577,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK2,sK0)
    | k1_xboole_0 = sK2
    | ~ spl4_35
    | ~ spl4_45 ),
    inference(resolution,[],[f315,f469])).

fof(f469,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK2)
    | ~ spl4_45 ),
    inference(avatar_component_clause,[],[f468])).

fof(f468,plain,
    ( spl4_45
  <=> r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_45])])).

fof(f315,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0 )
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl4_35
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v3_pre_topc(X0,sK0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f470,plain,
    ( spl4_45
    | ~ spl4_44 ),
    inference(avatar_split_clause,[],[f466,f462,f468])).

fof(f462,plain,
    ( spl4_44
  <=> r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_44])])).

fof(f466,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK2)
    | ~ spl4_44 ),
    inference(resolution,[],[f463,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | r1_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f463,plain,
    ( r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_44 ),
    inference(avatar_component_clause,[],[f462])).

fof(f464,plain,
    ( spl4_44
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_26 ),
    inference(avatar_split_clause,[],[f448,f214,f70,f44,f462])).

fof(f44,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f70,plain,
    ( spl4_5
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f448,plain,
    ( r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f446,f71])).

fof(f71,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f446,plain,
    ( ~ r1_tarski(sK2,sK1)
    | r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_3
    | ~ spl4_26 ),
    inference(resolution,[],[f409,f45])).

fof(f45,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f44])).

fof(f409,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X1)
        | r1_xboole_0(sK2,k3_subset_1(u1_struct_0(sK0),X1)) )
    | ~ spl4_26 ),
    inference(resolution,[],[f215,f29])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ r1_tarski(X1,X2)
      | r1_xboole_0(X1,k3_subset_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( r1_xboole_0(X1,k3_subset_1(X0,X2))
          <=> r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_subset_1)).

fof(f414,plain,
    ( spl4_4
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f173,f160,f44,f40,f67])).

fof(f67,plain,
    ( spl4_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f40,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f160,plain,
    ( spl4_16
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f173,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f172,f41])).

fof(f41,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f40])).

fof(f172,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tops_1(sK1,sK0)
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f171,f45])).

fof(f171,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_tops_1(sK1,sK0)
    | ~ spl4_16 ),
    inference(resolution,[],[f161,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_1)).

fof(f161,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f399,plain,
    ( ~ spl4_3
    | ~ spl4_24
    | spl4_31
    | ~ spl4_36 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_24
    | spl4_31
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f397,f204])).

fof(f204,plain,
    ( m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f203])).

fof(f203,plain,
    ( spl4_24
  <=> m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f397,plain,
    ( ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | spl4_31
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f396,f297])).

fof(f297,plain,
    ( ~ r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | spl4_31 ),
    inference(avatar_component_clause,[],[f296])).

fof(f296,plain,
    ( spl4_31
  <=> r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f396,plain,
    ( r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | ~ spl4_36 ),
    inference(subsumption_resolution,[],[f394,f45])).

fof(f394,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_36 ),
    inference(resolution,[],[f319,f30])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f319,plain,
    ( r1_xboole_0(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_36 ),
    inference(avatar_component_clause,[],[f318])).

fof(f318,plain,
    ( spl4_36
  <=> r1_xboole_0(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_36])])).

fof(f383,plain,
    ( ~ spl4_4
    | ~ spl4_2
    | ~ spl4_3
    | spl4_16 ),
    inference(avatar_split_clause,[],[f376,f160,f44,f40,f67])).

fof(f376,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_16 ),
    inference(subsumption_resolution,[],[f55,f312])).

fof(f312,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f55,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f47,f41])).

fof(f47,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f45,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f320,plain,
    ( spl4_36
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f299,f253,f318])).

fof(f253,plain,
    ( spl4_28
  <=> r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f299,plain,
    ( r1_xboole_0(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ spl4_28 ),
    inference(resolution,[],[f254,f34])).

fof(f254,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f253])).

fof(f316,plain,
    ( ~ spl4_16
    | spl4_35
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f106,f75,f40,f36,f314,f160])).

fof(f36,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f75,plain,
    ( spl4_6
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f106,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f105,f37])).

fof(f37,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f36])).

fof(f105,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f97,f41])).

fof(f97,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl4_6 ),
    inference(resolution,[],[f76,f24])).

fof(f24,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_tops_1)).

fof(f76,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f298,plain,
    ( ~ spl4_31
    | spl4_4
    | spl4_17
    | ~ spl4_18
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f247,f203,f167,f163,f67,f296])).

fof(f163,plain,
    ( spl4_17
  <=> k1_xboole_0 = sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f167,plain,
    ( spl4_18
  <=> v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f247,plain,
    ( ~ r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | spl4_4
    | spl4_17
    | ~ spl4_18
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f246,f164])).

fof(f164,plain,
    ( k1_xboole_0 != sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | spl4_17 ),
    inference(avatar_component_clause,[],[f163])).

fof(f246,plain,
    ( ~ r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | k1_xboole_0 = sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | spl4_4
    | ~ spl4_18
    | ~ spl4_24 ),
    inference(subsumption_resolution,[],[f245,f168])).

fof(f168,plain,
    ( v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f167])).

fof(f245,plain,
    ( ~ r1_tarski(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK1)
    | ~ v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | k1_xboole_0 = sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | spl4_4
    | ~ spl4_24 ),
    inference(resolution,[],[f218,f204])).

fof(f218,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1)
        | ~ v3_pre_topc(X2,sK0)
        | k1_xboole_0 = X2 )
    | spl4_4 ),
    inference(subsumption_resolution,[],[f20,f68])).

fof(f68,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl4_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f20,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f255,plain,
    ( spl4_16
    | spl4_28
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f114,f75,f40,f36,f253,f160])).

fof(f114,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f113,f37])).

fof(f113,plain,
    ( ~ v2_pre_topc(sK0)
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f101,f41])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f76,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | r1_xboole_0(X1,sK3(X0,X1))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f217,plain,
    ( ~ spl4_4
    | spl4_26 ),
    inference(avatar_split_clause,[],[f16,f214,f67])).

fof(f16,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f216,plain,
    ( spl4_26
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f176,f160,f44,f40,f214])).

fof(f176,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f16,f173])).

fof(f212,plain,
    ( ~ spl4_25
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f206,f160,f44,f40,f210])).

fof(f206,plain,
    ( k1_xboole_0 != sK2
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f19,f173])).

fof(f19,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f205,plain,
    ( spl4_16
    | spl4_24
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f108,f75,f40,f36,f203,f160])).

fof(f108,plain,
    ( m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f107,f37])).

fof(f107,plain,
    ( ~ v2_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f98,f41])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | m1_subset_1(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f76,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | m1_subset_1(sK3(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f182,plain,
    ( spl4_19
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(avatar_split_clause,[],[f177,f160,f44,f40,f180])).

fof(f177,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_16 ),
    inference(subsumption_resolution,[],[f18,f173])).

fof(f18,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f169,plain,
    ( spl4_16
    | spl4_18
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f112,f75,f40,f36,f167,f160])).

fof(f112,plain,
    ( v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f111,f37])).

fof(f111,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f100,f41])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f76,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(sK3(X0,X1),X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f165,plain,
    ( spl4_16
    | ~ spl4_17
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f110,f75,f40,f36,f163,f160])).

fof(f110,plain,
    ( k1_xboole_0 != sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f109,f37])).

fof(f109,plain,
    ( ~ v2_pre_topc(sK0)
    | k1_xboole_0 != sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | k1_xboole_0 != sK3(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl4_6 ),
    inference(resolution,[],[f76,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | k1_xboole_0 != sK3(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f77,plain,
    ( spl4_6
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f44,f75])).

fof(f53,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(resolution,[],[f45,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f72,plain,
    ( ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f17,f70,f67])).

fof(f17,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f46,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f21,f44])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f42,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f23,f40])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f38,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f22,f36])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
