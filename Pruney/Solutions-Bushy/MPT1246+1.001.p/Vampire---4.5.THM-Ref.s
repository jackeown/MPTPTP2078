%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1246+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:32 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  213 ( 534 expanded)
%              Number of leaves         :   31 ( 195 expanded)
%              Depth                    :   15
%              Number of atoms          :  976 (2353 expanded)
%              Number of equality atoms :   14 (  33 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f400,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f55,f60,f65,f80,f85,f94,f144,f164,f191,f194,f207,f210,f233,f246,f249,f264,f275,f295,f307,f316,f330,f377,f386,f388,f392,f399])).

fof(f399,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f398])).

fof(f398,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_12
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f397,f163])).

fof(f163,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl7_12
  <=> r2_hidden(sK2,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f397,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(resolution,[],[f396,f306])).

fof(f306,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f304])).

fof(f304,plain,
    ( spl7_19
  <=> r2_hidden(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f396,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f395,f84])).

fof(f84,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl7_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f395,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f394,f93])).

fof(f93,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl7_7
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f394,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(sK3,sK0)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_20
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f393,f315])).

fof(f315,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_20 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl7_20
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f393,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3,sK0)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,sK1)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_22 ),
    inference(resolution,[],[f329,f108])).

fof(f108,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_xboole_0(X0,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X2,sK0)
        | ~ r2_hidden(X1,X2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f71,f64])).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f62,plain,
    ( spl7_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f71,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X2,sK0)
        | ~ r2_hidden(X1,X2)
        | ~ r1_xboole_0(X0,X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f70,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f70,plain,
    ( ! [X2,X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X2,sK0)
        | ~ r2_hidden(X1,X2)
        | ~ r1_xboole_0(X0,X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f66,f54])).

fof(f54,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f52,plain,
    ( spl7_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f66,plain,
    ( ! [X2,X0,X1] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X2,sK0)
        | ~ r2_hidden(X1,X2)
        | ~ r1_xboole_0(X0,X2)
        | ~ r2_hidden(X1,k2_pre_topc(sK0,X0)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f59,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X3,X0)
      | ~ r2_hidden(X2,X3)
      | ~ r1_xboole_0(X1,X3)
      | ~ r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( ~ r1_xboole_0(X1,X3)
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_pre_topc(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ~ ( r1_xboole_0(X1,X3)
                        & r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_tops_1)).

fof(f59,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_2 ),
    inference(avatar_component_clause,[],[f57])).

fof(f57,plain,
    ( spl7_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f329,plain,
    ( r1_xboole_0(sK1,sK3)
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f327])).

fof(f327,plain,
    ( spl7_22
  <=> r1_xboole_0(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f392,plain,
    ( ~ spl7_18
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(avatar_split_clause,[],[f354,f323,f313,f304,f188,f91,f62,f57,f52,f230])).

fof(f230,plain,
    ( spl7_18
  <=> r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f188,plain,
    ( spl7_17
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f323,plain,
    ( spl7_21
  <=> r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f354,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_17
    | ~ spl7_19
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(resolution,[],[f334,f306])).

fof(f334,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_17
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f333,f189])).

fof(f189,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f188])).

fof(f333,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_7
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f332,f93])).

fof(f332,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(sK3,sK0)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_20
    | ~ spl7_21 ),
    inference(subsumption_resolution,[],[f331,f315])).

fof(f331,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(sK3,sK0)
        | ~ r2_hidden(X0,sK3)
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X0,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_21 ),
    inference(resolution,[],[f325,f108])).

fof(f325,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f323])).

fof(f388,plain,
    ( spl7_18
    | ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f387])).

fof(f387,plain,
    ( $false
    | spl7_18
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f383,f231])).

fof(f231,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f230])).

fof(f383,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl7_24 ),
    inference(resolution,[],[f376,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f376,plain,
    ( sP6(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl7_24
  <=> sP6(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f386,plain,
    ( spl7_12
    | ~ spl7_24 ),
    inference(avatar_contradiction_clause,[],[f385])).

fof(f385,plain,
    ( $false
    | spl7_12
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f382,f162])).

fof(f162,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f161])).

fof(f382,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl7_24 ),
    inference(resolution,[],[f376,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f377,plain,
    ( spl7_24
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f301,f87,f82,f62,f374])).

fof(f87,plain,
    ( spl7_6
  <=> r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f301,plain,
    ( sP6(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ spl7_3
    | ~ spl7_5
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f298,f84])).

fof(f298,plain,
    ( sP6(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)),k2_pre_topc(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_3
    | ~ spl7_6 ),
    inference(resolution,[],[f88,f116])).

fof(f116,plain,
    ( ! [X0,X1] :
        ( ~ r2_hidden(X1,k2_tops_1(sK0,X0))
        | sP6(X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_3 ),
    inference(superposition,[],[f49,f115])).

fof(f115,plain,
    ( ! [X0] :
        ( k2_tops_1(sK0,X0) = k3_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f114,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f114,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k3_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f113,f64])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_tops_1(sK0,X0) = k3_xboole_0(k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl7_3 ),
    inference(resolution,[],[f97,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f97,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1)),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k3_xboole_0(k2_pre_topc(sK0,X1),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X1))) = k2_tops_1(sK0,X1) )
    | ~ spl7_3 ),
    inference(superposition,[],[f75,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f75,plain,
    ( ! [X0] :
        ( k2_tops_1(sK0,X0) = k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl7_3 ),
    inference(resolution,[],[f64,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_1)).

fof(f49,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f88,plain,
    ( r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f330,plain,
    ( spl7_21
    | spl7_22
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f320,f87,f327,f323])).

fof(f320,plain,
    ( r1_xboole_0(sK1,sK3)
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f23,f88])).

fof(f23,plain,
    ( r1_xboole_0(sK1,sK3)
    | r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_tops_1(X0,X1))
              <~> ! [X3] :
                    ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                      & ~ r1_xboole_0(X1,X3) )
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r2_hidden(X2,k2_tops_1(X0,X1))
              <~> ! [X3] :
                    ( ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                      & ~ r1_xboole_0(X1,X3) )
                    | ~ r2_hidden(X2,X3)
                    | ~ v3_pre_topc(X3,X0)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              & m1_subset_1(X2,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ( r2_hidden(X2,k2_tops_1(X0,X1))
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => ( ( r2_hidden(X2,X3)
                          & v3_pre_topc(X3,X0) )
                       => ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                          & ~ r1_xboole_0(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( r2_hidden(X2,k2_tops_1(X0,X1))
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( r2_hidden(X2,X3)
                        & v3_pre_topc(X3,X0) )
                     => ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(X0),X1),X3)
                        & ~ r1_xboole_0(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tops_1)).

fof(f316,plain,
    ( spl7_20
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f311,f87,f313])).

fof(f311,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f24,f88])).

fof(f24,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f307,plain,
    ( spl7_19
    | ~ spl7_6 ),
    inference(avatar_split_clause,[],[f302,f87,f304])).

fof(f302,plain,
    ( r2_hidden(sK2,sK3)
    | ~ spl7_6 ),
    inference(subsumption_resolution,[],[f26,f88])).

fof(f26,plain,
    ( r2_hidden(sK2,sK3)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f295,plain,
    ( ~ spl7_9
    | ~ spl7_11
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f287])).

fof(f287,plain,
    ( $false
    | ~ spl7_9
    | ~ spl7_11
    | spl7_12 ),
    inference(resolution,[],[f285,f135])).

fof(f135,plain,
    ( r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | ~ spl7_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl7_9
  <=> r2_hidden(sK2,sK4(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f285,plain,
    ( ! [X0] : ~ r2_hidden(sK2,X0)
    | ~ spl7_11
    | spl7_12 ),
    inference(subsumption_resolution,[],[f279,f162])).

fof(f279,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | r2_hidden(sK2,k2_pre_topc(sK0,sK1)) )
    | ~ spl7_11 ),
    inference(resolution,[],[f143,f43])).

fof(f143,plain,
    ( ! [X0] :
        ( sP6(sK2,X0,k2_pre_topc(sK0,sK1))
        | ~ r2_hidden(sK2,X0) )
    | ~ spl7_11 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl7_11
  <=> ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | sP6(sK2,X0,k2_pre_topc(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f275,plain,
    ( ~ spl7_3
    | ~ spl7_5
    | spl7_6
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(avatar_contradiction_clause,[],[f274])).

fof(f274,plain,
    ( $false
    | ~ spl7_3
    | ~ spl7_5
    | spl7_6
    | ~ spl7_12
    | ~ spl7_18 ),
    inference(subsumption_resolution,[],[f228,f232])).

fof(f232,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl7_18 ),
    inference(avatar_component_clause,[],[f230])).

fof(f228,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl7_3
    | ~ spl7_5
    | spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f227,f84])).

fof(f227,plain,
    ( ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_3
    | spl7_6
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f226,f89])).

fof(f89,plain,
    ( ~ r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | spl7_6 ),
    inference(avatar_component_clause,[],[f87])).

fof(f226,plain,
    ( r2_hidden(sK2,k2_tops_1(sK0,sK1))
    | ~ r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl7_3
    | ~ spl7_12 ),
    inference(superposition,[],[f216,f115])).

fof(f216,plain,
    ( ! [X2] :
        ( r2_hidden(sK2,k3_xboole_0(k2_pre_topc(sK0,sK1),X2))
        | ~ r2_hidden(sK2,X2) )
    | ~ spl7_12 ),
    inference(resolution,[],[f212,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f212,plain,
    ( ! [X2] :
        ( sP6(sK2,X2,k2_pre_topc(sK0,sK1))
        | ~ r2_hidden(sK2,X2) )
    | ~ spl7_12 ),
    inference(resolution,[],[f163,f42])).

fof(f42,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f264,plain,
    ( ~ spl7_12
    | ~ spl7_16
    | spl7_18 ),
    inference(avatar_contradiction_clause,[],[f261])).

fof(f261,plain,
    ( $false
    | ~ spl7_12
    | ~ spl7_16
    | spl7_18 ),
    inference(resolution,[],[f255,f163])).

fof(f255,plain,
    ( ! [X0] : ~ r2_hidden(sK2,X0)
    | ~ spl7_16
    | spl7_18 ),
    inference(subsumption_resolution,[],[f252,f231])).

fof(f252,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) )
    | ~ spl7_16 ),
    inference(resolution,[],[f186,f43])).

fof(f186,plain,
    ( ! [X1] :
        ( sP6(sK2,X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ r2_hidden(sK2,X1) )
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f185])).

fof(f185,plain,
    ( spl7_16
  <=> ! [X1] :
        ( ~ r2_hidden(sK2,X1)
        | sP6(sK2,X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f249,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_13
    | ~ spl7_17
    | spl7_18 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_13
    | ~ spl7_17
    | spl7_18 ),
    inference(subsumption_resolution,[],[f205,f231])).

fof(f205,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_13
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f204,f54])).

fof(f204,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_13
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f203,f79])).

fof(f79,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f77])).

fof(f77,plain,
    ( spl7_4
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f203,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_13
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f202,f189])).

fof(f202,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_13 ),
    inference(subsumption_resolution,[],[f201,f64])).

fof(f201,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl7_2
    | spl7_13 ),
    inference(subsumption_resolution,[],[f200,f59])).

fof(f200,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl7_13 ),
    inference(resolution,[],[f175,f34])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f175,plain,
    ( ~ m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_13 ),
    inference(avatar_component_clause,[],[f173])).

fof(f173,plain,
    ( spl7_13
  <=> m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_13])])).

fof(f246,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_15
    | ~ spl7_17
    | spl7_18 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_15
    | ~ spl7_17
    | spl7_18 ),
    inference(subsumption_resolution,[],[f199,f231])).

fof(f199,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_15
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f198,f189])).

fof(f198,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_15 ),
    inference(subsumption_resolution,[],[f197,f79])).

fof(f197,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_15 ),
    inference(resolution,[],[f183,f99])).

fof(f99,plain,
    ( ! [X4,X3] :
        ( v3_pre_topc(sK4(sK0,X3,X4),sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,k2_pre_topc(sK0,X3)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f72,f64])).

fof(f72,plain,
    ( ! [X4,X3] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v3_pre_topc(sK4(sK0,X3,X4),sK0)
        | r2_hidden(X4,k2_pre_topc(sK0,X3)) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f67,f54])).

fof(f67,plain,
    ( ! [X4,X3] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | v3_pre_topc(sK4(sK0,X3,X4),sK0)
        | r2_hidden(X4,k2_pre_topc(sK0,X3)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f59,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | v3_pre_topc(sK4(X0,X1,X2),X0)
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f183,plain,
    ( ~ v3_pre_topc(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),sK0)
    | spl7_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl7_15
  <=> v3_pre_topc(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_15])])).

fof(f233,plain,
    ( spl7_18
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_14
    | ~ spl7_17 ),
    inference(avatar_split_clause,[],[f196,f188,f177,f77,f62,f57,f52,f230])).

fof(f177,plain,
    ( spl7_14
  <=> r2_hidden(sK2,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_14])])).

fof(f196,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_14
    | ~ spl7_17 ),
    inference(subsumption_resolution,[],[f195,f189])).

fof(f195,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_14 ),
    inference(resolution,[],[f179,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,sK4(sK0,X0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(sK2,k2_pre_topc(sK0,X0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f100,f79])).

fof(f100,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X6,sK4(sK0,X5,X6))
        | r2_hidden(X6,k2_pre_topc(sK0,X5)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f73,f64])).

fof(f73,plain,
    ( ! [X6,X5] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(X6,sK4(sK0,X5,X6))
        | r2_hidden(X6,k2_pre_topc(sK0,X5)) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f68,f54])).

fof(f68,plain,
    ( ! [X6,X5] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(X6,sK4(sK0,X5,X6))
        | r2_hidden(X6,k2_pre_topc(sK0,X5)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f59,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r2_hidden(X2,sK4(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f179,plain,
    ( ~ r2_hidden(sK2,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2))
    | spl7_14 ),
    inference(avatar_component_clause,[],[f177])).

fof(f210,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_8
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f209])).

fof(f209,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_8
    | spl7_12 ),
    inference(subsumption_resolution,[],[f155,f162])).

fof(f155,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_8 ),
    inference(subsumption_resolution,[],[f154,f54])).

fof(f154,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_8 ),
    inference(subsumption_resolution,[],[f153,f79])).

fof(f153,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_5
    | spl7_8 ),
    inference(subsumption_resolution,[],[f152,f84])).

fof(f152,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl7_2
    | ~ spl7_3
    | spl7_8 ),
    inference(subsumption_resolution,[],[f151,f64])).

fof(f151,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | ~ spl7_2
    | spl7_8 ),
    inference(subsumption_resolution,[],[f150,f59])).

fof(f150,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl7_8 ),
    inference(resolution,[],[f132,f34])).

fof(f132,plain,
    ( ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl7_8
  <=> m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f207,plain,
    ( spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10
    | spl7_12 ),
    inference(avatar_contradiction_clause,[],[f206])).

fof(f206,plain,
    ( $false
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10
    | spl7_12 ),
    inference(subsumption_resolution,[],[f149,f162])).

fof(f149,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_10 ),
    inference(subsumption_resolution,[],[f148,f84])).

fof(f148,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_10 ),
    inference(subsumption_resolution,[],[f147,f79])).

fof(f147,plain,
    ( ~ m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | spl7_10 ),
    inference(resolution,[],[f140,f99])).

fof(f140,plain,
    ( ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
    | spl7_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f138,plain,
    ( spl7_10
  <=> v3_pre_topc(sK4(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f194,plain,
    ( ~ spl7_5
    | spl7_17 ),
    inference(avatar_contradiction_clause,[],[f193])).

fof(f193,plain,
    ( $false
    | ~ spl7_5
    | spl7_17 ),
    inference(subsumption_resolution,[],[f192,f84])).

fof(f192,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_17 ),
    inference(resolution,[],[f190,f38])).

fof(f190,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl7_17 ),
    inference(avatar_component_clause,[],[f188])).

fof(f191,plain,
    ( ~ spl7_13
    | ~ spl7_14
    | ~ spl7_15
    | spl7_16
    | ~ spl7_17
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6 ),
    inference(avatar_split_clause,[],[f118,f87,f77,f62,f57,f52,f188,f185,f181,f177,f173])).

fof(f118,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X1)
        | sP6(sK2,X1,k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
        | ~ v3_pre_topc(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),sK0)
        | ~ r2_hidden(sK2,sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2))
        | ~ m1_subset_1(sK4(sK0,k3_subset_1(u1_struct_0(sK0),sK1),sK2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6 ),
    inference(resolution,[],[f106,f96])).

fof(f96,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X3)
        | ~ v3_pre_topc(X3,sK0)
        | ~ r2_hidden(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_6 ),
    inference(subsumption_resolution,[],[f22,f89])).

fof(f22,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ r2_hidden(sK2,X3)
      | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X3)
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f106,plain,
    ( ! [X0,X1] :
        ( r1_xboole_0(X0,sK4(sK0,X0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X1)
        | sP6(sK2,X1,k2_pre_topc(sK0,X0)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f105,f42])).

fof(f105,plain,
    ( ! [X0] :
        ( r2_hidden(sK2,k2_pre_topc(sK0,X0))
        | r1_xboole_0(X0,sK4(sK0,X0,sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4 ),
    inference(resolution,[],[f104,f79])).

fof(f104,plain,
    ( ! [X8,X7] :
        ( ~ m1_subset_1(X8,u1_struct_0(sK0))
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | r1_xboole_0(X7,sK4(sK0,X7,X8))
        | r2_hidden(X8,k2_pre_topc(sK0,X7)) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3 ),
    inference(subsumption_resolution,[],[f74,f64])).

fof(f74,plain,
    ( ! [X8,X7] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r1_xboole_0(X7,sK4(sK0,X7,X8))
        | r2_hidden(X8,k2_pre_topc(sK0,X7)) )
    | spl7_1
    | ~ spl7_2 ),
    inference(subsumption_resolution,[],[f69,f54])).

fof(f69,plain,
    ( ! [X8,X7] :
        ( v2_struct_0(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X8,u1_struct_0(sK0))
        | r1_xboole_0(X7,sK4(sK0,X7,X8))
        | r2_hidden(X8,k2_pre_topc(sK0,X7)) )
    | ~ spl7_2 ),
    inference(resolution,[],[f59,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | r1_xboole_0(X1,sK4(X0,X1,X2))
      | r2_hidden(X2,k2_pre_topc(X0,X1)) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f164,plain,
    ( spl7_12
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(avatar_split_clause,[],[f146,f134,f82,f77,f62,f57,f52,f161])).

fof(f146,plain,
    ( r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_9 ),
    inference(subsumption_resolution,[],[f145,f84])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2,k2_pre_topc(sK0,sK1))
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_9 ),
    inference(resolution,[],[f136,f101])).

fof(f136,plain,
    ( ~ r2_hidden(sK2,sK4(sK0,sK1,sK2))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f134])).

fof(f144,plain,
    ( ~ spl7_8
    | ~ spl7_9
    | ~ spl7_10
    | spl7_11
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(avatar_split_clause,[],[f121,f87,f82,f77,f62,f57,f52,f142,f138,f134,f130])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK2,X0)
        | sP6(sK2,X0,k2_pre_topc(sK0,sK1))
        | ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
        | ~ r2_hidden(sK2,sK4(sK0,sK1,sK2))
        | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | spl7_6 ),
    inference(subsumption_resolution,[],[f117,f84])).

fof(f117,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK2,X0)
        | sP6(sK2,X0,k2_pre_topc(sK0,sK1))
        | ~ v3_pre_topc(sK4(sK0,sK1,sK2),sK0)
        | ~ r2_hidden(sK2,sK4(sK0,sK1,sK2))
        | ~ m1_subset_1(sK4(sK0,sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_1
    | ~ spl7_2
    | ~ spl7_3
    | ~ spl7_4
    | spl7_6 ),
    inference(resolution,[],[f106,f95])).

fof(f95,plain,
    ( ! [X3] :
        ( ~ r1_xboole_0(sK1,X3)
        | ~ v3_pre_topc(X3,sK0)
        | ~ r2_hidden(sK2,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl7_6 ),
    inference(subsumption_resolution,[],[f21,f89])).

fof(f21,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X3,sK0)
      | ~ r2_hidden(sK2,X3)
      | ~ r1_xboole_0(sK1,X3)
      | r2_hidden(sK2,k2_tops_1(sK0,sK1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f94,plain,
    ( ~ spl7_6
    | spl7_7 ),
    inference(avatar_split_clause,[],[f25,f91,f87])).

fof(f25,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ r2_hidden(sK2,k2_tops_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f85,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f28,f82])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f80,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f27,f77])).

fof(f27,plain,(
    m1_subset_1(sK2,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f65,plain,(
    spl7_3 ),
    inference(avatar_split_clause,[],[f31,f62])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f60,plain,(
    spl7_2 ),
    inference(avatar_split_clause,[],[f30,f57])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f55,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f29,f52])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

%------------------------------------------------------------------------------
