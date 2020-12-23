%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1707+1.002 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n027.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:22 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 271 expanded)
%              Number of leaves         :   31 (  95 expanded)
%              Depth                    :   17
%              Number of atoms          :  563 (1245 expanded)
%              Number of equality atoms :   36 ( 124 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f610,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f86,f91,f96,f110,f115,f122,f127,f132,f160,f176,f195,f386,f430,f464,f567,f580,f600,f609])).

fof(f609,plain,
    ( ~ spl7_16
    | spl7_48 ),
    inference(avatar_contradiction_clause,[],[f608])).

fof(f608,plain,
    ( $false
    | ~ spl7_16
    | spl7_48 ),
    inference(subsumption_resolution,[],[f607,f151])).

fof(f151,plain,
    ( l1_pre_topc(sK1)
    | ~ spl7_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f150,plain,
    ( spl7_16
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_16])])).

fof(f607,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_48 ),
    inference(resolution,[],[f599,f38])).

fof(f38,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f599,plain,
    ( ~ l1_struct_0(sK1)
    | spl7_48 ),
    inference(avatar_component_clause,[],[f597])).

fof(f597,plain,
    ( spl7_48
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_48])])).

fof(f600,plain,
    ( ~ spl7_48
    | spl7_2
    | ~ spl7_45 ),
    inference(avatar_split_clause,[],[f589,f564,f68,f597])).

fof(f68,plain,
    ( spl7_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f564,plain,
    ( spl7_45
  <=> v1_xboole_0(u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_45])])).

fof(f589,plain,
    ( ~ l1_struct_0(sK1)
    | spl7_2
    | ~ spl7_45 ),
    inference(subsumption_resolution,[],[f587,f70])).

fof(f70,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f587,plain,
    ( ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl7_45 ),
    inference(resolution,[],[f566,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f566,plain,
    ( v1_xboole_0(u1_struct_0(sK1))
    | ~ spl7_45 ),
    inference(avatar_component_clause,[],[f564])).

fof(f580,plain,(
    ~ spl7_44 ),
    inference(avatar_contradiction_clause,[],[f578])).

fof(f578,plain,
    ( $false
    | ~ spl7_44 ),
    inference(resolution,[],[f562,f43])).

fof(f43,plain,(
    ! [X0] : m1_subset_1(sK4(X0),X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f562,plain,
    ( ! [X2] : ~ m1_subset_1(X2,u1_struct_0(sK1))
    | ~ spl7_44 ),
    inference(avatar_component_clause,[],[f561])).

fof(f561,plain,
    ( spl7_44
  <=> ! [X2] : ~ m1_subset_1(X2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_44])])).

fof(f567,plain,
    ( spl7_44
    | spl7_45
    | ~ spl7_32
    | ~ spl7_37 ),
    inference(avatar_split_clause,[],[f530,f461,f383,f564,f561])).

fof(f383,plain,
    ( spl7_32
  <=> u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f461,plain,
    ( spl7_37
  <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_37])])).

fof(f530,plain,
    ( ! [X2] :
        ( v1_xboole_0(u1_struct_0(sK1))
        | ~ m1_subset_1(X2,u1_struct_0(sK1)) )
    | ~ spl7_32
    | ~ spl7_37 ),
    inference(resolution,[],[f525,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f525,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_struct_0(sK1))
    | ~ spl7_32
    | ~ spl7_37 ),
    inference(resolution,[],[f520,f50])).

fof(f50,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f520,plain,
    ( ! [X4] : ~ sP6(X4,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl7_32
    | ~ spl7_37 ),
    inference(subsumption_resolution,[],[f396,f469])).

fof(f469,plain,
    ( ! [X0] : ~ r2_hidden(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl7_37 ),
    inference(resolution,[],[f463,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

fof(f463,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl7_37 ),
    inference(avatar_component_clause,[],[f461])).

fof(f396,plain,
    ( ! [X4] :
        ( r2_hidden(X4,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
        | ~ sP6(X4,u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl7_32 ),
    inference(superposition,[],[f61,f385])).

fof(f385,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f383])).

fof(f61,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,k2_xboole_0(X0,X1))
      | ~ sP6(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP6(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f464,plain,
    ( spl7_37
    | ~ spl7_10
    | spl7_34 ),
    inference(avatar_split_clause,[],[f440,f427,f119,f461])).

fof(f119,plain,
    ( spl7_10
  <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_10])])).

fof(f427,plain,
    ( spl7_34
  <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_34])])).

fof(f440,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl7_10
    | spl7_34 ),
    inference(subsumption_resolution,[],[f439,f121])).

fof(f121,plain,
    ( m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl7_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f439,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | spl7_34 ),
    inference(resolution,[],[f429,f45])).

fof(f429,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | spl7_34 ),
    inference(avatar_component_clause,[],[f427])).

fof(f430,plain,
    ( ~ spl7_34
    | spl7_20
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f394,f383,f192,f427])).

fof(f192,plain,
    ( spl7_20
  <=> r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_20])])).

fof(f394,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | spl7_20
    | ~ spl7_32 ),
    inference(superposition,[],[f194,f385])).

fof(f194,plain,
    ( ~ r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl7_20 ),
    inference(avatar_component_clause,[],[f192])).

fof(f386,plain,
    ( spl7_32
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f277,f93,f88,f83,f73,f68,f63,f383])).

fof(f63,plain,
    ( spl7_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f73,plain,
    ( spl7_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f83,plain,
    ( spl7_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f88,plain,
    ( spl7_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f93,plain,
    ( spl7_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f277,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f274,f65])).

fof(f65,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f274,plain,
    ( v2_struct_0(sK2)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f262,f90])).

fof(f90,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f262,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) )
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f259,f70])).

fof(f259,plain,
    ( ! [X1] :
        ( v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(sK1)
        | k2_xboole_0(u1_struct_0(sK1),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,sK1,X1)) )
    | spl7_3
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(resolution,[],[f252,f95])).

fof(f95,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f93])).

fof(f252,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f205,f224])).

fof(f224,plain,
    ( ! [X4,X5] :
        ( m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X4) )
    | spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f105,f85])).

fof(f85,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f83])).

fof(f105,plain,
    ( ! [X4,X5] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,X4,X5),sK0) )
    | spl7_3 ),
    inference(resolution,[],[f75,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

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

fof(f75,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f204,f181])).

fof(f181,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f103,f85])).

fof(f103,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ v2_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl7_3 ),
    inference(resolution,[],[f75,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f204,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(k1_tsep_1(sK0,X0,X1))
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f203,f75])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(k1_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f202,f85])).

fof(f202,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(k1_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl7_3
    | ~ spl7_5 ),
    inference(duplicate_literal_removal,[],[f201])).

fof(f201,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(k1_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X0,X1),sK0)
        | k2_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k1_tsep_1(sK0,X0,X1)) )
    | spl7_3
    | ~ spl7_5 ),
    inference(resolution,[],[f196,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0)
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f196,plain,
    ( ! [X2,X3] :
        ( v1_pre_topc(k1_tsep_1(sK0,X2,X3))
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X2) )
    | spl7_3
    | ~ spl7_5 ),
    inference(subsumption_resolution,[],[f104,f85])).

fof(f104,plain,
    ( ! [X2,X3] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | v1_pre_topc(k1_tsep_1(sK0,X2,X3)) )
    | spl7_3 ),
    inference(resolution,[],[f75,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f195,plain,
    ( ~ spl7_20
    | spl7_18 ),
    inference(avatar_split_clause,[],[f180,f173,f192])).

fof(f173,plain,
    ( spl7_18
  <=> sP6(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f180,plain,
    ( ~ r2_hidden(sK3,k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)))
    | spl7_18 ),
    inference(resolution,[],[f175,f60])).

fof(f60,plain,(
    ! [X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,k2_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( sP6(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f175,plain,
    ( ~ sP6(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | spl7_18 ),
    inference(avatar_component_clause,[],[f173])).

fof(f176,plain,
    ( ~ spl7_18
    | spl7_11
    | spl7_12 ),
    inference(avatar_split_clause,[],[f162,f129,f124,f173])).

fof(f124,plain,
    ( spl7_11
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f129,plain,
    ( spl7_12
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f162,plain,
    ( ~ sP6(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | spl7_11
    | spl7_12 ),
    inference(resolution,[],[f133,f131])).

fof(f131,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl7_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f133,plain,
    ( ! [X0] :
        ( r2_hidden(sK3,X0)
        | ~ sP6(sK3,X0,u1_struct_0(sK1)) )
    | spl7_11 ),
    inference(resolution,[],[f126,f52])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X0)
      | r2_hidden(X3,X1)
      | ~ sP6(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f126,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f160,plain,
    ( ~ spl7_5
    | ~ spl7_7
    | spl7_16 ),
    inference(avatar_contradiction_clause,[],[f159])).

fof(f159,plain,
    ( $false
    | ~ spl7_5
    | ~ spl7_7
    | spl7_16 ),
    inference(subsumption_resolution,[],[f158,f85])).

fof(f158,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl7_7
    | spl7_16 ),
    inference(resolution,[],[f154,f95])).

fof(f154,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | spl7_16 ),
    inference(resolution,[],[f152,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( l1_pre_topc(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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

fof(f152,plain,
    ( ~ l1_pre_topc(sK1)
    | spl7_16 ),
    inference(avatar_component_clause,[],[f150])).

fof(f132,plain,
    ( ~ spl7_12
    | spl7_9 ),
    inference(avatar_split_clause,[],[f117,f112,f129])).

fof(f112,plain,
    ( spl7_9
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f117,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK2))
    | spl7_9 ),
    inference(resolution,[],[f114,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f114,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f112])).

fof(f127,plain,
    ( ~ spl7_11
    | spl7_8 ),
    inference(avatar_split_clause,[],[f116,f107,f124])).

fof(f107,plain,
    ( spl7_8
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_8])])).

fof(f116,plain,
    ( ~ r2_hidden(sK3,u1_struct_0(sK1))
    | spl7_8 ),
    inference(resolution,[],[f109,f44])).

fof(f109,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl7_8 ),
    inference(avatar_component_clause,[],[f107])).

fof(f122,plain,(
    spl7_10 ),
    inference(avatar_split_clause,[],[f30,f119])).

fof(f30,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,plain,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f12])).

fof(f12,negated_conjecture,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tmap_1)).

fof(f115,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f58,f112])).

fof(f58,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f28])).

fof(f28,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,(
    ~ spl7_8 ),
    inference(avatar_split_clause,[],[f57,f107])).

fof(f57,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f29])).

fof(f29,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f96,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f34,f93])).

fof(f34,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f91,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f32,f88])).

fof(f32,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f86,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f37,f83])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f76,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f35,f73])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f33,f68])).

fof(f33,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f15])).

%------------------------------------------------------------------------------
