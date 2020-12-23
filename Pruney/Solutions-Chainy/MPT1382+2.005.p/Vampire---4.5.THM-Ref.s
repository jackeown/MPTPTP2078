%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 245 expanded)
%              Number of leaves         :   25 (  86 expanded)
%              Depth                    :   13
%              Number of atoms          :  516 (1020 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f453,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f61,f66,f84,f89,f94,f171,f193,f363,f393,f405,f439,f442,f449,f452])).

fof(f452,plain,
    ( ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | spl4_33 ),
    inference(avatar_contradiction_clause,[],[f451])).

fof(f451,plain,
    ( $false
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | spl4_33 ),
    inference(subsumption_resolution,[],[f450,f93])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f450,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_3
    | spl4_33 ),
    inference(resolution,[],[f438,f79])).

fof(f79,plain,
    ( ! [X0] :
        ( v3_pre_topc(k1_tops_1(sK0,X0),sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f77,f60])).

fof(f60,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f58,plain,
    ( spl4_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f77,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v3_pre_topc(k1_tops_1(sK0,X0),sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f65,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f63,plain,
    ( spl4_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f438,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | spl4_33 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl4_33
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).

fof(f449,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_32 ),
    inference(avatar_contradiction_clause,[],[f448])).

fof(f448,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | spl4_32 ),
    inference(subsumption_resolution,[],[f447,f83])).

fof(f83,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl4_4
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f447,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | spl4_32 ),
    inference(subsumption_resolution,[],[f446,f88])).

fof(f88,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_5
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f446,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | spl4_32 ),
    inference(subsumption_resolution,[],[f444,f93])).

fof(f444,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_32 ),
    inference(resolution,[],[f434,f76])).

fof(f76,plain,
    ( ! [X4,X5] :
        ( r2_hidden(X4,k1_tops_1(sK0,X5))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_connsp_2(X5,sK0,X4) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f75,f65])).

fof(f75,plain,
    ( ! [X4,X5] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,k1_tops_1(sK0,X5))
        | ~ m1_connsp_2(X5,sK0,X4) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f69,f60])).

fof(f69,plain,
    ( ! [X4,X5] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | r2_hidden(X4,k1_tops_1(sK0,X5))
        | ~ m1_connsp_2(X5,sK0,X4) )
    | spl4_1 ),
    inference(resolution,[],[f55,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f55,plain,
    ( ~ v2_struct_0(sK0)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f53,plain,
    ( spl4_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f434,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl4_32 ),
    inference(avatar_component_clause,[],[f432])).

fof(f432,plain,
    ( spl4_32
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f442,plain,
    ( ~ spl4_14
    | spl4_31 ),
    inference(avatar_contradiction_clause,[],[f441])).

fof(f441,plain,
    ( $false
    | ~ spl4_14
    | spl4_31 ),
    inference(subsumption_resolution,[],[f440,f162])).

fof(f162,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f161,plain,
    ( spl4_14
  <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f440,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl4_31 ),
    inference(resolution,[],[f427,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f427,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_31 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl4_31
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f439,plain,
    ( ~ spl4_31
    | ~ spl4_32
    | ~ spl4_33
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_16 ),
    inference(avatar_split_clause,[],[f402,f168,f63,f58,f53,f436,f432,f425])).

fof(f168,plain,
    ( spl4_16
  <=> m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f402,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | spl4_16 ),
    inference(resolution,[],[f170,f72])).

fof(f72,plain,
    ( ! [X0,X1] :
        ( m1_connsp_2(X0,sK0,X1)
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(X1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f71,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f71,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(X1,X0)
        | m1_connsp_2(X0,sK0,X1) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f70,f65])).

% (5831)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
fof(f70,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(X1,X0)
        | m1_connsp_2(X0,sK0,X1) )
    | spl4_1
    | ~ spl4_2 ),
    inference(subsumption_resolution,[],[f67,f60])).

fof(f67,plain,
    ( ! [X0,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r2_hidden(X1,X0)
        | m1_connsp_2(X0,sK0,X1) )
    | spl4_1 ),
    inference(resolution,[],[f55,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_connsp_2(X1,X0,X2)
              | ~ r2_hidden(X2,X1)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
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
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( ( r2_hidden(X2,X1)
                  & v3_pre_topc(X1,X0) )
               => m1_connsp_2(X1,X0,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

fof(f170,plain,
    ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
    | spl4_16 ),
    inference(avatar_component_clause,[],[f168])).

fof(f405,plain,
    ( spl4_14
    | spl4_27 ),
    inference(avatar_split_clause,[],[f395,f390,f161])).

fof(f390,plain,
    ( spl4_27
  <=> r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f395,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl4_27 ),
    inference(resolution,[],[f392,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

fof(f392,plain,
    ( ~ r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),k1_tops_1(sK0,sK2))
    | spl4_27 ),
    inference(avatar_component_clause,[],[f390])).

fof(f393,plain,
    ( ~ spl4_27
    | ~ spl4_3
    | ~ spl4_6
    | spl4_18 ),
    inference(avatar_split_clause,[],[f381,f190,f91,f63,f390])).

fof(f190,plain,
    ( spl4_18
  <=> r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f381,plain,
    ( ~ r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),k1_tops_1(sK0,sK2))
    | ~ spl4_3
    | ~ spl4_6
    | spl4_18 ),
    inference(subsumption_resolution,[],[f380,f93])).

fof(f380,plain,
    ( ~ r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3
    | spl4_18 ),
    inference(resolution,[],[f242,f78])).

fof(f78,plain,
    ( ! [X1] :
        ( r1_tarski(k1_tops_1(sK0,X1),X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_3 ),
    inference(resolution,[],[f65,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f242,plain,
    ( ! [X0] :
        ( ~ r1_tarski(X0,sK2)
        | ~ r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),X0) )
    | spl4_18 ),
    inference(resolution,[],[f192,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f192,plain,
    ( ~ r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),sK2)
    | spl4_18 ),
    inference(avatar_component_clause,[],[f190])).

fof(f363,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(avatar_contradiction_clause,[],[f362])).

fof(f362,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f361,f83])).

fof(f361,plain,
    ( ~ m1_connsp_2(sK2,sK0,sK1)
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(resolution,[],[f250,f88])).

fof(f250,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK2,sK0,X1) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_15 ),
    inference(subsumption_resolution,[],[f248,f93])).

fof(f248,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK2,sK0,X1) )
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_15 ),
    inference(resolution,[],[f243,f76])).

fof(f243,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_tops_1(sK0,sK2))
    | ~ spl4_15 ),
    inference(resolution,[],[f237,f51])).

fof(f51,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f237,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_tops_1(sK0,sK2))
        | ~ r2_hidden(X0,X1) )
    | ~ spl4_15 ),
    inference(resolution,[],[f166,f46])).

fof(f166,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
        | ~ r2_hidden(X1,X0) )
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f165])).

fof(f165,plain,
    ( spl4_15
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
        | ~ r2_hidden(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f193,plain,
    ( ~ spl4_18
    | ~ spl4_6
    | spl4_14 ),
    inference(avatar_split_clause,[],[f172,f161,f91,f190])).

fof(f172,plain,
    ( ~ r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),sK2)
    | ~ spl4_6
    | spl4_14 ),
    inference(resolution,[],[f163,f104])).

fof(f104,plain,
    ( ! [X0] :
        ( r1_tarski(X0,u1_struct_0(sK0))
        | ~ r2_hidden(sK3(X0,u1_struct_0(sK0)),sK2) )
    | ~ spl4_6 ),
    inference(resolution,[],[f97,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f97,plain,
    ( ! [X1] :
        ( r2_hidden(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK2) )
    | ~ spl4_6 ),
    inference(resolution,[],[f93,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f163,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
    | spl4_14 ),
    inference(avatar_component_clause,[],[f161])).

fof(f171,plain,
    ( ~ spl4_14
    | spl4_15
    | ~ spl4_16
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f146,f91,f63,f58,f168,f165,f161])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
        | ~ r2_hidden(X1,X0)
        | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) )
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f145,f93])).

fof(f145,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
        | ~ r2_hidden(X1,X0)
        | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(duplicate_literal_removal,[],[f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2)))
        | ~ r2_hidden(X1,X0)
        | ~ r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f128,f78])).

fof(f128,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(sK0,X0)))
        | ~ r2_hidden(X2,X1)
        | ~ r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0)) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f124,f46])).

fof(f124,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK2)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(sK0,X0)))
        | ~ r2_hidden(X2,X1) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f106,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f106,plain,
    ( ! [X0] :
        ( v1_xboole_0(k1_tops_1(sK0,X0))
        | ~ m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(k1_tops_1(sK0,X0),sK2) )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(resolution,[],[f79,f27])).

fof(f27,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK1)
      | v1_xboole_0(X3)
      | ~ r1_tarski(X3,sK2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ! [X3] :
                  ( ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_connsp_2(X3,X0,X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                  | v1_xboole_0(X3) )
              & m1_connsp_2(X2,X0,X1)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
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
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( ! [X3] :
                        ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                          & ~ v1_xboole_0(X3) )
                       => ~ ( r1_tarski(X3,X2)
                            & v3_pre_topc(X3,X0)
                            & m1_connsp_2(X3,X0,X1) ) )
                    & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ~ ( ! [X3] :
                      ( ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                        & ~ v1_xboole_0(X3) )
                     => ~ ( r1_tarski(X3,X2)
                          & v3_pre_topc(X3,X0)
                          & m1_connsp_2(X3,X0,X1) ) )
                  & m1_connsp_2(X2,X0,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).

fof(f94,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f28,f91])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f89,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f30,f86])).

fof(f30,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f84,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f29,f81])).

fof(f29,plain,(
    m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f66,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f56,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f31,f53])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:57:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.49  % (5851)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.50  % (5843)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (5835)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.51  % (5836)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.52  % (5851)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.53  % (5858)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f453,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f56,f61,f66,f84,f89,f94,f171,f193,f363,f393,f405,f439,f442,f449,f452])).
% 0.21/0.53  fof(f452,plain,(
% 0.21/0.53    ~spl4_2 | ~spl4_3 | ~spl4_6 | spl4_33),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f451])).
% 0.21/0.53  fof(f451,plain,(
% 0.21/0.53    $false | (~spl4_2 | ~spl4_3 | ~spl4_6 | spl4_33)),
% 0.21/0.53    inference(subsumption_resolution,[],[f450,f93])).
% 0.21/0.53  fof(f93,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f91])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    spl4_6 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.53  fof(f450,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_3 | spl4_33)),
% 0.21/0.53    inference(resolution,[],[f438,f79])).
% 0.21/0.53  fof(f79,plain,(
% 0.21/0.53    ( ! [X0] : (v3_pre_topc(k1_tops_1(sK0,X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f77,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    v2_pre_topc(sK0) | ~spl4_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f58])).
% 0.21/0.53  fof(f58,plain,(
% 0.21/0.53    spl4_2 <=> v2_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.53  fof(f77,plain,(
% 0.21/0.53    ( ! [X0] : (~v2_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k1_tops_1(sK0,X0),sK0)) ) | ~spl4_3),
% 0.21/0.53    inference(resolution,[],[f65,f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    l1_pre_topc(sK0) | ~spl4_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    spl4_3 <=> l1_pre_topc(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.53  fof(f438,plain,(
% 0.21/0.53    ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | spl4_33),
% 0.21/0.53    inference(avatar_component_clause,[],[f436])).
% 0.21/0.53  fof(f436,plain,(
% 0.21/0.53    spl4_33 <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_33])])).
% 0.21/0.53  fof(f449,plain,(
% 0.21/0.53    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_32),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f448])).
% 0.21/0.53  fof(f448,plain,(
% 0.21/0.53    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | spl4_32)),
% 0.21/0.53    inference(subsumption_resolution,[],[f447,f83])).
% 0.21/0.53  fof(f83,plain,(
% 0.21/0.53    m1_connsp_2(sK2,sK0,sK1) | ~spl4_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f81])).
% 0.21/0.53  fof(f81,plain,(
% 0.21/0.53    spl4_4 <=> m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.53  fof(f447,plain,(
% 0.21/0.53    ~m1_connsp_2(sK2,sK0,sK1) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | spl4_32)),
% 0.21/0.53    inference(subsumption_resolution,[],[f446,f88])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0)) | ~spl4_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl4_5 <=> m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.53  fof(f446,plain,(
% 0.21/0.53    ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_connsp_2(sK2,sK0,sK1) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | spl4_32)),
% 0.21/0.53    inference(subsumption_resolution,[],[f444,f93])).
% 0.21/0.53  fof(f444,plain,(
% 0.21/0.53    ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,u1_struct_0(sK0)) | ~m1_connsp_2(sK2,sK0,sK1) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_32)),
% 0.21/0.53    inference(resolution,[],[f434,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X4,X5] : (r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_connsp_2(X5,sK0,X4)) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f75,f65])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) ) | (spl4_1 | ~spl4_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f69,f60])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X4,X5] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,u1_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(X4,k1_tops_1(sK0,X5)) | ~m1_connsp_2(X5,sK0,X4)) ) | spl4_1),
% 0.21/0.53    inference(resolution,[],[f55,f36])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    ~v2_struct_0(sK0) | spl4_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f53])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    spl4_1 <=> v2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.53  fof(f434,plain,(
% 0.21/0.53    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl4_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f432])).
% 0.21/0.53  fof(f432,plain,(
% 0.21/0.53    spl4_32 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 0.21/0.53  fof(f442,plain,(
% 0.21/0.53    ~spl4_14 | spl4_31),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f441])).
% 0.21/0.53  fof(f441,plain,(
% 0.21/0.53    $false | (~spl4_14 | spl4_31)),
% 0.21/0.53    inference(subsumption_resolution,[],[f440,f162])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~spl4_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f161])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    spl4_14 <=> r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.53  fof(f440,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl4_31),
% 0.21/0.53    inference(resolution,[],[f427,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.53  fof(f427,plain,(
% 0.21/0.53    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_31),
% 0.21/0.53    inference(avatar_component_clause,[],[f425])).
% 0.21/0.53  fof(f425,plain,(
% 0.21/0.53    spl4_31 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.53  fof(f439,plain,(
% 0.21/0.53    ~spl4_31 | ~spl4_32 | ~spl4_33 | spl4_1 | ~spl4_2 | ~spl4_3 | spl4_16),
% 0.21/0.53    inference(avatar_split_clause,[],[f402,f168,f63,f58,f53,f436,f432,f425])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    spl4_16 <=> m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.53  fof(f402,plain,(
% 0.21/0.53    ~v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (spl4_1 | ~spl4_2 | ~spl4_3 | spl4_16)),
% 0.21/0.53    inference(resolution,[],[f170,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_connsp_2(X0,sK0,X1) | ~v3_pre_topc(X0,sK0) | ~r2_hidden(X1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f71,f48])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(flattening,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v3_pre_topc(X0,sK0) | ~r2_hidden(X1,X0) | m1_connsp_2(X0,sK0,X1)) ) | (spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.53    inference(subsumption_resolution,[],[f70,f65])).
% 0.21/0.53  % (5831)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v3_pre_topc(X0,sK0) | ~r2_hidden(X1,X0) | m1_connsp_2(X0,sK0,X1)) ) | (spl4_1 | ~spl4_2)),
% 0.21/0.53    inference(subsumption_resolution,[],[f67,f60])).
% 0.21/0.53  fof(f67,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v3_pre_topc(X0,sK0) | ~r2_hidden(X1,X0) | m1_connsp_2(X0,sK0,X1)) ) | spl4_1),
% 0.21/0.53    inference(resolution,[],[f55,f37])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.21/0.53  fof(f170,plain,(
% 0.21/0.53    ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | spl4_16),
% 0.21/0.53    inference(avatar_component_clause,[],[f168])).
% 0.21/0.53  fof(f405,plain,(
% 0.21/0.53    spl4_14 | spl4_27),
% 0.21/0.53    inference(avatar_split_clause,[],[f395,f390,f161])).
% 0.21/0.53  fof(f390,plain,(
% 0.21/0.53    spl4_27 <=> r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),k1_tops_1(sK0,sK2))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.21/0.53  fof(f395,plain,(
% 0.21/0.53    r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl4_27),
% 0.21/0.53    inference(resolution,[],[f392,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.21/0.53  fof(f392,plain,(
% 0.21/0.53    ~r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) | spl4_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f390])).
% 0.21/0.53  fof(f393,plain,(
% 0.21/0.53    ~spl4_27 | ~spl4_3 | ~spl4_6 | spl4_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f381,f190,f91,f63,f390])).
% 0.21/0.53  fof(f190,plain,(
% 0.21/0.53    spl4_18 <=> r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.21/0.53  fof(f381,plain,(
% 0.21/0.53    ~r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) | (~spl4_3 | ~spl4_6 | spl4_18)),
% 0.21/0.53    inference(subsumption_resolution,[],[f380,f93])).
% 0.21/0.53  fof(f380,plain,(
% 0.21/0.53    ~r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),k1_tops_1(sK0,sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_3 | spl4_18)),
% 0.21/0.53    inference(resolution,[],[f242,f78])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(k1_tops_1(sK0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl4_3),
% 0.21/0.53    inference(resolution,[],[f65,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f8])).
% 0.21/0.53  fof(f8,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.53  fof(f242,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_tarski(X0,sK2) | ~r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),X0)) ) | spl4_18),
% 0.21/0.53    inference(resolution,[],[f192,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    ~r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),sK2) | spl4_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f190])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_15),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f362])).
% 0.21/0.53  fof(f362,plain,(
% 0.21/0.53    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_15)),
% 0.21/0.53    inference(subsumption_resolution,[],[f361,f83])).
% 0.21/0.53  fof(f361,plain,(
% 0.21/0.53    ~m1_connsp_2(sK2,sK0,sK1) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_5 | ~spl4_6 | ~spl4_15)),
% 0.21/0.53    inference(resolution,[],[f250,f88])).
% 0.21/0.53  fof(f250,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_connsp_2(sK2,sK0,X1)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_15)),
% 0.21/0.53    inference(subsumption_resolution,[],[f248,f93])).
% 0.21/0.53  fof(f248,plain,(
% 0.21/0.53    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~m1_connsp_2(sK2,sK0,X1)) ) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_15)),
% 0.21/0.53    inference(resolution,[],[f243,f76])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK2))) ) | ~spl4_15),
% 0.21/0.53    inference(resolution,[],[f237,f51])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.53    inference(equality_resolution,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.21/0.53    inference(cnf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.53  fof(f237,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_tarski(X1,k1_tops_1(sK0,sK2)) | ~r2_hidden(X0,X1)) ) | ~spl4_15),
% 0.21/0.53    inference(resolution,[],[f166,f46])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | ~r2_hidden(X1,X0)) ) | ~spl4_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f165])).
% 0.21/0.53  fof(f165,plain,(
% 0.21/0.53    spl4_15 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | ~r2_hidden(X1,X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    ~spl4_18 | ~spl4_6 | spl4_14),
% 0.21/0.53    inference(avatar_split_clause,[],[f172,f161,f91,f190])).
% 0.21/0.53  fof(f172,plain,(
% 0.21/0.53    ~r2_hidden(sK3(k1_tops_1(sK0,sK2),u1_struct_0(sK0)),sK2) | (~spl4_6 | spl4_14)),
% 0.21/0.53    inference(resolution,[],[f163,f104])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    ( ! [X0] : (r1_tarski(X0,u1_struct_0(sK0)) | ~r2_hidden(sK3(X0,u1_struct_0(sK0)),sK2)) ) | ~spl4_6),
% 0.21/0.53    inference(resolution,[],[f97,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r2_hidden(sK3(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f23])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    ( ! [X1] : (r2_hidden(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK2)) ) | ~spl4_6),
% 0.21/0.53    inference(resolution,[],[f93,f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | spl4_14),
% 0.21/0.53    inference(avatar_component_clause,[],[f161])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    ~spl4_14 | spl4_15 | ~spl4_16 | ~spl4_2 | ~spl4_3 | ~spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f146,f91,f63,f58,f168,f165,f161])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | ~r2_hidden(X1,X0) | ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))) ) | (~spl4_2 | ~spl4_3 | ~spl4_6)),
% 0.21/0.53    inference(subsumption_resolution,[],[f145,f93])).
% 0.21/0.53  fof(f145,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | ~r2_hidden(X1,X0) | ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0))) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.53    inference(duplicate_literal_removal,[],[f144])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(k1_tops_1(sK0,sK2),sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k1_tops_1(sK0,sK2))) | ~r2_hidden(X1,X0) | ~r1_tarski(k1_tops_1(sK0,sK2),u1_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.53    inference(resolution,[],[f128,f78])).
% 0.21/0.53  fof(f128,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_tarski(k1_tops_1(sK0,X0),sK2) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(sK0,X0))) | ~r2_hidden(X2,X1) | ~r1_tarski(k1_tops_1(sK0,X0),u1_struct_0(sK0))) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.53    inference(resolution,[],[f124,f46])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),sK2) | ~m1_subset_1(X1,k1_zfmisc_1(k1_tops_1(sK0,X0))) | ~r2_hidden(X2,X1)) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.53    inference(resolution,[],[f106,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    ( ! [X0] : (v1_xboole_0(k1_tops_1(sK0,X0)) | ~m1_subset_1(k1_tops_1(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(k1_tops_1(sK0,X0),sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k1_tops_1(sK0,X0),sK2)) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.53    inference(resolution,[],[f79,f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ( ! [X3] : (~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK1) | v1_xboole_0(X3) | ~r1_tarski(X3,sK2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (! [X3] : (~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3)) & m1_connsp_2(X2,X0,X1) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : ((! [X3] : ((~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_connsp_2(X3,X0,X1)) | (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X3))) & m1_connsp_2(X2,X0,X1)) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.53    inference(negated_conjecture,[],[f11])).
% 0.21/0.53  fof(f11,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X3)) => ~(r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_connsp_2(X3,X0,X1))) & m1_connsp_2(X2,X0,X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_connsp_2)).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl4_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f28,f91])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f89,plain,(
% 0.21/0.53    spl4_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f30,f86])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    m1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    spl4_4),
% 0.21/0.53    inference(avatar_split_clause,[],[f29,f81])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    m1_connsp_2(sK2,sK0,sK1)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    spl4_3),
% 0.21/0.53    inference(avatar_split_clause,[],[f33,f63])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    l1_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    spl4_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f32,f58])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    v2_pre_topc(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~spl4_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f31,f53])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ~v2_struct_0(sK0)),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (5851)------------------------------
% 0.21/0.53  % (5851)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (5851)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (5851)Memory used [KB]: 11001
% 0.21/0.53  % (5851)Time elapsed: 0.099 s
% 0.21/0.53  % (5851)------------------------------
% 0.21/0.53  % (5851)------------------------------
% 0.21/0.53  % (5830)Success in time 0.169 s
%------------------------------------------------------------------------------
