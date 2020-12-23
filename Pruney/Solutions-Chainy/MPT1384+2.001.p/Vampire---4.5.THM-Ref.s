%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  133 ( 254 expanded)
%              Number of leaves         :   28 ( 104 expanded)
%              Depth                    :   16
%              Number of atoms          :  590 (1209 expanded)
%              Number of equality atoms :    6 (   9 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f396,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f88,f105,f119,f124,f133,f140,f145,f149,f162,f193,f203,f223,f231,f328,f390,f395])).

fof(f395,plain,
    ( ~ spl6_4
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl6_4
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f57,f154,f78,f144])).

fof(f144,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) )
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_16
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_connsp_2(X3,sK0,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f78,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f154,plain,
    ( m1_connsp_2(sK1,sK0,sK2)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl6_18
  <=> m1_connsp_2(sK1,sK0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f57,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
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

fof(f390,plain,
    ( ~ spl6_2
    | ~ spl6_4
    | ~ spl6_3
    | spl6_5
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f353,f126,f81,f71,f76,f66])).

fof(f66,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f71,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f81,plain,
    ( spl6_5
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f126,plain,
    ( spl6_13
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f353,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ spl6_13 ),
    inference(superposition,[],[f42,f128])).

fof(f128,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f42,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f328,plain,
    ( spl6_14
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f325,f229,f221,f201,f147,f138,f117,f76,f130])).

% (18323)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
fof(f130,plain,
    ( spl6_14
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f117,plain,
    ( spl6_11
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f138,plain,
    ( spl6_15
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK3(X2),sK0,X2)
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f147,plain,
    ( spl6_17
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f201,plain,
    ( spl6_23
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK1,sK0,X2)
        | r2_hidden(X2,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f221,plain,
    ( spl6_25
  <=> ! [X5,X6] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ m1_connsp_2(sK3(X5),sK0,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | r2_hidden(X6,k1_tops_1(sK0,sK3(X5)))
        | ~ r2_hidden(X5,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f229,plain,
    ( spl6_26
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | m1_connsp_2(sK1,sK0,X2)
        | ~ r2_hidden(X2,k1_tops_1(sK0,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f325,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(duplicate_literal_removal,[],[f323])).

fof(f323,plain,
    ( r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(resolution,[],[f322,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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

fof(f322,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(duplicate_literal_removal,[],[f321])).

fof(f321,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) )
    | ~ spl6_4
    | ~ spl6_11
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(resolution,[],[f320,f135])).

fof(f135,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(X0),sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(duplicate_literal_removal,[],[f134])).

fof(f134,plain,
    ( ! [X0] :
        ( r1_tarski(sK3(X0),sK1)
        | ~ r2_hidden(X0,sK1)
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_4
    | ~ spl6_11 ),
    inference(resolution,[],[f118,f93])).

fof(f93,plain,
    ( ! [X3] :
        ( m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f78,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f118,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | r1_tarski(sK3(X2),sK1)
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f117])).

fof(f320,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK3(sK4(X2,k1_tops_1(sK0,sK1))),sK1)
        | ~ r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X2,k1_tops_1(sK0,sK1)) )
    | ~ spl6_4
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(duplicate_literal_removal,[],[f319])).

fof(f319,plain,
    ( ! [X2] :
        ( ~ r1_tarski(sK3(sK4(X2,k1_tops_1(sK0,sK1))),sK1)
        | ~ r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X2,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1) )
    | ~ spl6_4
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(resolution,[],[f260,f93])).

fof(f260,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
        | ~ r1_tarski(sK3(sK4(X0,k1_tops_1(sK0,sK1))),sK1)
        | ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)
        | r1_tarski(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(duplicate_literal_removal,[],[f259])).

fof(f259,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK3(sK4(X0,k1_tops_1(sK0,sK1))),sK1)
        | ~ m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
        | ~ r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)
        | ~ m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
        | r1_tarski(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_23
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(resolution,[],[f257,f205])).

fof(f205,plain,
    ( ! [X1] :
        ( ~ m1_connsp_2(sK1,sK0,sK4(X1,k1_tops_1(sK0,sK1)))
        | ~ m1_subset_1(sK4(X1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0))
        | r1_tarski(X1,k1_tops_1(sK0,sK1)) )
    | ~ spl6_23 ),
    inference(resolution,[],[f202,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f202,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_tops_1(sK0,sK1))
        | ~ m1_connsp_2(sK1,sK0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0)) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f201])).

fof(f257,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,X0)
        | ~ r1_tarski(sK3(X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(duplicate_literal_removal,[],[f254])).

fof(f254,plain,
    ( ! [X0] :
        ( m1_connsp_2(sK1,sK0,X0)
        | ~ r1_tarski(sK3(X0),sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1) )
    | ~ spl6_15
    | ~ spl6_17
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(resolution,[],[f253,f139])).

fof(f139,plain,
    ( ! [X2] :
        ( m1_connsp_2(sK3(X2),sK0,X2)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f138])).

fof(f253,plain,
    ( ! [X0,X1] :
        ( ~ m1_connsp_2(sK3(X1),sK0,X0)
        | m1_connsp_2(sK1,sK0,X0)
        | ~ r1_tarski(sK3(X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl6_17
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(duplicate_literal_removal,[],[f249])).

fof(f249,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X0)
        | ~ r1_tarski(sK3(X1),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1)
        | ~ m1_connsp_2(sK3(X1),sK0,X0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X1,sK1) )
    | ~ spl6_17
    | ~ spl6_25
    | ~ spl6_26 ),
    inference(resolution,[],[f238,f222])).

fof(f222,plain,
    ( ! [X6,X5] :
        ( r2_hidden(X6,k1_tops_1(sK0,sK3(X5)))
        | ~ m1_connsp_2(sK3(X5),sK0,X6)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK1) )
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f221])).

fof(f238,plain,
    ( ! [X4,X3] :
        ( ~ r2_hidden(X4,k1_tops_1(sK0,sK3(X3)))
        | ~ m1_subset_1(X4,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X4)
        | ~ r1_tarski(sK3(X3),sK1)
        | ~ m1_subset_1(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl6_17
    | ~ spl6_26 ),
    inference(resolution,[],[f230,f148])).

fof(f148,plain,
    ( ! [X2] :
        ( m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,sK1) )
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f147])).

fof(f230,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X2)
        | ~ r2_hidden(X2,k1_tops_1(sK0,X3)) )
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f229])).

fof(f231,plain,
    ( ~ spl6_3
    | ~ spl6_4
    | spl6_26
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f199,f191,f229,f76,f71])).

fof(f191,plain,
    ( spl6_22
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | m1_connsp_2(sK1,sK0,X1)
        | ~ r2_hidden(X1,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f199,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X2,u1_struct_0(sK0))
        | ~ r2_hidden(X2,k1_tops_1(sK0,X3))
        | m1_connsp_2(sK1,sK0,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X3,sK1)
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_22 ),
    inference(resolution,[],[f194,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,X1)
        | m1_connsp_2(sK1,sK0,X0) )
    | ~ spl6_22 ),
    inference(resolution,[],[f192,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f192,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f191])).

fof(f223,plain,
    ( spl6_1
    | ~ spl6_3
    | ~ spl6_2
    | spl6_25
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f167,f147,f221,f66,f71,f61])).

fof(f61,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f167,plain,
    ( ! [X6,X5] :
        ( ~ m1_subset_1(X5,u1_struct_0(sK0))
        | ~ r2_hidden(X5,sK1)
        | ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X6,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X6,k1_tops_1(sK0,sK3(X5)))
        | ~ m1_connsp_2(sK3(X5),sK0,X6) )
    | ~ spl6_17 ),
    inference(resolution,[],[f148,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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

fof(f203,plain,
    ( spl6_1
    | spl6_23
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f91,f76,f66,f71,f201,f61])).

fof(f91,plain,
    ( ! [X2] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X2,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X2,k1_tops_1(sK0,sK1))
        | ~ m1_connsp_2(sK1,sK0,X2) )
    | ~ spl6_4 ),
    inference(resolution,[],[f78,f40])).

fof(f193,plain,
    ( spl6_1
    | spl6_22
    | ~ spl6_3
    | ~ spl6_2
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f90,f76,f66,f71,f191,f61])).

fof(f90,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | ~ r2_hidden(X1,k1_tops_1(sK0,sK1))
        | m1_connsp_2(sK1,sK0,X1) )
    | ~ spl6_4 ),
    inference(resolution,[],[f78,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f162,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | spl6_18 ),
    inference(avatar_contradiction_clause,[],[f161])).

fof(f161,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_12
    | spl6_18 ),
    inference(unit_resulting_resolution,[],[f68,f73,f63,f87,f82,f123,f78,f155,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ v3_pre_topc(X1,X0)
      | ~ r2_hidden(X2,X1)
      | m1_connsp_2(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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

fof(f155,plain,
    ( ~ m1_connsp_2(sK1,sK0,sK2)
    | spl6_18 ),
    inference(avatar_component_clause,[],[f153])).

fof(f123,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl6_12
  <=> m1_subset_1(sK2,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f82,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f87,plain,
    ( r2_hidden(sK2,sK1)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl6_6
  <=> r2_hidden(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f63,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f61])).

fof(f73,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f68,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f149,plain,
    ( spl6_5
    | spl6_17 ),
    inference(avatar_split_clause,[],[f27,f147,f81])).

fof(f27,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ! [X2] :
                ( ? [X3] :
                    ( r1_tarski(X3,X1)
                    & m1_connsp_2(X3,X0,X2)
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                | ~ r2_hidden(X2,X1)
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
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
            <=> ! [X2] :
                  ( m1_subset_1(X2,u1_struct_0(X0))
                 => ~ ( ! [X3] :
                          ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                         => ~ ( r1_tarski(X3,X1)
                              & m1_connsp_2(X3,X0,X2) ) )
                      & r2_hidden(X2,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ~ ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => ~ ( r1_tarski(X3,X1)
                            & m1_connsp_2(X3,X0,X2) ) )
                    & r2_hidden(X2,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).

fof(f145,plain,
    ( ~ spl6_5
    | spl6_16 ),
    inference(avatar_split_clause,[],[f30,f143,f81])).

fof(f30,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_connsp_2(X3,sK0,sK2)
      | ~ r1_tarski(X3,sK1)
      | ~ v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f140,plain,
    ( spl6_5
    | spl6_15 ),
    inference(avatar_split_clause,[],[f28,f138,f81])).

fof(f28,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | m1_connsp_2(sK3(X2),sK0,X2)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f133,plain,
    ( spl6_13
    | ~ spl6_14
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f106,f102,f130,f126])).

fof(f102,plain,
    ( spl6_8
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f106,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ spl6_8 ),
    inference(resolution,[],[f104,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f104,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f102])).

fof(f124,plain,
    ( ~ spl6_5
    | spl6_12 ),
    inference(avatar_split_clause,[],[f31,f121,f81])).

fof(f31,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f119,plain,
    ( spl6_5
    | spl6_11 ),
    inference(avatar_split_clause,[],[f29,f117,f81])).

fof(f29,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,u1_struct_0(sK0))
      | ~ r2_hidden(X2,sK1)
      | r1_tarski(sK3(X2),sK1)
      | v3_pre_topc(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f105,plain,
    ( spl6_8
    | ~ spl6_3
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f92,f76,f71,f102])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f78,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f88,plain,
    ( ~ spl6_5
    | spl6_6 ),
    inference(avatar_split_clause,[],[f32,f85,f81])).

fof(f32,plain,
    ( r2_hidden(sK2,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f33,f76])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f74,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f36,f71])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f69,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f35,f66])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:43:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.50  % (18311)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.50  % (18312)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.51  % (18328)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.51  % (18327)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.51  % (18320)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.51  % (18305)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.51  % (18319)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.51  % (18308)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.52  % (18309)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.52  % (18314)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.52  % (18315)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.52  % (18304)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.52  % (18324)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.52  % (18326)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.53  % (18318)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.53  % (18322)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.53  % (18306)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (18316)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.53  % (18332)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.53  % (18307)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.53  % (18333)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.53  % (18310)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (18329)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.54  % (18330)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.55  % (18321)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (18325)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.55  % (18331)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (18313)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.55  % (18317)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.55  % (18326)Refutation found. Thanks to Tanya!
% 0.20/0.55  % SZS status Theorem for theBenchmark
% 0.20/0.55  % SZS output start Proof for theBenchmark
% 0.20/0.55  fof(f396,plain,(
% 0.20/0.55    $false),
% 0.20/0.55    inference(avatar_sat_refutation,[],[f64,f69,f74,f79,f88,f105,f119,f124,f133,f140,f145,f149,f162,f193,f203,f223,f231,f328,f390,f395])).
% 0.20/0.55  fof(f395,plain,(
% 0.20/0.55    ~spl6_4 | ~spl6_16 | ~spl6_18),
% 0.20/0.55    inference(avatar_contradiction_clause,[],[f391])).
% 0.20/0.55  fof(f391,plain,(
% 0.20/0.55    $false | (~spl6_4 | ~spl6_16 | ~spl6_18)),
% 0.20/0.55    inference(unit_resulting_resolution,[],[f57,f154,f78,f144])).
% 0.20/0.55  fof(f144,plain,(
% 0.20/0.55    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2)) ) | ~spl6_16),
% 0.20/0.55    inference(avatar_component_clause,[],[f143])).
% 0.20/0.55  fof(f143,plain,(
% 0.20/0.55    spl6_16 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_connsp_2(X3,sK0,sK2))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.55  fof(f78,plain,(
% 0.20/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_4),
% 0.20/0.55    inference(avatar_component_clause,[],[f76])).
% 0.20/0.55  fof(f76,plain,(
% 0.20/0.55    spl6_4 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.55  fof(f154,plain,(
% 0.20/0.55    m1_connsp_2(sK1,sK0,sK2) | ~spl6_18),
% 0.20/0.55    inference(avatar_component_clause,[],[f153])).
% 0.20/0.55  fof(f153,plain,(
% 0.20/0.55    spl6_18 <=> m1_connsp_2(sK1,sK0,sK2)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.55  fof(f57,plain,(
% 0.20/0.55    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.55    inference(equality_resolution,[],[f43])).
% 0.20/0.55  fof(f43,plain,(
% 0.20/0.55    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 0.20/0.55    inference(cnf_transformation,[],[f2])).
% 0.20/0.55  fof(f2,axiom,(
% 0.20/0.55    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.55  fof(f390,plain,(
% 0.20/0.55    ~spl6_2 | ~spl6_4 | ~spl6_3 | spl6_5 | ~spl6_13),
% 0.20/0.55    inference(avatar_split_clause,[],[f353,f126,f81,f71,f76,f66])).
% 0.20/0.55  fof(f66,plain,(
% 0.20/0.55    spl6_2 <=> v2_pre_topc(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.55  fof(f71,plain,(
% 0.20/0.55    spl6_3 <=> l1_pre_topc(sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.55  fof(f81,plain,(
% 0.20/0.55    spl6_5 <=> v3_pre_topc(sK1,sK0)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.55  fof(f126,plain,(
% 0.20/0.55    spl6_13 <=> sK1 = k1_tops_1(sK0,sK1)),
% 0.20/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.55  fof(f353,plain,(
% 0.20/0.55    v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~spl6_13),
% 0.20/0.55    inference(superposition,[],[f42,f128])).
% 0.20/0.55  fof(f128,plain,(
% 0.20/0.55    sK1 = k1_tops_1(sK0,sK1) | ~spl6_13),
% 0.20/0.55    inference(avatar_component_clause,[],[f126])).
% 0.20/0.55  fof(f42,plain,(
% 0.20/0.55    ( ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0)) )),
% 0.20/0.55    inference(cnf_transformation,[],[f23])).
% 0.20/0.55  fof(f23,plain,(
% 0.20/0.55    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.55    inference(flattening,[],[f22])).
% 0.20/0.55  fof(f22,plain,(
% 0.20/0.55    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.55    inference(ennf_transformation,[],[f6])).
% 0.20/0.55  fof(f6,axiom,(
% 0.20/0.55    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.20/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.20/0.55  fof(f328,plain,(
% 0.20/0.55    spl6_14 | ~spl6_4 | ~spl6_11 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_25 | ~spl6_26),
% 0.20/0.55    inference(avatar_split_clause,[],[f325,f229,f221,f201,f147,f138,f117,f76,f130])).
% 0.20/0.55  % (18323)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.56  fof(f130,plain,(
% 0.20/0.56    spl6_14 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.56  fof(f117,plain,(
% 0.20/0.56    spl6_11 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.56  fof(f138,plain,(
% 0.20/0.56    spl6_15 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK3(X2),sK0,X2) | ~r2_hidden(X2,sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.56  fof(f147,plain,(
% 0.20/0.56    spl6_17 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X2,sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.56  fof(f201,plain,(
% 0.20/0.56    spl6_23 <=> ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~m1_connsp_2(sK1,sK0,X2) | r2_hidden(X2,k1_tops_1(sK0,sK1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.56  fof(f221,plain,(
% 0.20/0.56    spl6_25 <=> ! [X5,X6] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~m1_connsp_2(sK3(X5),sK0,X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | r2_hidden(X6,k1_tops_1(sK0,sK3(X5))) | ~r2_hidden(X5,sK1))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.56  fof(f229,plain,(
% 0.20/0.56    spl6_26 <=> ! [X3,X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | m1_connsp_2(sK1,sK0,X2) | ~r2_hidden(X2,k1_tops_1(sK0,X3)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.56  fof(f325,plain,(
% 0.20/0.56    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl6_4 | ~spl6_11 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f323])).
% 0.20/0.56  fof(f323,plain,(
% 0.20/0.56    r1_tarski(sK1,k1_tops_1(sK0,sK1)) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl6_4 | ~spl6_11 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(resolution,[],[f322,f47])).
% 0.20/0.56  fof(f47,plain,(
% 0.20/0.56    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f24,plain,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f1])).
% 0.20/0.56  fof(f1,axiom,(
% 0.20/0.56    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.56  fof(f322,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X0,k1_tops_1(sK0,sK1))) ) | (~spl6_4 | ~spl6_11 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f321])).
% 0.20/0.56  fof(f321,plain,(
% 0.20/0.56    ( ! [X0] : (~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1)) ) | (~spl6_4 | ~spl6_11 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(resolution,[],[f320,f135])).
% 0.20/0.56  fof(f135,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(sK3(X0),sK1) | ~r2_hidden(X0,sK1)) ) | (~spl6_4 | ~spl6_11)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f134])).
% 0.20/0.56  fof(f134,plain,(
% 0.20/0.56    ( ! [X0] : (r1_tarski(sK3(X0),sK1) | ~r2_hidden(X0,sK1) | ~r2_hidden(X0,sK1)) ) | (~spl6_4 | ~spl6_11)),
% 0.20/0.56    inference(resolution,[],[f118,f93])).
% 0.20/0.56  fof(f93,plain,(
% 0.20/0.56    ( ! [X3] : (m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1)) ) | ~spl6_4),
% 0.20/0.56    inference(resolution,[],[f78,f55])).
% 0.20/0.56  fof(f55,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f26])).
% 0.20/0.56  fof(f26,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.56    inference(flattening,[],[f25])).
% 0.20/0.56  fof(f25,plain,(
% 0.20/0.56    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.56    inference(ennf_transformation,[],[f5])).
% 0.20/0.56  fof(f5,axiom,(
% 0.20/0.56    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.56  fof(f118,plain,(
% 0.20/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | r1_tarski(sK3(X2),sK1) | ~r2_hidden(X2,sK1)) ) | ~spl6_11),
% 0.20/0.56    inference(avatar_component_clause,[],[f117])).
% 0.20/0.56  fof(f320,plain,(
% 0.20/0.56    ( ! [X2] : (~r1_tarski(sK3(sK4(X2,k1_tops_1(sK0,sK1))),sK1) | ~r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X2,k1_tops_1(sK0,sK1))) ) | (~spl6_4 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f319])).
% 0.20/0.56  fof(f319,plain,(
% 0.20/0.56    ( ! [X2] : (~r1_tarski(sK3(sK4(X2,k1_tops_1(sK0,sK1))),sK1) | ~r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X2,k1_tops_1(sK0,sK1)) | ~r2_hidden(sK4(X2,k1_tops_1(sK0,sK1)),sK1)) ) | (~spl6_4 | ~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(resolution,[],[f260,f93])).
% 0.20/0.56  fof(f260,plain,(
% 0.20/0.56    ( ! [X0] : (~m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~r1_tarski(sK3(sK4(X0,k1_tops_1(sK0,sK1))),sK1) | ~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) | r1_tarski(X0,k1_tops_1(sK0,sK1))) ) | (~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f259])).
% 0.20/0.56  fof(f259,plain,(
% 0.20/0.56    ( ! [X0] : (~r1_tarski(sK3(sK4(X0,k1_tops_1(sK0,sK1))),sK1) | ~m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | ~r2_hidden(sK4(X0,k1_tops_1(sK0,sK1)),sK1) | ~m1_subset_1(sK4(X0,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r1_tarski(X0,k1_tops_1(sK0,sK1))) ) | (~spl6_15 | ~spl6_17 | ~spl6_23 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(resolution,[],[f257,f205])).
% 0.20/0.56  fof(f205,plain,(
% 0.20/0.56    ( ! [X1] : (~m1_connsp_2(sK1,sK0,sK4(X1,k1_tops_1(sK0,sK1))) | ~m1_subset_1(sK4(X1,k1_tops_1(sK0,sK1)),u1_struct_0(sK0)) | r1_tarski(X1,k1_tops_1(sK0,sK1))) ) | ~spl6_23),
% 0.20/0.56    inference(resolution,[],[f202,f48])).
% 0.20/0.56  fof(f48,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f202,plain,(
% 0.20/0.56    ( ! [X2] : (r2_hidden(X2,k1_tops_1(sK0,sK1)) | ~m1_connsp_2(sK1,sK0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0))) ) | ~spl6_23),
% 0.20/0.56    inference(avatar_component_clause,[],[f201])).
% 0.20/0.56  fof(f257,plain,(
% 0.20/0.56    ( ! [X0] : (m1_connsp_2(sK1,sK0,X0) | ~r1_tarski(sK3(X0),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | (~spl6_15 | ~spl6_17 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f254])).
% 0.20/0.56  fof(f254,plain,(
% 0.20/0.56    ( ! [X0] : (m1_connsp_2(sK1,sK0,X0) | ~r1_tarski(sK3(X0),sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) ) | (~spl6_15 | ~spl6_17 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(resolution,[],[f253,f139])).
% 0.20/0.56  fof(f139,plain,(
% 0.20/0.56    ( ! [X2] : (m1_connsp_2(sK3(X2),sK0,X2) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1)) ) | ~spl6_15),
% 0.20/0.56    inference(avatar_component_clause,[],[f138])).
% 0.20/0.56  fof(f253,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_connsp_2(sK3(X1),sK0,X0) | m1_connsp_2(sK1,sK0,X0) | ~r1_tarski(sK3(X1),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | (~spl6_17 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(duplicate_literal_removal,[],[f249])).
% 0.20/0.56  fof(f249,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X0,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X0) | ~r1_tarski(sK3(X1),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK1) | ~m1_connsp_2(sK3(X1),sK0,X0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X1,sK1)) ) | (~spl6_17 | ~spl6_25 | ~spl6_26)),
% 0.20/0.56    inference(resolution,[],[f238,f222])).
% 0.20/0.56  fof(f222,plain,(
% 0.20/0.56    ( ! [X6,X5] : (r2_hidden(X6,k1_tops_1(sK0,sK3(X5))) | ~m1_connsp_2(sK3(X5),sK0,X6) | ~m1_subset_1(X6,u1_struct_0(sK0)) | ~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X5,sK1)) ) | ~spl6_25),
% 0.20/0.56    inference(avatar_component_clause,[],[f221])).
% 0.20/0.56  fof(f238,plain,(
% 0.20/0.56    ( ! [X4,X3] : (~r2_hidden(X4,k1_tops_1(sK0,sK3(X3))) | ~m1_subset_1(X4,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X4) | ~r1_tarski(sK3(X3),sK1) | ~m1_subset_1(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1)) ) | (~spl6_17 | ~spl6_26)),
% 0.20/0.56    inference(resolution,[],[f230,f148])).
% 0.20/0.56  fof(f148,plain,(
% 0.20/0.56    ( ! [X2] : (m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1)) ) | ~spl6_17),
% 0.20/0.56    inference(avatar_component_clause,[],[f147])).
% 0.20/0.56  fof(f230,plain,(
% 0.20/0.56    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~m1_subset_1(X2,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X2) | ~r2_hidden(X2,k1_tops_1(sK0,X3))) ) | ~spl6_26),
% 0.20/0.56    inference(avatar_component_clause,[],[f229])).
% 0.20/0.56  fof(f231,plain,(
% 0.20/0.56    ~spl6_3 | ~spl6_4 | spl6_26 | ~spl6_22),
% 0.20/0.56    inference(avatar_split_clause,[],[f199,f191,f229,f76,f71])).
% 0.20/0.56  fof(f191,plain,(
% 0.20/0.56    spl6_22 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | m1_connsp_2(sK1,sK0,X1) | ~r2_hidden(X1,k1_tops_1(sK0,sK1)))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.56  fof(f199,plain,(
% 0.20/0.56    ( ! [X2,X3] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,k1_tops_1(sK0,X3)) | m1_connsp_2(sK1,sK0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X3,sK1) | ~l1_pre_topc(sK0)) ) | ~spl6_22),
% 0.20/0.56    inference(resolution,[],[f194,f38])).
% 0.20/0.56  fof(f38,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f17])).
% 0.20/0.56  fof(f17,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(flattening,[],[f16])).
% 0.20/0.56  fof(f16,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f8])).
% 0.20/0.56  fof(f8,axiom,(
% 0.20/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.20/0.56  fof(f194,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X1,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,X1) | m1_connsp_2(sK1,sK0,X0)) ) | ~spl6_22),
% 0.20/0.56    inference(resolution,[],[f192,f46])).
% 0.20/0.56  fof(f46,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0) | ~r1_tarski(X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f24])).
% 0.20/0.56  fof(f192,plain,(
% 0.20/0.56    ( ! [X1] : (~r2_hidden(X1,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_22),
% 0.20/0.56    inference(avatar_component_clause,[],[f191])).
% 0.20/0.56  fof(f223,plain,(
% 0.20/0.56    spl6_1 | ~spl6_3 | ~spl6_2 | spl6_25 | ~spl6_17),
% 0.20/0.56    inference(avatar_split_clause,[],[f167,f147,f221,f66,f71,f61])).
% 0.20/0.56  fof(f61,plain,(
% 0.20/0.56    spl6_1 <=> v2_struct_0(sK0)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.56  fof(f167,plain,(
% 0.20/0.56    ( ! [X6,X5] : (~m1_subset_1(X5,u1_struct_0(sK0)) | ~r2_hidden(X5,sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X6,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X6,k1_tops_1(sK0,sK3(X5))) | ~m1_connsp_2(sK3(X5),sK0,X6)) ) | ~spl6_17),
% 0.20/0.56    inference(resolution,[],[f148,f40])).
% 0.20/0.56  fof(f40,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | r2_hidden(X1,k1_tops_1(X0,X2)) | ~m1_connsp_2(X2,X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f19,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f18])).
% 0.20/0.56  fof(f18,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f9])).
% 0.20/0.56  fof(f9,axiom,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m1_connsp_2(X2,X0,X1) <=> r2_hidden(X1,k1_tops_1(X0,X2))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).
% 0.20/0.56  fof(f203,plain,(
% 0.20/0.56    spl6_1 | spl6_23 | ~spl6_3 | ~spl6_2 | ~spl6_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f91,f76,f66,f71,f201,f61])).
% 0.20/0.56  fof(f91,plain,(
% 0.20/0.56    ( ! [X2] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,u1_struct_0(sK0)) | v2_struct_0(sK0) | r2_hidden(X2,k1_tops_1(sK0,sK1)) | ~m1_connsp_2(sK1,sK0,X2)) ) | ~spl6_4),
% 0.20/0.56    inference(resolution,[],[f78,f40])).
% 0.20/0.56  fof(f193,plain,(
% 0.20/0.56    spl6_1 | spl6_22 | ~spl6_3 | ~spl6_2 | ~spl6_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f90,f76,f66,f71,f191,f61])).
% 0.20/0.56  fof(f90,plain,(
% 0.20/0.56    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0) | ~r2_hidden(X1,k1_tops_1(sK0,sK1)) | m1_connsp_2(sK1,sK0,X1)) ) | ~spl6_4),
% 0.20/0.56    inference(resolution,[],[f78,f39])).
% 0.20/0.56  fof(f39,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2)) | m1_connsp_2(X2,X0,X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f19])).
% 0.20/0.56  fof(f162,plain,(
% 0.20/0.56    spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | spl6_18),
% 0.20/0.56    inference(avatar_contradiction_clause,[],[f161])).
% 0.20/0.56  fof(f161,plain,(
% 0.20/0.56    $false | (spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_5 | ~spl6_6 | ~spl6_12 | spl6_18)),
% 0.20/0.56    inference(unit_resulting_resolution,[],[f68,f73,f63,f87,f82,f123,f78,f155,f41])).
% 0.20/0.56  fof(f41,plain,(
% 0.20/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~v3_pre_topc(X1,X0) | ~r2_hidden(X2,X1) | m1_connsp_2(X1,X0,X2)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f21])).
% 0.20/0.56  fof(f21,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_connsp_2(X1,X0,X2) | ~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f20])).
% 0.20/0.56  fof(f20,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (! [X2] : ((m1_connsp_2(X1,X0,X2) | (~r2_hidden(X2,X1) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f10])).
% 0.20/0.56  fof(f10,axiom,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ((r2_hidden(X2,X1) & v3_pre_topc(X1,X0)) => m1_connsp_2(X1,X0,X2)))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).
% 0.20/0.56  fof(f155,plain,(
% 0.20/0.56    ~m1_connsp_2(sK1,sK0,sK2) | spl6_18),
% 0.20/0.56    inference(avatar_component_clause,[],[f153])).
% 0.20/0.56  fof(f123,plain,(
% 0.20/0.56    m1_subset_1(sK2,u1_struct_0(sK0)) | ~spl6_12),
% 0.20/0.56    inference(avatar_component_clause,[],[f121])).
% 0.20/0.56  fof(f121,plain,(
% 0.20/0.56    spl6_12 <=> m1_subset_1(sK2,u1_struct_0(sK0))),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.56  fof(f82,plain,(
% 0.20/0.56    v3_pre_topc(sK1,sK0) | ~spl6_5),
% 0.20/0.56    inference(avatar_component_clause,[],[f81])).
% 0.20/0.56  fof(f87,plain,(
% 0.20/0.56    r2_hidden(sK2,sK1) | ~spl6_6),
% 0.20/0.56    inference(avatar_component_clause,[],[f85])).
% 0.20/0.56  fof(f85,plain,(
% 0.20/0.56    spl6_6 <=> r2_hidden(sK2,sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.56  fof(f63,plain,(
% 0.20/0.56    ~v2_struct_0(sK0) | spl6_1),
% 0.20/0.56    inference(avatar_component_clause,[],[f61])).
% 0.20/0.56  fof(f73,plain,(
% 0.20/0.56    l1_pre_topc(sK0) | ~spl6_3),
% 0.20/0.56    inference(avatar_component_clause,[],[f71])).
% 0.20/0.56  fof(f68,plain,(
% 0.20/0.56    v2_pre_topc(sK0) | ~spl6_2),
% 0.20/0.56    inference(avatar_component_clause,[],[f66])).
% 0.20/0.56  fof(f149,plain,(
% 0.20/0.56    spl6_5 | spl6_17),
% 0.20/0.56    inference(avatar_split_clause,[],[f27,f147,f81])).
% 0.20/0.56  fof(f27,plain,(
% 0.20/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_subset_1(sK3(X2),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f14,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : (? [X3] : (r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.56    inference(flattening,[],[f13])).
% 0.20/0.56  fof(f13,plain,(
% 0.20/0.56    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> ! [X2] : ((? [X3] : ((r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X2,u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.56    inference(ennf_transformation,[],[f12])).
% 0.20/0.56  fof(f12,negated_conjecture,(
% 0.20/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.56    inference(negated_conjecture,[],[f11])).
% 0.20/0.56  fof(f11,conjecture,(
% 0.20/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ~(! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ~(r1_tarski(X3,X1) & m1_connsp_2(X3,X0,X2))) & r2_hidden(X2,X1))))))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_connsp_2)).
% 0.20/0.56  fof(f145,plain,(
% 0.20/0.56    ~spl6_5 | spl6_16),
% 0.20/0.56    inference(avatar_split_clause,[],[f30,f143,f81])).
% 0.20/0.56  fof(f30,plain,(
% 0.20/0.56    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_connsp_2(X3,sK0,sK2) | ~r1_tarski(X3,sK1) | ~v3_pre_topc(sK1,sK0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f140,plain,(
% 0.20/0.56    spl6_5 | spl6_15),
% 0.20/0.56    inference(avatar_split_clause,[],[f28,f138,f81])).
% 0.20/0.56  fof(f28,plain,(
% 0.20/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | m1_connsp_2(sK3(X2),sK0,X2) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f133,plain,(
% 0.20/0.56    spl6_13 | ~spl6_14 | ~spl6_8),
% 0.20/0.56    inference(avatar_split_clause,[],[f106,f102,f130,f126])).
% 0.20/0.56  fof(f102,plain,(
% 0.20/0.56    spl6_8 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.20/0.56    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.56  fof(f106,plain,(
% 0.20/0.56    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | sK1 = k1_tops_1(sK0,sK1) | ~spl6_8),
% 0.20/0.56    inference(resolution,[],[f104,f45])).
% 0.20/0.56  fof(f45,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.56    inference(cnf_transformation,[],[f2])).
% 0.20/0.56  fof(f104,plain,(
% 0.20/0.56    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl6_8),
% 0.20/0.56    inference(avatar_component_clause,[],[f102])).
% 0.20/0.56  fof(f124,plain,(
% 0.20/0.56    ~spl6_5 | spl6_12),
% 0.20/0.56    inference(avatar_split_clause,[],[f31,f121,f81])).
% 0.20/0.56  fof(f31,plain,(
% 0.20/0.56    m1_subset_1(sK2,u1_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f119,plain,(
% 0.20/0.56    spl6_5 | spl6_11),
% 0.20/0.56    inference(avatar_split_clause,[],[f29,f117,f81])).
% 0.20/0.56  fof(f29,plain,(
% 0.20/0.56    ( ! [X2] : (~m1_subset_1(X2,u1_struct_0(sK0)) | ~r2_hidden(X2,sK1) | r1_tarski(sK3(X2),sK1) | v3_pre_topc(sK1,sK0)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f105,plain,(
% 0.20/0.56    spl6_8 | ~spl6_3 | ~spl6_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f92,f76,f71,f102])).
% 0.20/0.56  fof(f92,plain,(
% 0.20/0.56    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl6_4),
% 0.20/0.56    inference(resolution,[],[f78,f37])).
% 0.20/0.56  fof(f37,plain,(
% 0.20/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.20/0.56    inference(cnf_transformation,[],[f15])).
% 0.20/0.56  fof(f15,plain,(
% 0.20/0.56    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.56    inference(ennf_transformation,[],[f7])).
% 0.20/0.56  fof(f7,axiom,(
% 0.20/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.20/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.20/0.56  fof(f88,plain,(
% 0.20/0.56    ~spl6_5 | spl6_6),
% 0.20/0.56    inference(avatar_split_clause,[],[f32,f85,f81])).
% 0.20/0.56  fof(f32,plain,(
% 0.20/0.56    r2_hidden(sK2,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f79,plain,(
% 0.20/0.56    spl6_4),
% 0.20/0.56    inference(avatar_split_clause,[],[f33,f76])).
% 0.20/0.56  fof(f33,plain,(
% 0.20/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f74,plain,(
% 0.20/0.56    spl6_3),
% 0.20/0.56    inference(avatar_split_clause,[],[f36,f71])).
% 0.20/0.56  fof(f36,plain,(
% 0.20/0.56    l1_pre_topc(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f69,plain,(
% 0.20/0.56    spl6_2),
% 0.20/0.56    inference(avatar_split_clause,[],[f35,f66])).
% 0.20/0.56  fof(f35,plain,(
% 0.20/0.56    v2_pre_topc(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  fof(f64,plain,(
% 0.20/0.56    ~spl6_1),
% 0.20/0.56    inference(avatar_split_clause,[],[f34,f61])).
% 0.20/0.56  fof(f34,plain,(
% 0.20/0.56    ~v2_struct_0(sK0)),
% 0.20/0.56    inference(cnf_transformation,[],[f14])).
% 0.20/0.56  % SZS output end Proof for theBenchmark
% 0.20/0.56  % (18326)------------------------------
% 0.20/0.56  % (18326)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18326)Termination reason: Refutation
% 0.20/0.56  
% 0.20/0.56  % (18326)Memory used [KB]: 11001
% 0.20/0.56  % (18326)Time elapsed: 0.095 s
% 0.20/0.56  % (18326)------------------------------
% 0.20/0.56  % (18326)------------------------------
% 0.20/0.56  % (18330)Refutation not found, incomplete strategy% (18330)------------------------------
% 0.20/0.56  % (18330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.56  % (18330)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.56  
% 0.20/0.56  % (18330)Memory used [KB]: 10746
% 0.20/0.56  % (18330)Time elapsed: 0.160 s
% 0.20/0.56  % (18330)------------------------------
% 0.20/0.56  % (18330)------------------------------
% 0.20/0.57  % (18303)Success in time 0.213 s
%------------------------------------------------------------------------------
