%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1718+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:24 EST 2020

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 319 expanded)
%              Number of leaves         :   30 ( 163 expanded)
%              Depth                    :   11
%              Number of atoms          :  725 (3185 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :   27 (   8 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f165,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f51,f55,f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f113,f128,f134,f152,f160,f162,f164])).

fof(f164,plain,
    ( spl5_14
    | ~ spl5_12
    | spl5_9
    | ~ spl5_8
    | spl5_5
    | ~ spl5_4
    | spl5_20 ),
    inference(avatar_split_clause,[],[f163,f158,f61,f65,f77,f81,f93,f101])).

fof(f101,plain,
    ( spl5_14
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f93,plain,
    ( spl5_12
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f81,plain,
    ( spl5_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f77,plain,
    ( spl5_8
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f65,plain,
    ( spl5_5
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

% (8586)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f61,plain,
    ( spl5_4
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f158,plain,
    ( spl5_20
  <=> m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f163,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_20 ),
    inference(resolution,[],[f159,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f159,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)
    | spl5_20 ),
    inference(avatar_component_clause,[],[f158])).

fof(f162,plain,
    ( spl5_14
    | ~ spl5_12
    | spl5_11
    | ~ spl5_10
    | spl5_7
    | ~ spl5_6
    | spl5_19 ),
    inference(avatar_split_clause,[],[f161,f155,f69,f73,f85,f89,f93,f101])).

fof(f89,plain,
    ( spl5_11
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f85,plain,
    ( spl5_10
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f73,plain,
    ( spl5_7
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f69,plain,
    ( spl5_6
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f155,plain,
    ( spl5_19
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f161,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_19 ),
    inference(resolution,[],[f156,f45])).

fof(f156,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | spl5_19 ),
    inference(avatar_component_clause,[],[f155])).

fof(f160,plain,
    ( ~ spl5_19
    | ~ spl5_12
    | ~ spl5_20
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f153,f140,f97,f158,f93,f155])).

fof(f97,plain,
    ( spl5_13
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f140,plain,
    ( spl5_18
  <=> ! [X0] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f153,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),sK0)
    | ~ spl5_13
    | ~ spl5_18 ),
    inference(resolution,[],[f141,f98])).

fof(f98,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f97])).

fof(f141,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f140])).

fof(f152,plain,
    ( spl5_18
    | spl5_9
    | ~ spl5_4
    | ~ spl5_6
    | ~ spl5_2
    | spl5_7
    | spl5_5
    | ~ spl5_8
    | ~ spl5_10
    | ~ spl5_3
    | spl5_11
    | spl5_1
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f138,f132,f49,f89,f57,f85,f77,f65,f73,f53,f69,f61,f81,f140])).

fof(f53,plain,
    ( spl5_2
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f57,plain,
    ( spl5_3
  <=> m1_pre_topc(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f49,plain,
    ( spl5_1
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f132,plain,
    ( spl5_17
  <=> ! [X1,X3,X0,X2] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(k1_tsep_1(sK0,X2,X3)))
        | v2_struct_0(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X3,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f138,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK2)
        | ~ m1_pre_topc(sK1,sK0)
        | ~ m1_pre_topc(sK2,sK0)
        | v2_struct_0(sK4)
        | v2_struct_0(sK3)
        | ~ m1_pre_topc(sK3,sK4)
        | ~ m1_pre_topc(sK3,sK0)
        | ~ m1_pre_topc(sK4,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK2,sK4),X0)
        | ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl5_1
    | ~ spl5_17 ),
    inference(resolution,[],[f137,f50])).

fof(f50,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4))
    | spl5_1 ),
    inference(avatar_component_clause,[],[f49])).

fof(f137,plain,
    ( ! [X14,X17,X15,X13,X16] :
        ( m1_pre_topc(k1_tsep_1(sK0,X14,X16),k1_tsep_1(sK0,X13,X15))
        | v2_struct_0(X14)
        | ~ m1_pre_topc(X14,X13)
        | ~ m1_pre_topc(X14,sK0)
        | ~ m1_pre_topc(X13,sK0)
        | v2_struct_0(X15)
        | v2_struct_0(X16)
        | ~ m1_pre_topc(X16,X15)
        | ~ m1_pre_topc(X16,sK0)
        | ~ m1_pre_topc(X15,sK0)
        | v2_struct_0(X13)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X13,X15),X17)
        | ~ m1_pre_topc(k1_tsep_1(sK0,X14,X16),X17)
        | ~ l1_pre_topc(X17)
        | ~ v2_pre_topc(X17) )
    | ~ spl5_17 ),
    inference(resolution,[],[f133,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f133,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(k1_tsep_1(sK0,X2,X3)))
        | v2_struct_0(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X3)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X3,sK0) )
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f134,plain,
    ( ~ spl5_12
    | spl5_17
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f130,f126,f97,f132,f93])).

fof(f126,plain,
    ( spl5_16
  <=> ! [X1,X3,X0,X2,X4] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X3,X2)),u1_struct_0(k1_tsep_1(sK0,X1,X0)))
        | ~ v2_pre_topc(X4)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(X2,X4)
        | ~ m1_pre_topc(X0,X4)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,X1)
        | v2_struct_0(X3)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f130,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(k1_tsep_1(sK0,X2,X3)))
        | ~ m1_pre_topc(X3,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,X3)
        | v2_struct_0(X1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | v2_struct_0(X2) )
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(duplicate_literal_removal,[],[f129])).

fof(f129,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(k1_tsep_1(sK0,X2,X3)))
        | ~ m1_pre_topc(X3,sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X1,X3)
        | v2_struct_0(X1)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X0,X2)
        | v2_struct_0(X0)
        | v2_struct_0(X2) )
    | ~ spl5_13
    | ~ spl5_16 ),
    inference(resolution,[],[f127,f98])).

fof(f127,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ v2_pre_topc(X4)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X3,X2)),u1_struct_0(k1_tsep_1(sK0,X1,X0)))
        | ~ m1_pre_topc(X0,sK0)
        | ~ l1_pre_topc(X4)
        | ~ m1_pre_topc(X2,X4)
        | ~ m1_pre_topc(X0,X4)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X2,X0)
        | v2_struct_0(X2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X3,X1)
        | v2_struct_0(X3)
        | v2_struct_0(X1) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f126])).

fof(f128,plain,
    ( ~ spl5_12
    | spl5_16
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f123,f111,f97,f126,f93])).

fof(f111,plain,
    ( spl5_15
  <=> ! [X1,X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f123,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X0,X4)
        | ~ m1_pre_topc(X2,X4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ m1_pre_topc(X3,X1)
        | ~ l1_pre_topc(sK0)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X3,X2)),u1_struct_0(k1_tsep_1(sK0,X1,X0))) )
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(duplicate_literal_removal,[],[f122])).

fof(f122,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X2,sK0)
        | ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X0,X4)
        | ~ m1_pre_topc(X2,X4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ m1_pre_topc(X3,X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X3,sK0)
        | ~ l1_pre_topc(sK0)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X3,X2)),u1_struct_0(k1_tsep_1(sK0,X1,X0))) )
    | ~ spl5_13
    | ~ spl5_15 ),
    inference(resolution,[],[f121,f98])).

fof(f121,plain,
    ( ! [X4,X2,X0,X5,X3,X1] :
        ( ~ v2_pre_topc(X5)
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X3)
        | ~ m1_pre_topc(X3,X4)
        | ~ m1_pre_topc(X1,X4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4)
        | ~ m1_pre_topc(X0,X2)
        | ~ m1_pre_topc(X2,X5)
        | ~ m1_pre_topc(X0,X5)
        | ~ l1_pre_topc(X5)
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(k1_tsep_1(sK0,X2,X3))) )
    | ~ spl5_15 ),
    inference(resolution,[],[f120,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f120,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(k1_tsep_1(sK0,X2,X3)))
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,X3)
        | ~ m1_pre_topc(X3,X4)
        | ~ m1_pre_topc(X1,X4)
        | ~ l1_pre_topc(X4)
        | ~ v2_pre_topc(X4) )
    | ~ spl5_15 ),
    inference(resolution,[],[f116,f42])).

fof(f116,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X3))
        | r1_tarski(u1_struct_0(k1_tsep_1(sK0,X0,X1)),u1_struct_0(k1_tsep_1(sK0,X2,X3)))
        | ~ r1_tarski(u1_struct_0(X0),u1_struct_0(X2))
        | ~ m1_pre_topc(X3,sK0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1) )
    | ~ spl5_15 ),
    inference(superposition,[],[f114,f112])).

fof(f112,plain,
    ( ! [X0,X1] :
        ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_struct_0(X0) )
    | ~ spl5_15 ),
    inference(avatar_component_clause,[],[f111])).

fof(f114,plain,
    ( ! [X2,X0,X3,X1] :
        ( r1_tarski(k2_xboole_0(X2,X3),u1_struct_0(k1_tsep_1(sK0,X0,X1)))
        | ~ r1_tarski(X3,u1_struct_0(X1))
        | ~ r1_tarski(X2,u1_struct_0(X0))
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(X1) )
    | ~ spl5_15 ),
    inference(superposition,[],[f46,f112])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k2_xboole_0(X0,X2),k2_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

fof(f113,plain,
    ( spl5_14
    | spl5_15
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f108,f93,f111,f101])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) = u1_struct_0(k1_tsep_1(sK0,X1,X0))
        | v2_struct_0(sK0) )
    | ~ spl5_12 ),
    inference(resolution,[],[f106,f94])).

fof(f94,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f93])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f105,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f104,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f47,f45])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f10])).

fof(f10,plain,(
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
    inference(flattening,[],[f9])).

fof(f9,plain,(
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

fof(f103,plain,(
    ~ spl5_14 ),
    inference(avatar_split_clause,[],[f25,f101])).

fof(f25,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4))
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK1,sK2)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f8,f21,f20,f19,f18,f17])).

fof(f17,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                        & m1_pre_topc(X3,X4)
                        & m1_pre_topc(X1,X2)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),k1_tsep_1(sK0,X2,X4))
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_pre_topc(k1_tsep_1(sK0,X1,X3),k1_tsep_1(sK0,X2,X4))
                    & m1_pre_topc(X3,X4)
                    & m1_pre_topc(X1,X2)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,X2,X4))
                  & m1_pre_topc(X3,X4)
                  & m1_pre_topc(sK1,X2)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,X2,X4))
                & m1_pre_topc(X3,X4)
                & m1_pre_topc(sK1,X2)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,sK2,X4))
              & m1_pre_topc(X3,X4)
              & m1_pre_topc(sK1,sK2)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,X3),k1_tsep_1(sK0,sK2,X4))
            & m1_pre_topc(X3,X4)
            & m1_pre_topc(sK1,sK2)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,X4))
          & m1_pre_topc(sK3,X4)
          & m1_pre_topc(sK1,sK2)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X4] :
        ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,X4))
        & m1_pre_topc(sK3,X4)
        & m1_pre_topc(sK1,sK2)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4))
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK1,sK2)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f7])).

fof(f7,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4))
                      & m1_pre_topc(X3,X4)
                      & m1_pre_topc(X1,X2)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,negated_conjecture,(
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
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X3,X4)
                            & m1_pre_topc(X1,X2) )
                         => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f5,conjecture,(
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
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X3,X4)
                          & m1_pre_topc(X1,X2) )
                       => m1_pre_topc(k1_tsep_1(X0,X1,X3),k1_tsep_1(X0,X2,X4)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tmap_1)).

fof(f99,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f26,f97])).

fof(f26,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f95,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f27,f93])).

fof(f27,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f91,plain,(
    ~ spl5_11 ),
    inference(avatar_split_clause,[],[f28,f89])).

fof(f28,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f87,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f29,f85])).

fof(f29,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f83,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f30,f81])).

fof(f30,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f31,f77])).

fof(f31,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f75,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f32,f73])).

fof(f32,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f22])).

fof(f71,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f33,f69])).

fof(f33,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f67,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f35,f61])).

fof(f35,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f59,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f36,f57])).

fof(f36,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f37,f53])).

fof(f37,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f22])).

fof(f51,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f38,f49])).

fof(f38,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK0,sK1,sK3),k1_tsep_1(sK0,sK2,sK4)) ),
    inference(cnf_transformation,[],[f22])).

%------------------------------------------------------------------------------
