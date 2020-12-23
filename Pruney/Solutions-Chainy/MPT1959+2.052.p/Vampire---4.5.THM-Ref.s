%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:58 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.45s
% Verified   : 
% Statistics : Number of formulae       :  107 ( 180 expanded)
%              Number of leaves         :   30 (  73 expanded)
%              Depth                    :    7
%              Number of atoms          :  354 ( 834 expanded)
%              Number of equality atoms :   18 (  26 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f287,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f63,f68,f83,f88,f93,f103,f108,f124,f125,f132,f152,f195,f206,f214,f233,f255,f256,f257,f263,f281,f286])).

fof(f286,plain,
    ( ~ spl6_10
    | spl6_13
    | ~ spl6_31 ),
    inference(avatar_contradiction_clause,[],[f283])).

fof(f283,plain,
    ( $false
    | ~ spl6_10
    | spl6_13
    | ~ spl6_31 ),
    inference(unit_resulting_resolution,[],[f130,f280,f280,f127])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK5(X0,u1_struct_0(sK0)),sK1)
        | ~ r2_hidden(sK5(X0,u1_struct_0(sK0)),X0)
        | u1_struct_0(sK0) = X0 )
    | ~ spl6_10 ),
    inference(resolution,[],[f113,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK5(X0,X1),X1)
      | ~ r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ? [X2] :
          ( r2_hidden(X2,X0)
        <~> r2_hidden(X2,X1) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
        <=> r2_hidden(X2,X1) )
     => X0 = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).

fof(f113,plain,
    ( ! [X3] :
        ( r2_hidden(X3,u1_struct_0(sK0))
        | ~ r2_hidden(X3,sK1) )
    | ~ spl6_10 ),
    inference(resolution,[],[f107,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(X2,X1)
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f107,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl6_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f280,plain,
    ( r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f278])).

fof(f278,plain,
    ( spl6_31
  <=> r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f130,plain,
    ( sK1 != u1_struct_0(sK0)
    | spl6_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl6_13
  <=> sK1 = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f281,plain,
    ( spl6_13
    | spl6_31
    | ~ spl6_23 ),
    inference(avatar_split_clause,[],[f275,f204,f278,f129])).

fof(f204,plain,
    ( spl6_23
  <=> ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f275,plain,
    ( r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1)
    | sK1 = u1_struct_0(sK0)
    | ~ spl6_23 ),
    inference(factoring,[],[f224])).

fof(f224,plain,
    ( ! [X1] :
        ( r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1)
        | r2_hidden(sK5(X1,u1_struct_0(sK0)),X1)
        | u1_struct_0(sK0) = X1 )
    | ~ spl6_23 ),
    inference(resolution,[],[f222,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK5(X0,X1),X1)
      | r2_hidden(sK5(X0,X1),X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f222,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,u1_struct_0(sK0))
        | r2_hidden(X3,sK1) )
    | ~ spl6_23 ),
    inference(resolution,[],[f205,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f205,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | r2_hidden(X1,sK1) )
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f204])).

fof(f263,plain,
    ( ~ spl6_14
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f258,f149,f144])).

fof(f144,plain,
    ( spl6_14
  <=> v1_subset_1(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f149,plain,
    ( spl6_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f258,plain,
    ( ~ v1_subset_1(sK1,sK1)
    | ~ spl6_15 ),
    inference(resolution,[],[f151,f58])).

fof(f58,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f151,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f257,plain,
    ( sK1 != u1_struct_0(sK0)
    | v1_subset_1(sK1,sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f256,plain,
    ( sK1 != u1_struct_0(sK0)
    | v1_xboole_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f255,plain,
    ( sK1 != u1_struct_0(sK0)
    | r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f233,plain,
    ( spl6_24
    | spl6_25
    | ~ spl6_22 ),
    inference(avatar_split_clause,[],[f216,f200,f230,f226])).

fof(f226,plain,
    ( spl6_24
  <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f230,plain,
    ( spl6_25
  <=> v1_xboole_0(u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f200,plain,
    ( spl6_22
  <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f216,plain,
    ( v1_xboole_0(u1_struct_0(sK0))
    | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl6_22 ),
    inference(resolution,[],[f201,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f201,plain,
    ( m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f200])).

fof(f214,plain,
    ( ~ spl6_7
    | spl6_22 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl6_7
    | spl6_22 ),
    inference(unit_resulting_resolution,[],[f92,f202,f40])).

fof(f40,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0))
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).

fof(f202,plain,
    ( ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
    | spl6_22 ),
    inference(avatar_component_clause,[],[f200])).

fof(f92,plain,
    ( l1_orders_2(sK0)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl6_7
  <=> l1_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f206,plain,
    ( spl6_2
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_12
    | ~ spl6_22
    | spl6_23
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f198,f193,f204,f200,f121,f80,f85,f90,f65])).

fof(f65,plain,
    ( spl6_2
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f85,plain,
    ( spl6_6
  <=> v1_yellow_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f80,plain,
    ( spl6_5
  <=> v5_orders_2(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f121,plain,
    ( spl6_12
  <=> r2_hidden(k3_yellow_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f193,plain,
    ( spl6_21
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | r2_hidden(X1,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f198,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | v2_struct_0(sK0) )
    | ~ spl6_21 ),
    inference(duplicate_literal_removal,[],[f197])).

fof(f197,plain,
    ( ! [X1] :
        ( r2_hidden(X1,sK1)
        | ~ m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))
        | ~ r2_hidden(k3_yellow_0(sK0),sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ v5_orders_2(sK0)
        | ~ v1_yellow_0(sK0)
        | ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0) )
    | ~ spl6_21 ),
    inference(resolution,[],[f194,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_orders_2(X0,k3_yellow_0(X0),X1)
      | ~ v5_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

% (11204)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_orders_2(X0,k3_yellow_0(X0),X1)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_orders_2(X0)
      | ~ v1_yellow_0(X0)
      | ~ v5_orders_2(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r1_orders_2(X0,k3_yellow_0(X0),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).

fof(f194,plain,
    ( ! [X0,X1] :
        ( ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f193])).

fof(f195,plain,
    ( ~ spl6_9
    | spl6_21
    | ~ spl6_7
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f111,f105,f90,f193,f100])).

fof(f100,plain,
    ( spl6_9
  <=> v13_waybel_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f111,plain,
    ( ! [X0,X1] :
        ( ~ l1_orders_2(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | ~ r2_hidden(X0,sK1)
        | ~ r1_orders_2(sK0,X0,X1)
        | r2_hidden(X1,sK1)
        | ~ v13_waybel_0(sK1,sK0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f107,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_orders_2(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_subset_1(X3,u1_struct_0(X0))
      | ~ r2_hidden(X2,X1)
      | ~ r1_orders_2(X0,X2,X3)
      | r2_hidden(X3,X1)
      | ~ v13_waybel_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( ! [X3] :
                    ( r2_hidden(X3,X1)
                    | ~ r1_orders_2(X0,X2,X3)
                    | ~ r2_hidden(X2,X1)
                    | ~ m1_subset_1(X3,u1_struct_0(X0)) )
                | ~ m1_subset_1(X2,u1_struct_0(X0)) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_orders_2(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_orders_2(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v13_waybel_0(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,u1_struct_0(X0))
               => ! [X3] :
                    ( m1_subset_1(X3,u1_struct_0(X0))
                   => ( ( r1_orders_2(X0,X2,X3)
                        & r2_hidden(X2,X1) )
                     => r2_hidden(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).

fof(f152,plain,
    ( spl6_15
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f136,f129,f105,f149])).

fof(f136,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_10
    | ~ spl6_13 ),
    inference(backward_demodulation,[],[f107,f131])).

fof(f131,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f129])).

fof(f132,plain,
    ( spl6_11
    | spl6_13
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f114,f105,f129,f117])).

fof(f117,plain,
    ( spl6_11
  <=> v1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f114,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_10 ),
    inference(resolution,[],[f107,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f125,plain,
    ( ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f29,f121,f117])).

fof(f29,plain,
    ( r2_hidden(k3_yellow_0(sK0),sK1)
    | ~ v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v1_subset_1(X1,u1_struct_0(X0))
          <~> ~ r2_hidden(k3_yellow_0(X0),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & v13_waybel_0(X1,X0)
          & v2_waybel_0(X1,X0)
          & ~ v1_xboole_0(X1) )
      & l1_orders_2(X0)
      & v1_yellow_0(X0)
      & v5_orders_2(X0)
      & v4_orders_2(X0)
      & v3_orders_2(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_orders_2(X0)
          & v1_yellow_0(X0)
          & v5_orders_2(X0)
          & v4_orders_2(X0)
          & v3_orders_2(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & v13_waybel_0(X1,X0)
              & v2_waybel_0(X1,X0)
              & ~ v1_xboole_0(X1) )
           => ( v1_subset_1(X1,u1_struct_0(X0))
            <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_orders_2(X0)
        & v1_yellow_0(X0)
        & v5_orders_2(X0)
        & v4_orders_2(X0)
        & v3_orders_2(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & v13_waybel_0(X1,X0)
            & v2_waybel_0(X1,X0)
            & ~ v1_xboole_0(X1) )
         => ( v1_subset_1(X1,u1_struct_0(X0))
          <=> ~ r2_hidden(k3_yellow_0(X0),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).

fof(f124,plain,
    ( spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f28,f121,f117])).

fof(f28,plain,
    ( ~ r2_hidden(k3_yellow_0(sK0),sK1)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f108,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f33,f105])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f103,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f32,f100])).

fof(f32,plain,(
    v13_waybel_0(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f93,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f39,f90])).

fof(f39,plain,(
    l1_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f38,f85])).

fof(f38,plain,(
    v1_yellow_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f83,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f37,f80])).

fof(f37,plain,(
    v5_orders_2(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    ~ spl6_2 ),
    inference(avatar_split_clause,[],[f34,f65])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f63,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f30,f60])).

% (11229)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
fof(f60,plain,
    ( spl6_1
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f30,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:19:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (11231)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.21/0.52  % (11223)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.21/0.52  % (11215)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (11214)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.21/0.53  % (11203)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.53  % (11225)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.21/0.53  % (11213)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.21/0.53  % (11217)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.21/0.53  % (11208)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.54  % (11207)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.54  % (11220)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.21/0.54  % (11205)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.54  % (11212)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.21/0.54  % (11206)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.21/0.54  % (11224)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.55  % (11225)Refutation found. Thanks to Tanya!
% 0.21/0.55  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (11227)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.21/0.55  % (11230)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.21/0.55  % (11221)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.55  % (11232)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.21/0.55  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f287,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f63,f68,f83,f88,f93,f103,f108,f124,f125,f132,f152,f195,f206,f214,f233,f255,f256,f257,f263,f281,f286])).
% 1.45/0.55  fof(f286,plain,(
% 1.45/0.55    ~spl6_10 | spl6_13 | ~spl6_31),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f283])).
% 1.45/0.55  fof(f283,plain,(
% 1.45/0.55    $false | (~spl6_10 | spl6_13 | ~spl6_31)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f130,f280,f280,f127])).
% 1.45/0.55  fof(f127,plain,(
% 1.45/0.55    ( ! [X0] : (~r2_hidden(sK5(X0,u1_struct_0(sK0)),sK1) | ~r2_hidden(sK5(X0,u1_struct_0(sK0)),X0) | u1_struct_0(sK0) = X0) ) | ~spl6_10),
% 1.45/0.55    inference(resolution,[],[f113,f56])).
% 1.45/0.55  fof(f56,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r2_hidden(sK5(X0,X1),X1) | ~r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f25])).
% 1.45/0.55  fof(f25,plain,(
% 1.45/0.55    ! [X0,X1] : (X0 = X1 | ? [X2] : (r2_hidden(X2,X0) <~> r2_hidden(X2,X1)))),
% 1.45/0.55    inference(ennf_transformation,[],[f1])).
% 1.45/0.55  fof(f1,axiom,(
% 1.45/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) <=> r2_hidden(X2,X1)) => X0 = X1)),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tarski)).
% 1.45/0.55  fof(f113,plain,(
% 1.45/0.55    ( ! [X3] : (r2_hidden(X3,u1_struct_0(sK0)) | ~r2_hidden(X3,sK1)) ) | ~spl6_10),
% 1.45/0.55    inference(resolution,[],[f107,f54])).
% 1.45/0.55  fof(f54,plain,(
% 1.45/0.55    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(X2,X1) | r2_hidden(X2,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f24])).
% 1.45/0.55  fof(f24,plain,(
% 1.45/0.55    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f2])).
% 1.45/0.55  fof(f2,axiom,(
% 1.45/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 1.45/0.55  fof(f107,plain,(
% 1.45/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_10),
% 1.45/0.55    inference(avatar_component_clause,[],[f105])).
% 1.45/0.55  fof(f105,plain,(
% 1.45/0.55    spl6_10 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 1.45/0.55  fof(f280,plain,(
% 1.45/0.55    r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1) | ~spl6_31),
% 1.45/0.55    inference(avatar_component_clause,[],[f278])).
% 1.45/0.55  fof(f278,plain,(
% 1.45/0.55    spl6_31 <=> r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 1.45/0.55  fof(f130,plain,(
% 1.45/0.55    sK1 != u1_struct_0(sK0) | spl6_13),
% 1.45/0.55    inference(avatar_component_clause,[],[f129])).
% 1.45/0.55  fof(f129,plain,(
% 1.45/0.55    spl6_13 <=> sK1 = u1_struct_0(sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.45/0.55  fof(f281,plain,(
% 1.45/0.55    spl6_13 | spl6_31 | ~spl6_23),
% 1.45/0.55    inference(avatar_split_clause,[],[f275,f204,f278,f129])).
% 1.45/0.55  fof(f204,plain,(
% 1.45/0.55    spl6_23 <=> ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 1.45/0.55  fof(f275,plain,(
% 1.45/0.55    r2_hidden(sK5(sK1,u1_struct_0(sK0)),sK1) | sK1 = u1_struct_0(sK0) | ~spl6_23),
% 1.45/0.55    inference(factoring,[],[f224])).
% 1.45/0.55  fof(f224,plain,(
% 1.45/0.55    ( ! [X1] : (r2_hidden(sK5(X1,u1_struct_0(sK0)),sK1) | r2_hidden(sK5(X1,u1_struct_0(sK0)),X1) | u1_struct_0(sK0) = X1) ) | ~spl6_23),
% 1.45/0.55    inference(resolution,[],[f222,f55])).
% 1.45/0.55  fof(f55,plain,(
% 1.45/0.55    ( ! [X0,X1] : (r2_hidden(sK5(X0,X1),X1) | r2_hidden(sK5(X0,X1),X0) | X0 = X1) )),
% 1.45/0.55    inference(cnf_transformation,[],[f25])).
% 1.45/0.55  fof(f222,plain,(
% 1.45/0.55    ( ! [X3] : (~r2_hidden(X3,u1_struct_0(sK0)) | r2_hidden(X3,sK1)) ) | ~spl6_23),
% 1.45/0.55    inference(resolution,[],[f205,f50])).
% 1.45/0.55  fof(f50,plain,(
% 1.45/0.55    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f20])).
% 1.45/0.55  fof(f20,plain,(
% 1.45/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.45/0.55    inference(ennf_transformation,[],[f4])).
% 1.45/0.55  fof(f4,axiom,(
% 1.45/0.55    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.45/0.55  fof(f205,plain,(
% 1.45/0.55    ( ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | r2_hidden(X1,sK1)) ) | ~spl6_23),
% 1.45/0.55    inference(avatar_component_clause,[],[f204])).
% 1.45/0.55  fof(f263,plain,(
% 1.45/0.55    ~spl6_14 | ~spl6_15),
% 1.45/0.55    inference(avatar_split_clause,[],[f258,f149,f144])).
% 1.45/0.55  fof(f144,plain,(
% 1.45/0.55    spl6_14 <=> v1_subset_1(sK1,sK1)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 1.45/0.55  fof(f149,plain,(
% 1.45/0.55    spl6_15 <=> m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 1.45/0.55  fof(f258,plain,(
% 1.45/0.55    ~v1_subset_1(sK1,sK1) | ~spl6_15),
% 1.45/0.55    inference(resolution,[],[f151,f58])).
% 1.45/0.55  fof(f58,plain,(
% 1.45/0.55    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 1.45/0.55    inference(equality_resolution,[],[f53])).
% 1.45/0.55  fof(f53,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f23])).
% 1.45/0.55  fof(f23,plain,(
% 1.45/0.55    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f10])).
% 1.45/0.55  fof(f10,axiom,(
% 1.45/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 1.45/0.55  fof(f151,plain,(
% 1.45/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~spl6_15),
% 1.45/0.55    inference(avatar_component_clause,[],[f149])).
% 1.45/0.55  fof(f257,plain,(
% 1.45/0.55    sK1 != u1_struct_0(sK0) | v1_subset_1(sK1,sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.45/0.55  fof(f256,plain,(
% 1.45/0.55    sK1 != u1_struct_0(sK0) | v1_xboole_0(sK1) | ~v1_xboole_0(u1_struct_0(sK0))),
% 1.45/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.45/0.55  fof(f255,plain,(
% 1.45/0.55    sK1 != u1_struct_0(sK0) | r2_hidden(k3_yellow_0(sK0),sK1) | ~r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.45/0.55    introduced(theory_tautology_sat_conflict,[])).
% 1.45/0.55  fof(f233,plain,(
% 1.45/0.55    spl6_24 | spl6_25 | ~spl6_22),
% 1.45/0.55    inference(avatar_split_clause,[],[f216,f200,f230,f226])).
% 1.45/0.55  fof(f226,plain,(
% 1.45/0.55    spl6_24 <=> r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 1.45/0.55  fof(f230,plain,(
% 1.45/0.55    spl6_25 <=> v1_xboole_0(u1_struct_0(sK0))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 1.45/0.55  fof(f200,plain,(
% 1.45/0.55    spl6_22 <=> m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 1.45/0.55  fof(f216,plain,(
% 1.45/0.55    v1_xboole_0(u1_struct_0(sK0)) | r2_hidden(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl6_22),
% 1.45/0.55    inference(resolution,[],[f201,f51])).
% 1.45/0.55  fof(f51,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f22])).
% 1.45/0.55  fof(f22,plain,(
% 1.45/0.55    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 1.45/0.55    inference(flattening,[],[f21])).
% 1.45/0.55  fof(f21,plain,(
% 1.45/0.55    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 1.45/0.55    inference(ennf_transformation,[],[f5])).
% 1.45/0.55  fof(f5,axiom,(
% 1.45/0.55    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 1.45/0.55  fof(f201,plain,(
% 1.45/0.55    m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~spl6_22),
% 1.45/0.55    inference(avatar_component_clause,[],[f200])).
% 1.45/0.55  fof(f214,plain,(
% 1.45/0.55    ~spl6_7 | spl6_22),
% 1.45/0.55    inference(avatar_contradiction_clause,[],[f208])).
% 1.45/0.55  fof(f208,plain,(
% 1.45/0.55    $false | (~spl6_7 | spl6_22)),
% 1.45/0.55    inference(unit_resulting_resolution,[],[f92,f202,f40])).
% 1.45/0.55  fof(f40,plain,(
% 1.45/0.55    ( ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f15])).
% 1.45/0.55  fof(f15,plain,(
% 1.45/0.55    ! [X0] : (m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)) | ~l1_orders_2(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f7])).
% 1.45/0.55  fof(f7,axiom,(
% 1.45/0.55    ! [X0] : (l1_orders_2(X0) => m1_subset_1(k3_yellow_0(X0),u1_struct_0(X0)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_yellow_0)).
% 1.45/0.55  fof(f202,plain,(
% 1.45/0.55    ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | spl6_22),
% 1.45/0.55    inference(avatar_component_clause,[],[f200])).
% 1.45/0.55  fof(f92,plain,(
% 1.45/0.55    l1_orders_2(sK0) | ~spl6_7),
% 1.45/0.55    inference(avatar_component_clause,[],[f90])).
% 1.45/0.55  fof(f90,plain,(
% 1.45/0.55    spl6_7 <=> l1_orders_2(sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 1.45/0.55  fof(f206,plain,(
% 1.45/0.55    spl6_2 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_12 | ~spl6_22 | spl6_23 | ~spl6_21),
% 1.45/0.55    inference(avatar_split_clause,[],[f198,f193,f204,f200,f121,f80,f85,f90,f65])).
% 1.45/0.55  fof(f65,plain,(
% 1.45/0.55    spl6_2 <=> v2_struct_0(sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 1.45/0.55  fof(f85,plain,(
% 1.45/0.55    spl6_6 <=> v1_yellow_0(sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 1.45/0.55  fof(f80,plain,(
% 1.45/0.55    spl6_5 <=> v5_orders_2(sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 1.45/0.55  fof(f121,plain,(
% 1.45/0.55    spl6_12 <=> r2_hidden(k3_yellow_0(sK0),sK1)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 1.45/0.55  fof(f193,plain,(
% 1.45/0.55    spl6_21 <=> ! [X1,X0] : (~m1_subset_1(X0,u1_struct_0(sK0)) | r2_hidden(X1,sK1) | ~r1_orders_2(sK0,X0,X1) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 1.45/0.55  fof(f198,plain,(
% 1.45/0.55    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | v2_struct_0(sK0)) ) | ~spl6_21),
% 1.45/0.55    inference(duplicate_literal_removal,[],[f197])).
% 1.45/0.55  fof(f197,plain,(
% 1.45/0.55    ( ! [X1] : (r2_hidden(X1,sK1) | ~m1_subset_1(k3_yellow_0(sK0),u1_struct_0(sK0)) | ~r2_hidden(k3_yellow_0(sK0),sK1) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~v5_orders_2(sK0) | ~v1_yellow_0(sK0) | ~l1_orders_2(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_struct_0(sK0)) ) | ~spl6_21),
% 1.45/0.55    inference(resolution,[],[f194,f47])).
% 1.45/0.55  fof(f47,plain,(
% 1.45/0.55    ( ! [X0,X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~v5_orders_2(X0) | ~v1_yellow_0(X0) | ~l1_orders_2(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f19])).
% 1.45/0.55  % (11204)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 1.45/0.55  fof(f19,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0))),
% 1.45/0.55    inference(flattening,[],[f18])).
% 1.45/0.55  fof(f18,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : (r1_orders_2(X0,k3_yellow_0(X0),X1) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_orders_2(X0) | ~v1_yellow_0(X0) | ~v5_orders_2(X0) | v2_struct_0(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f8])).
% 1.45/0.55  fof(f8,axiom,(
% 1.45/0.55    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r1_orders_2(X0,k3_yellow_0(X0),X1)))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_yellow_0)).
% 1.45/0.55  fof(f194,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl6_21),
% 1.45/0.55    inference(avatar_component_clause,[],[f193])).
% 1.45/0.55  fof(f195,plain,(
% 1.45/0.55    ~spl6_9 | spl6_21 | ~spl6_7 | ~spl6_10),
% 1.45/0.55    inference(avatar_split_clause,[],[f111,f105,f90,f193,f100])).
% 1.45/0.55  fof(f100,plain,(
% 1.45/0.55    spl6_9 <=> v13_waybel_0(sK1,sK0)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 1.45/0.55  fof(f111,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~l1_orders_2(sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X1,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1) | ~r1_orders_2(sK0,X0,X1) | r2_hidden(X1,sK1) | ~v13_waybel_0(sK1,sK0)) ) | ~spl6_10),
% 1.45/0.55    inference(resolution,[],[f107,f45])).
% 1.45/0.55  fof(f45,plain,(
% 1.45/0.55    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_orders_2(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X3,u1_struct_0(X0)) | ~r2_hidden(X2,X1) | ~r1_orders_2(X0,X2,X3) | r2_hidden(X3,X1) | ~v13_waybel_0(X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f17])).
% 1.45/0.55  fof(f17,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : (r2_hidden(X3,X1) | ~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.45/0.55    inference(flattening,[],[f16])).
% 1.45/0.55  fof(f16,plain,(
% 1.45/0.55    ! [X0] : (! [X1] : ((v13_waybel_0(X1,X0) <=> ! [X2] : (! [X3] : ((r2_hidden(X3,X1) | (~r1_orders_2(X0,X2,X3) | ~r2_hidden(X2,X1))) | ~m1_subset_1(X3,u1_struct_0(X0))) | ~m1_subset_1(X2,u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_orders_2(X0))),
% 1.45/0.55    inference(ennf_transformation,[],[f9])).
% 1.45/0.55  fof(f9,axiom,(
% 1.45/0.55    ! [X0] : (l1_orders_2(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v13_waybel_0(X1,X0) <=> ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(X0)) => ((r1_orders_2(X0,X2,X3) & r2_hidden(X2,X1)) => r2_hidden(X3,X1)))))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d20_waybel_0)).
% 1.45/0.55  fof(f152,plain,(
% 1.45/0.55    spl6_15 | ~spl6_10 | ~spl6_13),
% 1.45/0.55    inference(avatar_split_clause,[],[f136,f129,f105,f149])).
% 1.45/0.55  fof(f136,plain,(
% 1.45/0.55    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | (~spl6_10 | ~spl6_13)),
% 1.45/0.55    inference(backward_demodulation,[],[f107,f131])).
% 1.45/0.55  fof(f131,plain,(
% 1.45/0.55    sK1 = u1_struct_0(sK0) | ~spl6_13),
% 1.45/0.55    inference(avatar_component_clause,[],[f129])).
% 1.45/0.55  fof(f132,plain,(
% 1.45/0.55    spl6_11 | spl6_13 | ~spl6_10),
% 1.45/0.55    inference(avatar_split_clause,[],[f114,f105,f129,f117])).
% 1.45/0.55  fof(f117,plain,(
% 1.45/0.55    spl6_11 <=> v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 1.45/0.55  fof(f114,plain,(
% 1.45/0.55    sK1 = u1_struct_0(sK0) | v1_subset_1(sK1,u1_struct_0(sK0)) | ~spl6_10),
% 1.45/0.55    inference(resolution,[],[f107,f52])).
% 1.45/0.55  fof(f52,plain,(
% 1.45/0.55    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 1.45/0.55    inference(cnf_transformation,[],[f23])).
% 1.45/0.55  fof(f125,plain,(
% 1.45/0.55    ~spl6_11 | spl6_12),
% 1.45/0.55    inference(avatar_split_clause,[],[f29,f121,f117])).
% 1.45/0.55  fof(f29,plain,(
% 1.45/0.55    r2_hidden(k3_yellow_0(sK0),sK1) | ~v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f14,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) & l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0))),
% 1.45/0.55    inference(flattening,[],[f13])).
% 1.45/0.55  fof(f13,plain,(
% 1.45/0.55    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) <~> ~r2_hidden(k3_yellow_0(X0),X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1))) & (l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)))),
% 1.45/0.55    inference(ennf_transformation,[],[f12])).
% 1.45/0.55  fof(f12,negated_conjecture,(
% 1.45/0.55    ~! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.45/0.55    inference(negated_conjecture,[],[f11])).
% 1.45/0.55  fof(f11,conjecture,(
% 1.45/0.55    ! [X0] : ((l1_orders_2(X0) & v1_yellow_0(X0) & v5_orders_2(X0) & v4_orders_2(X0) & v3_orders_2(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v13_waybel_0(X1,X0) & v2_waybel_0(X1,X0) & ~v1_xboole_0(X1)) => (v1_subset_1(X1,u1_struct_0(X0)) <=> ~r2_hidden(k3_yellow_0(X0),X1))))),
% 1.45/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_waybel_7)).
% 1.45/0.55  fof(f124,plain,(
% 1.45/0.55    spl6_11 | ~spl6_12),
% 1.45/0.55    inference(avatar_split_clause,[],[f28,f121,f117])).
% 1.45/0.55  fof(f28,plain,(
% 1.45/0.55    ~r2_hidden(k3_yellow_0(sK0),sK1) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f108,plain,(
% 1.45/0.55    spl6_10),
% 1.45/0.55    inference(avatar_split_clause,[],[f33,f105])).
% 1.45/0.55  fof(f33,plain,(
% 1.45/0.55    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f103,plain,(
% 1.45/0.55    spl6_9),
% 1.45/0.55    inference(avatar_split_clause,[],[f32,f100])).
% 1.45/0.55  fof(f32,plain,(
% 1.45/0.55    v13_waybel_0(sK1,sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f93,plain,(
% 1.45/0.55    spl6_7),
% 1.45/0.55    inference(avatar_split_clause,[],[f39,f90])).
% 1.45/0.55  fof(f39,plain,(
% 1.45/0.55    l1_orders_2(sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f88,plain,(
% 1.45/0.55    spl6_6),
% 1.45/0.55    inference(avatar_split_clause,[],[f38,f85])).
% 1.45/0.55  fof(f38,plain,(
% 1.45/0.55    v1_yellow_0(sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f83,plain,(
% 1.45/0.55    spl6_5),
% 1.45/0.55    inference(avatar_split_clause,[],[f37,f80])).
% 1.45/0.55  fof(f37,plain,(
% 1.45/0.55    v5_orders_2(sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f68,plain,(
% 1.45/0.55    ~spl6_2),
% 1.45/0.55    inference(avatar_split_clause,[],[f34,f65])).
% 1.45/0.55  fof(f34,plain,(
% 1.45/0.55    ~v2_struct_0(sK0)),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  fof(f63,plain,(
% 1.45/0.55    ~spl6_1),
% 1.45/0.55    inference(avatar_split_clause,[],[f30,f60])).
% 1.45/0.55  % (11229)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.45/0.55  fof(f60,plain,(
% 1.45/0.55    spl6_1 <=> v1_xboole_0(sK1)),
% 1.45/0.55    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 1.45/0.55  fof(f30,plain,(
% 1.45/0.55    ~v1_xboole_0(sK1)),
% 1.45/0.55    inference(cnf_transformation,[],[f14])).
% 1.45/0.55  % SZS output end Proof for theBenchmark
% 1.45/0.55  % (11225)------------------------------
% 1.45/0.55  % (11225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.45/0.55  % (11225)Termination reason: Refutation
% 1.45/0.55  
% 1.45/0.55  % (11225)Memory used [KB]: 10874
% 1.45/0.55  % (11225)Time elapsed: 0.094 s
% 1.45/0.55  % (11225)------------------------------
% 1.45/0.55  % (11225)------------------------------
% 1.45/0.55  % (11218)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.45/0.55  % (11216)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.45/0.55  % (11202)Success in time 0.194 s
%------------------------------------------------------------------------------
