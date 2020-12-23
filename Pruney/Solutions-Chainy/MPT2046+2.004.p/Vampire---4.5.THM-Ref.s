%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:23:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 147 expanded)
%              Number of leaves         :   19 (  61 expanded)
%              Depth                    :   10
%              Number of atoms          :  286 ( 530 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f201,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f102,f121,f134,f195])).

fof(f195,plain,
    ( spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(avatar_contradiction_clause,[],[f194])).

fof(f194,plain,
    ( $false
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_9
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f165,f133])).

fof(f133,plain,
    ( m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl4_11
  <=> m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f165,plain,
    ( ~ m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f72,f67,f62,f57,f52,f82,f120,f35])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ r1_tarski(k1_yellow19(X0,X1),X2)
      | r2_waybel_7(X0,X2,X1)
      | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r2_waybel_7(X0,X2,X1)
                  | ~ r1_tarski(k1_yellow19(X0,X1),X2) )
                & ( r1_tarski(k1_yellow19(X0,X1),X2)
                  | ~ r2_waybel_7(X0,X2,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
              | ~ v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
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
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
                & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) )
             => ( r2_waybel_7(X0,X2,X1)
              <=> r1_tarski(k1_yellow19(X0,X1),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).

fof(f120,plain,
    ( v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f118])).

fof(f118,plain,
    ( spl4_9
  <=> v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f82,plain,(
    ! [X0] : r1_tarski(X0,X0) ),
    inference(backward_demodulation,[],[f74,f79])).

fof(f79,plain,(
    ! [X0] : sK3(X0) = X0 ),
    inference(unit_resulting_resolution,[],[f37,f36,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ( v1_subset_1(X1,X0)
          | X0 = X1 )
        & ( X0 != X1
          | ~ v1_subset_1(X1,X0) ) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f36,plain,(
    ! [X0] : m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_subset_1(sK3(X0),X0)
      & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f1,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ~ v1_subset_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => ( ~ v1_subset_1(sK3(X0),X0)
        & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f1,axiom,(
    ! [X0] :
    ? [X1] :
      ( ~ v1_subset_1(X1,X0)
      & m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

fof(f37,plain,(
    ! [X0] : ~ v1_subset_1(sK3(X0),X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    ! [X0] : r1_tarski(sK3(X0),X0) ),
    inference(unit_resulting_resolution,[],[f36,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f52,plain,
    ( ~ r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f50])).

fof(f50,plain,
    ( spl4_1
  <=> r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f57,plain,
    ( m1_subset_1(sK2,u1_struct_0(sK1))
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f55,plain,
    ( spl4_2
  <=> m1_subset_1(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f62,plain,
    ( l1_pre_topc(sK1)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f60])).

fof(f60,plain,
    ( spl4_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f67,plain,
    ( v2_pre_topc(sK1)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f65])).

fof(f65,plain,
    ( spl4_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f72,plain,
    ( ~ v2_struct_0(sK1)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f70,plain,
    ( spl4_5
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f134,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f127,f70,f65,f60,f55,f131])).

fof(f127,plain,
    ( m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f72,f67,f62,f57,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0)))))
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow19)).

fof(f121,plain,
    ( spl4_9
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f104,f95,f118])).

fof(f95,plain,
    ( spl4_6
  <=> sP0(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f104,plain,
    ( v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1)))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f97,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
      | ~ sP0(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ sP0(X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f97,plain,
    ( sP0(sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f95])).

fof(f102,plain,
    ( spl4_6
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(avatar_split_clause,[],[f101,f70,f65,f60,f55,f95])).

fof(f101,plain,
    ( sP0(sK1,sK2)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4
    | spl4_5 ),
    inference(subsumption_resolution,[],[f100,f72])).

fof(f100,plain,
    ( sP0(sK1,sK2)
    | v2_struct_0(sK1)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f99,f67])).

fof(f99,plain,
    ( sP0(sK1,sK2)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f93,f62])).

fof(f93,plain,
    ( sP0(sK1,sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl4_2 ),
    inference(resolution,[],[f45,f57])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | sP0(X0,X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( sP0(X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f18])).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0)))
        & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0))))
        & ~ v1_xboole_0(k1_yellow19(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow19)).

fof(f73,plain,(
    ~ spl4_5 ),
    inference(avatar_split_clause,[],[f29,f70])).

fof(f29,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,
    ( ~ r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2)
    & m1_subset_1(sK2,u1_struct_0(sK1))
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
            & m1_subset_1(X1,u1_struct_0(X0)) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ r2_waybel_7(sK1,k1_yellow19(sK1,X1),X1)
          & m1_subset_1(X1,u1_struct_0(sK1)) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ~ r2_waybel_7(sK1,k1_yellow19(sK1,X1),X1)
        & m1_subset_1(X1,u1_struct_0(sK1)) )
   => ( ~ r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2)
      & m1_subset_1(sK2,u1_struct_0(sK1)) ) ),
    introduced(choice_axiom,[])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ r2_waybel_7(X0,k1_yellow19(X0,X1),X1)
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => r2_waybel_7(X0,k1_yellow19(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow19)).

fof(f68,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f30,f65])).

fof(f30,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f63,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f31,f60])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f22])).

fof(f58,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f32,f55])).

fof(f32,plain,(
    m1_subset_1(sK2,u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f22])).

fof(f53,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f33,f50])).

fof(f33,plain,(
    ~ r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2) ),
    inference(cnf_transformation,[],[f22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:46:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.41  % (11964)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.41  % (11964)Refutation found. Thanks to Tanya!
% 0.21/0.41  % SZS status Theorem for theBenchmark
% 0.21/0.41  % SZS output start Proof for theBenchmark
% 0.21/0.41  fof(f201,plain,(
% 0.21/0.41    $false),
% 0.21/0.41    inference(avatar_sat_refutation,[],[f53,f58,f63,f68,f73,f102,f121,f134,f195])).
% 0.21/0.41  fof(f195,plain,(
% 0.21/0.41    spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_9 | ~spl4_11),
% 0.21/0.41    inference(avatar_contradiction_clause,[],[f194])).
% 0.21/0.41  fof(f194,plain,(
% 0.21/0.41    $false | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_9 | ~spl4_11)),
% 0.21/0.41    inference(subsumption_resolution,[],[f165,f133])).
% 0.21/0.41  fof(f133,plain,(
% 0.21/0.41    m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) | ~spl4_11),
% 0.21/0.41    inference(avatar_component_clause,[],[f131])).
% 0.21/0.41  fof(f131,plain,(
% 0.21/0.41    spl4_11 <=> m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1)))))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.41  fof(f165,plain,(
% 0.21/0.41    ~m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) | (spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5 | ~spl4_9)),
% 0.21/0.41    inference(unit_resulting_resolution,[],[f72,f67,f62,f57,f52,f82,f120,f35])).
% 0.21/0.41  fof(f35,plain,(
% 0.21/0.41    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~r1_tarski(k1_yellow19(X0,X1),X2) | r2_waybel_7(X0,X2,X1) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f23])).
% 0.21/0.41  fof(f23,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (! [X2] : (((r2_waybel_7(X0,X2,X1) | ~r1_tarski(k1_yellow19(X0,X1),X2)) & (r1_tarski(k1_yellow19(X0,X1),X2) | ~r2_waybel_7(X0,X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.41    inference(nnf_transformation,[],[f12])).
% 0.21/0.41  fof(f12,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.41    inference(flattening,[],[f11])).
% 0.21/0.41  fof(f11,plain,(
% 0.21/0.41    ! [X0] : (! [X1] : (! [X2] : ((r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)) | (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0))))) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f6])).
% 0.21/0.41  fof(f6,axiom,(
% 0.21/0.41    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) & v13_waybel_0(X2,k3_yellow_1(k2_struct_0(X0)))) => (r2_waybel_7(X0,X2,X1) <=> r1_tarski(k1_yellow19(X0,X1),X2)))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow19)).
% 0.21/0.41  fof(f120,plain,(
% 0.21/0.41    v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1))) | ~spl4_9),
% 0.21/0.41    inference(avatar_component_clause,[],[f118])).
% 0.21/0.41  fof(f118,plain,(
% 0.21/0.41    spl4_9 <=> v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1)))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.41  fof(f82,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(X0,X0)) )),
% 0.21/0.41    inference(backward_demodulation,[],[f74,f79])).
% 0.21/0.41  fof(f79,plain,(
% 0.21/0.41    ( ! [X0] : (sK3(X0) = X0) )),
% 0.21/0.41    inference(unit_resulting_resolution,[],[f37,f36,f39])).
% 0.21/0.41  fof(f39,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f26])).
% 0.21/0.41  fof(f26,plain,(
% 0.21/0.41    ! [X0,X1] : (((v1_subset_1(X1,X0) | X0 = X1) & (X0 != X1 | ~v1_subset_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.41    inference(nnf_transformation,[],[f13])).
% 0.21/0.41  fof(f13,plain,(
% 0.21/0.41    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f3])).
% 0.21/0.41  fof(f3,axiom,(
% 0.21/0.41    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.41  fof(f36,plain,(
% 0.21/0.41    ( ! [X0] : (m1_subset_1(sK3(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.41    inference(cnf_transformation,[],[f25])).
% 0.21/0.41  fof(f25,plain,(
% 0.21/0.41    ! [X0] : (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0)))),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f1,f24])).
% 0.21/0.41  fof(f24,plain,(
% 0.21/0.41    ! [X0] : (? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0))) => (~v1_subset_1(sK3(X0),X0) & m1_subset_1(sK3(X0),k1_zfmisc_1(X0))))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f1,axiom,(
% 0.21/0.41    ! [X0] : ? [X1] : (~v1_subset_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).
% 0.21/0.41  fof(f37,plain,(
% 0.21/0.41    ( ! [X0] : (~v1_subset_1(sK3(X0),X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f25])).
% 0.21/0.41  fof(f74,plain,(
% 0.21/0.41    ( ! [X0] : (r1_tarski(sK3(X0),X0)) )),
% 0.21/0.41    inference(unit_resulting_resolution,[],[f36,f46])).
% 0.21/0.41  fof(f46,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f28])).
% 0.21/0.41  fof(f28,plain,(
% 0.21/0.41    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 0.21/0.41    inference(nnf_transformation,[],[f2])).
% 0.21/0.41  fof(f2,axiom,(
% 0.21/0.41    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.41  fof(f52,plain,(
% 0.21/0.41    ~r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2) | spl4_1),
% 0.21/0.41    inference(avatar_component_clause,[],[f50])).
% 0.21/0.41  fof(f50,plain,(
% 0.21/0.41    spl4_1 <=> r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.41  fof(f57,plain,(
% 0.21/0.41    m1_subset_1(sK2,u1_struct_0(sK1)) | ~spl4_2),
% 0.21/0.41    inference(avatar_component_clause,[],[f55])).
% 0.21/0.41  fof(f55,plain,(
% 0.21/0.41    spl4_2 <=> m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.41  fof(f62,plain,(
% 0.21/0.41    l1_pre_topc(sK1) | ~spl4_3),
% 0.21/0.41    inference(avatar_component_clause,[],[f60])).
% 0.21/0.41  fof(f60,plain,(
% 0.21/0.41    spl4_3 <=> l1_pre_topc(sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.41  fof(f67,plain,(
% 0.21/0.41    v2_pre_topc(sK1) | ~spl4_4),
% 0.21/0.41    inference(avatar_component_clause,[],[f65])).
% 0.21/0.41  fof(f65,plain,(
% 0.21/0.41    spl4_4 <=> v2_pre_topc(sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.41  fof(f72,plain,(
% 0.21/0.41    ~v2_struct_0(sK1) | spl4_5),
% 0.21/0.41    inference(avatar_component_clause,[],[f70])).
% 0.21/0.41  fof(f70,plain,(
% 0.21/0.41    spl4_5 <=> v2_struct_0(sK1)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.41  fof(f134,plain,(
% 0.21/0.41    spl4_11 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f127,f70,f65,f60,f55,f131])).
% 0.21/0.41  fof(f127,plain,(
% 0.21/0.41    m1_subset_1(k1_yellow19(sK1,sK2),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(sK1))))) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5)),
% 0.21/0.41    inference(unit_resulting_resolution,[],[f72,f67,f62,f57,f40])).
% 0.21/0.41  fof(f40,plain,(
% 0.21/0.41    ( ! [X0,X1] : (m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f15])).
% 0.21/0.41  fof(f15,plain,(
% 0.21/0.41    ! [X0,X1] : (m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.41    inference(flattening,[],[f14])).
% 0.21/0.41  fof(f14,plain,(
% 0.21/0.41    ! [X0,X1] : (m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f4])).
% 0.21/0.41  fof(f4,axiom,(
% 0.21/0.41    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => m1_subset_1(k1_yellow19(X0,X1),k1_zfmisc_1(u1_struct_0(k3_yellow_1(k2_struct_0(X0))))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_yellow19)).
% 0.21/0.41  fof(f121,plain,(
% 0.21/0.41    spl4_9 | ~spl4_6),
% 0.21/0.41    inference(avatar_split_clause,[],[f104,f95,f118])).
% 0.21/0.41  fof(f95,plain,(
% 0.21/0.41    spl4_6 <=> sP0(sK1,sK2)),
% 0.21/0.41    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.41  fof(f104,plain,(
% 0.21/0.41    v13_waybel_0(k1_yellow19(sK1,sK2),k3_yellow_1(k2_struct_0(sK1))) | ~spl4_6),
% 0.21/0.41    inference(unit_resulting_resolution,[],[f97,f44])).
% 0.21/0.41  fof(f44,plain,(
% 0.21/0.41    ( ! [X0,X1] : (v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) | ~sP0(X0,X1)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f27])).
% 0.21/0.41  fof(f27,plain,(
% 0.21/0.41    ! [X0,X1] : ((v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(k1_yellow19(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.41    inference(nnf_transformation,[],[f18])).
% 0.21/0.41  fof(f18,plain,(
% 0.21/0.41    ! [X0,X1] : ((v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(k1_yellow19(X0,X1))) | ~sP0(X0,X1))),
% 0.21/0.41    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.41  fof(f97,plain,(
% 0.21/0.41    sP0(sK1,sK2) | ~spl4_6),
% 0.21/0.41    inference(avatar_component_clause,[],[f95])).
% 0.21/0.41  fof(f102,plain,(
% 0.21/0.41    spl4_6 | ~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f101,f70,f65,f60,f55,f95])).
% 0.21/0.41  fof(f101,plain,(
% 0.21/0.41    sP0(sK1,sK2) | (~spl4_2 | ~spl4_3 | ~spl4_4 | spl4_5)),
% 0.21/0.41    inference(subsumption_resolution,[],[f100,f72])).
% 0.21/0.41  fof(f100,plain,(
% 0.21/0.41    sP0(sK1,sK2) | v2_struct_0(sK1) | (~spl4_2 | ~spl4_3 | ~spl4_4)),
% 0.21/0.41    inference(subsumption_resolution,[],[f99,f67])).
% 0.21/0.41  fof(f99,plain,(
% 0.21/0.41    sP0(sK1,sK2) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl4_2 | ~spl4_3)),
% 0.21/0.41    inference(subsumption_resolution,[],[f93,f62])).
% 0.21/0.41  fof(f93,plain,(
% 0.21/0.41    sP0(sK1,sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | ~spl4_2),
% 0.21/0.41    inference(resolution,[],[f45,f57])).
% 0.21/0.41  fof(f45,plain,(
% 0.21/0.41    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | sP0(X0,X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.41    inference(cnf_transformation,[],[f19])).
% 0.21/0.41  fof(f19,plain,(
% 0.21/0.41    ! [X0,X1] : (sP0(X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.41    inference(definition_folding,[],[f17,f18])).
% 0.21/0.41  fof(f17,plain,(
% 0.21/0.41    ! [X0,X1] : ((v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(k1_yellow19(X0,X1))) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.41    inference(flattening,[],[f16])).
% 0.21/0.41  fof(f16,plain,(
% 0.21/0.41    ! [X0,X1] : ((v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(k1_yellow19(X0,X1))) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.41    inference(ennf_transformation,[],[f5])).
% 0.21/0.41  fof(f5,axiom,(
% 0.21/0.41    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v13_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v2_waybel_0(k1_yellow19(X0,X1),k3_yellow_1(k2_struct_0(X0))) & v1_subset_1(k1_yellow19(X0,X1),u1_struct_0(k3_yellow_1(k2_struct_0(X0)))) & ~v1_xboole_0(k1_yellow19(X0,X1))))),
% 0.21/0.41    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_yellow19)).
% 0.21/0.41  fof(f73,plain,(
% 0.21/0.41    ~spl4_5),
% 0.21/0.41    inference(avatar_split_clause,[],[f29,f70])).
% 0.21/0.41  fof(f29,plain,(
% 0.21/0.41    ~v2_struct_0(sK1)),
% 0.21/0.41    inference(cnf_transformation,[],[f22])).
% 0.21/0.41  fof(f22,plain,(
% 0.21/0.41    (~r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2) & m1_subset_1(sK2,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.21/0.41    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2])],[f10,f21,f20])).
% 0.21/0.41  fof(f20,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (~r2_waybel_7(X0,k1_yellow19(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~r2_waybel_7(sK1,k1_yellow19(sK1,X1),X1) & m1_subset_1(X1,u1_struct_0(sK1))) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f21,plain,(
% 0.21/0.41    ? [X1] : (~r2_waybel_7(sK1,k1_yellow19(sK1,X1),X1) & m1_subset_1(X1,u1_struct_0(sK1))) => (~r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2) & m1_subset_1(sK2,u1_struct_0(sK1)))),
% 0.21/0.41    introduced(choice_axiom,[])).
% 0.21/0.41  fof(f10,plain,(
% 0.21/0.41    ? [X0] : (? [X1] : (~r2_waybel_7(X0,k1_yellow19(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.41    inference(flattening,[],[f9])).
% 0.21/0.42  fof(f9,plain,(
% 0.21/0.42    ? [X0] : (? [X1] : (~r2_waybel_7(X0,k1_yellow19(X0,X1),X1) & m1_subset_1(X1,u1_struct_0(X0))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.42    inference(ennf_transformation,[],[f8])).
% 0.21/0.42  fof(f8,negated_conjecture,(
% 0.21/0.42    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_waybel_7(X0,k1_yellow19(X0,X1),X1)))),
% 0.21/0.42    inference(negated_conjecture,[],[f7])).
% 0.21/0.42  fof(f7,conjecture,(
% 0.21/0.42    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => r2_waybel_7(X0,k1_yellow19(X0,X1),X1)))),
% 0.21/0.42    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_yellow19)).
% 0.21/0.42  fof(f68,plain,(
% 0.21/0.42    spl4_4),
% 0.21/0.42    inference(avatar_split_clause,[],[f30,f65])).
% 0.21/0.42  fof(f30,plain,(
% 0.21/0.42    v2_pre_topc(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f63,plain,(
% 0.21/0.42    spl4_3),
% 0.21/0.42    inference(avatar_split_clause,[],[f31,f60])).
% 0.21/0.42  fof(f31,plain,(
% 0.21/0.42    l1_pre_topc(sK1)),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f58,plain,(
% 0.21/0.42    spl4_2),
% 0.21/0.42    inference(avatar_split_clause,[],[f32,f55])).
% 0.21/0.42  fof(f32,plain,(
% 0.21/0.42    m1_subset_1(sK2,u1_struct_0(sK1))),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  fof(f53,plain,(
% 0.21/0.42    ~spl4_1),
% 0.21/0.42    inference(avatar_split_clause,[],[f33,f50])).
% 0.21/0.42  fof(f33,plain,(
% 0.21/0.42    ~r2_waybel_7(sK1,k1_yellow19(sK1,sK2),sK2)),
% 0.21/0.42    inference(cnf_transformation,[],[f22])).
% 0.21/0.42  % SZS output end Proof for theBenchmark
% 0.21/0.42  % (11964)------------------------------
% 0.21/0.42  % (11964)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.42  % (11964)Termination reason: Refutation
% 0.21/0.42  
% 0.21/0.42  % (11964)Memory used [KB]: 10746
% 0.21/0.42  % (11964)Time elapsed: 0.008 s
% 0.21/0.42  % (11964)------------------------------
% 0.21/0.42  % (11964)------------------------------
% 0.21/0.42  % (11947)Success in time 0.062 s
%------------------------------------------------------------------------------
