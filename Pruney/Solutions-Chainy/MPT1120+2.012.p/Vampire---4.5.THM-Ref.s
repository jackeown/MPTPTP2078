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
% DateTime   : Thu Dec  3 13:09:17 EST 2020

% Result     : Theorem 1.58s
% Output     : Refutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :  101 ( 184 expanded)
%              Number of leaves         :   26 (  75 expanded)
%              Depth                    :    8
%              Number of atoms          :  264 ( 502 expanded)
%              Number of equality atoms :   12 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f289,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f119,f129,f133,f167,f178,f182,f185,f278,f285,f288])).

fof(f288,plain,(
    spl3_34 ),
    inference(avatar_contradiction_clause,[],[f286])).

fof(f286,plain,
    ( $false
    | spl3_34 ),
    inference(unit_resulting_resolution,[],[f48,f284,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f284,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl3_34 ),
    inference(avatar_component_clause,[],[f282])).

fof(f282,plain,
    ( spl3_34
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f48,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
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

fof(f285,plain,
    ( ~ spl3_34
    | spl3_33 ),
    inference(avatar_split_clause,[],[f279,f275,f282])).

fof(f275,plain,
    ( spl3_33
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f279,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(sK2))
    | spl3_33 ),
    inference(resolution,[],[f277,f113])).

fof(f113,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f110])).

fof(f110,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f105,f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f42,f44])).

fof(f44,plain,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k9_subset_1(X1,X2,X0),X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(resolution,[],[f43,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f277,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f275])).

fof(f278,plain,
    ( ~ spl3_1
    | ~ spl3_20
    | ~ spl3_3
    | ~ spl3_33
    | spl3_19 ),
    inference(avatar_split_clause,[],[f200,f164,f275,f61,f171,f51])).

fof(f51,plain,
    ( spl3_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f171,plain,
    ( spl3_20
  <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f61,plain,
    ( spl3_3
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f164,plain,
    ( spl3_19
  <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f200,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_19 ),
    inference(resolution,[],[f166,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).

fof(f166,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f164])).

fof(f185,plain,(
    spl3_21 ),
    inference(avatar_contradiction_clause,[],[f183])).

fof(f183,plain,
    ( $false
    | spl3_21 ),
    inference(unit_resulting_resolution,[],[f48,f177,f46])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f34,f44])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k3_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k3_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

fof(f177,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | spl3_21 ),
    inference(avatar_component_clause,[],[f175])).

fof(f175,plain,
    ( spl3_21
  <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f182,plain,
    ( ~ spl3_3
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f179])).

fof(f179,plain,
    ( $false
    | ~ spl3_3
    | spl3_20 ),
    inference(unit_resulting_resolution,[],[f63,f173,f112])).

fof(f112,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_setfam_1(k2_tarski(X4,X5)),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(duplicate_literal_removal,[],[f111])).

fof(f111,plain,(
    ! [X4,X5,X3] :
      ( m1_subset_1(k1_setfam_1(k2_tarski(X4,X5)),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f43,f47])).

fof(f173,plain,
    ( ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f171])).

fof(f63,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f61])).

fof(f178,plain,
    ( ~ spl3_1
    | ~ spl3_20
    | ~ spl3_2
    | ~ spl3_21
    | spl3_18 ),
    inference(avatar_split_clause,[],[f169,f160,f175,f56,f171,f51])).

fof(f56,plain,
    ( spl3_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f160,plain,
    ( spl3_18
  <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f169,plain,
    ( ~ r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_18 ),
    inference(resolution,[],[f162,f40])).

fof(f162,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f160])).

fof(f167,plain,
    ( ~ spl3_18
    | ~ spl3_19
    | spl3_13 ),
    inference(avatar_split_clause,[],[f156,f126,f164,f160])).

fof(f126,plain,
    ( spl3_13
  <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f156,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2))
    | ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))
    | spl3_13 ),
    inference(resolution,[],[f128,f45])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f33,f44])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k3_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k3_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

fof(f128,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f133,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | spl3_12 ),
    inference(avatar_contradiction_clause,[],[f130])).

fof(f130,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | spl3_12 ),
    inference(unit_resulting_resolution,[],[f53,f63,f124,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f124,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_12 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl3_12
  <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f53,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f129,plain,
    ( ~ spl3_12
    | ~ spl3_13
    | spl3_11 ),
    inference(avatar_split_clause,[],[f120,f116,f126,f122])).

fof(f116,plain,
    ( spl3_11
  <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f120,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))
    | ~ m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(superposition,[],[f118,f47])).

fof(f118,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f119,plain,
    ( ~ spl3_3
    | ~ spl3_11
    | spl3_4 ),
    inference(avatar_split_clause,[],[f108,f66,f116,f61])).

fof(f66,plain,
    ( spl3_4
  <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f108,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_4 ),
    inference(superposition,[],[f68,f47])).

fof(f68,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    | spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f69,plain,(
    ~ spl3_4 ),
    inference(avatar_split_clause,[],[f32,f66])).

fof(f32,plain,(
    ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2)))
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X2] :
        ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2)))
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).

fof(f64,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f31,f61])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f56])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f54,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:05:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.55  % (15355)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.56  % (15356)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.57  % (15364)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.57  % (15347)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (15358)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.57  % (15362)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.58  % (15357)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.58  % (15365)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.58/0.58  % (15349)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.58/0.58  % (15353)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.58/0.58  % (15348)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.58/0.58  % (15358)Refutation not found, incomplete strategy% (15358)------------------------------
% 1.58/0.58  % (15358)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.58  % (15358)Termination reason: Refutation not found, incomplete strategy
% 1.58/0.58  
% 1.58/0.58  % (15358)Memory used [KB]: 10618
% 1.58/0.58  % (15358)Time elapsed: 0.143 s
% 1.58/0.58  % (15358)------------------------------
% 1.58/0.58  % (15358)------------------------------
% 1.58/0.59  % (15365)Refutation found. Thanks to Tanya!
% 1.58/0.59  % SZS status Theorem for theBenchmark
% 1.58/0.59  % SZS output start Proof for theBenchmark
% 1.58/0.59  fof(f289,plain,(
% 1.58/0.59    $false),
% 1.58/0.59    inference(avatar_sat_refutation,[],[f54,f59,f64,f69,f119,f129,f133,f167,f178,f182,f185,f278,f285,f288])).
% 1.58/0.59  fof(f288,plain,(
% 1.58/0.59    spl3_34),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f286])).
% 1.58/0.59  fof(f286,plain,(
% 1.58/0.59    $false | spl3_34),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f48,f284,f36])).
% 1.58/0.59  fof(f36,plain,(
% 1.58/0.59    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f26])).
% 1.58/0.59  fof(f26,plain,(
% 1.58/0.59    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.58/0.59    inference(nnf_transformation,[],[f7])).
% 1.58/0.59  fof(f7,axiom,(
% 1.58/0.59    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 1.58/0.59  fof(f284,plain,(
% 1.58/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | spl3_34),
% 1.58/0.59    inference(avatar_component_clause,[],[f282])).
% 1.58/0.59  fof(f282,plain,(
% 1.58/0.59    spl3_34 <=> m1_subset_1(sK2,k1_zfmisc_1(sK2))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.58/0.59  fof(f48,plain,(
% 1.58/0.59    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 1.58/0.59    inference(equality_resolution,[],[f38])).
% 1.58/0.59  fof(f38,plain,(
% 1.58/0.59    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 1.58/0.59    inference(cnf_transformation,[],[f28])).
% 1.58/0.59  fof(f28,plain,(
% 1.58/0.59    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.59    inference(flattening,[],[f27])).
% 1.58/0.59  fof(f27,plain,(
% 1.58/0.59    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.58/0.59    inference(nnf_transformation,[],[f1])).
% 1.58/0.59  fof(f1,axiom,(
% 1.58/0.59    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.58/0.59  fof(f285,plain,(
% 1.58/0.59    ~spl3_34 | spl3_33),
% 1.58/0.59    inference(avatar_split_clause,[],[f279,f275,f282])).
% 1.58/0.59  fof(f275,plain,(
% 1.58/0.59    spl3_33 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.58/0.59  fof(f279,plain,(
% 1.58/0.59    ~m1_subset_1(sK2,k1_zfmisc_1(sK2)) | spl3_33),
% 1.58/0.59    inference(resolution,[],[f277,f113])).
% 1.58/0.59  fof(f113,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.58/0.59    inference(duplicate_literal_removal,[],[f110])).
% 1.58/0.59  fof(f110,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X1,X2)),X0) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.58/0.59    inference(superposition,[],[f105,f47])).
% 1.58/0.59  fof(f47,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.58/0.59    inference(definition_unfolding,[],[f42,f44])).
% 1.58/0.59  fof(f44,plain,(
% 1.58/0.59    ( ! [X0,X1] : (k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f6])).
% 1.58/0.59  fof(f6,axiom,(
% 1.58/0.59    ! [X0,X1] : k1_setfam_1(k2_tarski(X0,X1)) = k3_xboole_0(X0,X1)),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 1.58/0.59  fof(f42,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.58/0.59    inference(cnf_transformation,[],[f20])).
% 1.58/0.59  fof(f20,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.58/0.59    inference(ennf_transformation,[],[f5])).
% 1.58/0.59  fof(f5,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 1.58/0.59  fof(f105,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (r1_tarski(k9_subset_1(X1,X2,X0),X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.58/0.59    inference(resolution,[],[f43,f35])).
% 1.58/0.59  fof(f35,plain,(
% 1.58/0.59    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f26])).
% 1.58/0.59  fof(f43,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.58/0.59    inference(cnf_transformation,[],[f21])).
% 1.58/0.59  fof(f21,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.58/0.59    inference(ennf_transformation,[],[f4])).
% 1.58/0.59  fof(f4,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.58/0.59  fof(f277,plain,(
% 1.58/0.59    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | spl3_33),
% 1.58/0.59    inference(avatar_component_clause,[],[f275])).
% 1.58/0.59  fof(f278,plain,(
% 1.58/0.59    ~spl3_1 | ~spl3_20 | ~spl3_3 | ~spl3_33 | spl3_19),
% 1.58/0.59    inference(avatar_split_clause,[],[f200,f164,f275,f61,f171,f51])).
% 1.58/0.59  fof(f51,plain,(
% 1.58/0.59    spl3_1 <=> l1_pre_topc(sK0)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.58/0.59  fof(f171,plain,(
% 1.58/0.59    spl3_20 <=> m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.58/0.59  fof(f61,plain,(
% 1.58/0.59    spl3_3 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.58/0.59  fof(f164,plain,(
% 1.58/0.59    spl3_19 <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.58/0.59  fof(f200,plain,(
% 1.58/0.59    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_19),
% 1.58/0.59    inference(resolution,[],[f166,f40])).
% 1.58/0.59  fof(f40,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f17])).
% 1.58/0.59  fof(f17,plain,(
% 1.58/0.59    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.58/0.59    inference(flattening,[],[f16])).
% 1.58/0.59  fof(f16,plain,(
% 1.58/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.58/0.59    inference(ennf_transformation,[],[f9])).
% 1.58/0.59  fof(f9,axiom,(
% 1.58/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_pre_topc)).
% 1.58/0.59  fof(f166,plain,(
% 1.58/0.59    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) | spl3_19),
% 1.58/0.59    inference(avatar_component_clause,[],[f164])).
% 1.58/0.59  fof(f185,plain,(
% 1.58/0.59    spl3_21),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f183])).
% 1.58/0.59  fof(f183,plain,(
% 1.58/0.59    $false | spl3_21),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f48,f177,f46])).
% 1.58/0.59  fof(f46,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X2)),X1) | ~r1_tarski(X0,X1)) )),
% 1.58/0.59    inference(definition_unfolding,[],[f34,f44])).
% 1.58/0.59  fof(f34,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f15])).
% 1.58/0.59  fof(f15,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (r1_tarski(k3_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 1.58/0.59    inference(ennf_transformation,[],[f2])).
% 1.58/0.59  fof(f2,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k3_xboole_0(X0,X2),X1))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).
% 1.58/0.59  fof(f177,plain,(
% 1.58/0.59    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) | spl3_21),
% 1.58/0.59    inference(avatar_component_clause,[],[f175])).
% 1.58/0.59  fof(f175,plain,(
% 1.58/0.59    spl3_21 <=> r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1)),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.58/0.59  fof(f182,plain,(
% 1.58/0.59    ~spl3_3 | spl3_20),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f179])).
% 1.58/0.59  fof(f179,plain,(
% 1.58/0.59    $false | (~spl3_3 | spl3_20)),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f63,f173,f112])).
% 1.58/0.59  fof(f112,plain,(
% 1.58/0.59    ( ! [X4,X5,X3] : (m1_subset_1(k1_setfam_1(k2_tarski(X4,X5)),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 1.58/0.59    inference(duplicate_literal_removal,[],[f111])).
% 1.58/0.59  fof(f111,plain,(
% 1.58/0.59    ( ! [X4,X5,X3] : (m1_subset_1(k1_setfam_1(k2_tarski(X4,X5)),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 1.58/0.59    inference(superposition,[],[f43,f47])).
% 1.58/0.59  fof(f173,plain,(
% 1.58/0.59    ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 1.58/0.59    inference(avatar_component_clause,[],[f171])).
% 1.58/0.59  fof(f63,plain,(
% 1.58/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 1.58/0.59    inference(avatar_component_clause,[],[f61])).
% 1.58/0.59  fof(f178,plain,(
% 1.58/0.59    ~spl3_1 | ~spl3_20 | ~spl3_2 | ~spl3_21 | spl3_18),
% 1.58/0.59    inference(avatar_split_clause,[],[f169,f160,f175,f56,f171,f51])).
% 1.58/0.59  fof(f56,plain,(
% 1.58/0.59    spl3_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.58/0.59  fof(f160,plain,(
% 1.58/0.59    spl3_18 <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.58/0.59  fof(f169,plain,(
% 1.58/0.59    ~r1_tarski(k1_setfam_1(k2_tarski(sK1,sK2)),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(k1_setfam_1(k2_tarski(sK1,sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_18),
% 1.58/0.59    inference(resolution,[],[f162,f40])).
% 1.58/0.59  fof(f162,plain,(
% 1.58/0.59    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) | spl3_18),
% 1.58/0.59    inference(avatar_component_clause,[],[f160])).
% 1.58/0.59  fof(f167,plain,(
% 1.58/0.59    ~spl3_18 | ~spl3_19 | spl3_13),
% 1.58/0.59    inference(avatar_split_clause,[],[f156,f126,f164,f160])).
% 1.58/0.59  fof(f126,plain,(
% 1.58/0.59    spl3_13 <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.58/0.59  fof(f156,plain,(
% 1.58/0.59    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK2)) | ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k2_pre_topc(sK0,sK1)) | spl3_13),
% 1.58/0.59    inference(resolution,[],[f128,f45])).
% 1.58/0.59  fof(f45,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k1_setfam_1(k2_tarski(X1,X2))) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.58/0.59    inference(definition_unfolding,[],[f33,f44])).
% 1.58/0.59  fof(f33,plain,(
% 1.58/0.59    ( ! [X2,X0,X1] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f14])).
% 1.58/0.59  fof(f14,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | ~r1_tarski(X0,X2) | ~r1_tarski(X0,X1))),
% 1.58/0.59    inference(flattening,[],[f13])).
% 1.58/0.59  fof(f13,plain,(
% 1.58/0.59    ! [X0,X1,X2] : (r1_tarski(X0,k3_xboole_0(X1,X2)) | (~r1_tarski(X0,X2) | ~r1_tarski(X0,X1)))),
% 1.58/0.59    inference(ennf_transformation,[],[f3])).
% 1.58/0.59  fof(f3,axiom,(
% 1.58/0.59    ! [X0,X1,X2] : ((r1_tarski(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k3_xboole_0(X1,X2)))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).
% 1.58/0.59  fof(f128,plain,(
% 1.58/0.59    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) | spl3_13),
% 1.58/0.59    inference(avatar_component_clause,[],[f126])).
% 1.58/0.59  fof(f133,plain,(
% 1.58/0.59    ~spl3_1 | ~spl3_3 | spl3_12),
% 1.58/0.59    inference(avatar_contradiction_clause,[],[f130])).
% 1.58/0.59  fof(f130,plain,(
% 1.58/0.59    $false | (~spl3_1 | ~spl3_3 | spl3_12)),
% 1.58/0.59    inference(unit_resulting_resolution,[],[f53,f63,f124,f41])).
% 1.58/0.59  fof(f41,plain,(
% 1.58/0.59    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 1.58/0.59    inference(cnf_transformation,[],[f19])).
% 1.58/0.59  fof(f19,plain,(
% 1.58/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.58/0.59    inference(flattening,[],[f18])).
% 1.58/0.59  fof(f18,plain,(
% 1.58/0.59    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 1.58/0.59    inference(ennf_transformation,[],[f8])).
% 1.58/0.59  fof(f8,axiom,(
% 1.58/0.59    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 1.58/0.59  fof(f124,plain,(
% 1.58/0.59    ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_12),
% 1.58/0.59    inference(avatar_component_clause,[],[f122])).
% 1.58/0.59  fof(f122,plain,(
% 1.58/0.59    spl3_12 <=> m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.58/0.59  fof(f53,plain,(
% 1.58/0.59    l1_pre_topc(sK0) | ~spl3_1),
% 1.58/0.59    inference(avatar_component_clause,[],[f51])).
% 1.58/0.59  fof(f129,plain,(
% 1.58/0.59    ~spl3_12 | ~spl3_13 | spl3_11),
% 1.58/0.59    inference(avatar_split_clause,[],[f120,f116,f126,f122])).
% 1.58/0.59  fof(f116,plain,(
% 1.58/0.59    spl3_11 <=> r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.58/0.59  fof(f120,plain,(
% 1.58/0.59    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k1_setfam_1(k2_tarski(k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))) | ~m1_subset_1(k2_pre_topc(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 1.58/0.59    inference(superposition,[],[f118,f47])).
% 1.58/0.59  fof(f118,plain,(
% 1.58/0.59    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | spl3_11),
% 1.58/0.59    inference(avatar_component_clause,[],[f116])).
% 1.58/0.59  fof(f119,plain,(
% 1.58/0.59    ~spl3_3 | ~spl3_11 | spl3_4),
% 1.58/0.59    inference(avatar_split_clause,[],[f108,f66,f116,f61])).
% 1.58/0.59  fof(f66,plain,(
% 1.58/0.59    spl3_4 <=> r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 1.58/0.59    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.58/0.59  fof(f108,plain,(
% 1.58/0.59    ~r1_tarski(k2_pre_topc(sK0,k1_setfam_1(k2_tarski(sK1,sK2))),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_4),
% 1.58/0.59    inference(superposition,[],[f68,f47])).
% 1.58/0.59  fof(f68,plain,(
% 1.58/0.59    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) | spl3_4),
% 1.58/0.59    inference(avatar_component_clause,[],[f66])).
% 1.58/0.59  fof(f69,plain,(
% 1.58/0.59    ~spl3_4),
% 1.58/0.59    inference(avatar_split_clause,[],[f32,f66])).
% 1.58/0.59  fof(f32,plain,(
% 1.58/0.59    ~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2)))),
% 1.58/0.59    inference(cnf_transformation,[],[f25])).
% 1.58/0.59  fof(f25,plain,(
% 1.58/0.59    ((~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0)),
% 1.58/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f12,f24,f23,f22])).
% 1.58/0.59  fof(f22,plain,(
% 1.58/0.59    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0))),
% 1.58/0.59    introduced(choice_axiom,[])).
% 1.58/0.59  fof(f23,plain,(
% 1.58/0.59    ? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),X1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.58/0.59    introduced(choice_axiom,[])).
% 1.58/0.59  fof(f24,plain,(
% 1.58/0.59    ? [X2] : (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,X2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~r1_tarski(k2_pre_topc(sK0,k9_subset_1(u1_struct_0(sK0),sK1,sK2)),k9_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k2_pre_topc(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.58/0.59    introduced(choice_axiom,[])).
% 1.58/0.59  fof(f12,plain,(
% 1.58/0.59    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 1.58/0.59    inference(ennf_transformation,[],[f11])).
% 1.58/0.59  fof(f11,negated_conjecture,(
% 1.58/0.59    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.58/0.59    inference(negated_conjecture,[],[f10])).
% 1.58/0.59  fof(f10,conjecture,(
% 1.58/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k2_pre_topc(X0,k9_subset_1(u1_struct_0(X0),X1,X2)),k9_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k2_pre_topc(X0,X2))))))),
% 1.58/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_pre_topc)).
% 1.58/0.59  fof(f64,plain,(
% 1.58/0.59    spl3_3),
% 1.58/0.59    inference(avatar_split_clause,[],[f31,f61])).
% 1.58/0.59  fof(f31,plain,(
% 1.58/0.59    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.58/0.59    inference(cnf_transformation,[],[f25])).
% 1.58/0.59  fof(f59,plain,(
% 1.58/0.59    spl3_2),
% 1.58/0.59    inference(avatar_split_clause,[],[f30,f56])).
% 1.58/0.59  fof(f30,plain,(
% 1.58/0.59    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.58/0.59    inference(cnf_transformation,[],[f25])).
% 1.58/0.59  fof(f54,plain,(
% 1.58/0.59    spl3_1),
% 1.58/0.59    inference(avatar_split_clause,[],[f29,f51])).
% 1.58/0.59  fof(f29,plain,(
% 1.58/0.59    l1_pre_topc(sK0)),
% 1.58/0.59    inference(cnf_transformation,[],[f25])).
% 1.58/0.59  % SZS output end Proof for theBenchmark
% 1.58/0.59  % (15365)------------------------------
% 1.58/0.59  % (15365)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.58/0.59  % (15365)Termination reason: Refutation
% 1.58/0.59  
% 1.58/0.59  % (15365)Memory used [KB]: 10874
% 1.58/0.59  % (15365)Time elapsed: 0.114 s
% 1.58/0.59  % (15365)------------------------------
% 1.58/0.59  % (15365)------------------------------
% 1.58/0.59  % (15337)Success in time 0.228 s
%------------------------------------------------------------------------------
