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
% DateTime   : Thu Dec  3 13:11:12 EST 2020

% Result     : Theorem 3.95s
% Output     : Refutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  112 ( 232 expanded)
%              Number of leaves         :   26 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  275 ( 577 expanded)
%              Number of equality atoms :   14 (  61 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f155,f157,f330,f408,f421,f607,f637,f881,f926,f3138,f3161])).

fof(f3161,plain,
    ( ~ spl3_5
    | spl3_22
    | ~ spl3_186 ),
    inference(avatar_contradiction_clause,[],[f3150])).

fof(f3150,plain,
    ( $false
    | ~ spl3_5
    | spl3_22
    | ~ spl3_186 ),
    inference(unit_resulting_resolution,[],[f145,f407,f3137,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X2,X1)
      | r1_xboole_0(X2,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f48,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k2_xboole_0(X0,X1) = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k2_xboole_0(X0,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f3137,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2)
    | ~ spl3_186 ),
    inference(avatar_component_clause,[],[f3135])).

fof(f3135,plain,
    ( spl3_186
  <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_186])])).

fof(f407,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f405])).

fof(f405,plain,
    ( spl3_22
  <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f145,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl3_5
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f3138,plain,
    ( ~ spl3_14
    | spl3_186
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f3125,f848,f3135,f312])).

fof(f312,plain,
    ( spl3_14
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f848,plain,
    ( spl3_63
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f3125,plain,
    ( r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_63 ),
    inference(resolution,[],[f850,f221])).

fof(f221,plain,(
    ! [X10,X8,X11,X9] :
      ( ~ r1_tarski(X11,k7_subset_1(X10,X8,X9))
      | r1_xboole_0(X11,X9)
      | ~ m1_subset_1(X8,k1_zfmisc_1(X10)) ) ),
    inference(superposition,[],[f91,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f52,f56])).

fof(f56,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))) ),
    inference(definition_unfolding,[],[f41,f40])).

fof(f40,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f41,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))
      | r1_xboole_0(X0,X2) ) ),
    inference(resolution,[],[f53,f57])).

fof(f57,plain,(
    ! [X0,X1] : r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1) ),
    inference(definition_unfolding,[],[f39,f56])).

fof(f39,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( r1_xboole_0(X0,X2)
      | ~ r1_xboole_0(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_xboole_0(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

fof(f850,plain,
    ( r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f848])).

fof(f926,plain,
    ( spl3_63
    | ~ spl3_6
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f920,f604,f147,f848])).

fof(f147,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f604,plain,
    ( spl3_39
  <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f920,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_39 ),
    inference(resolution,[],[f605,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f605,plain,
    ( m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f604])).

fof(f881,plain,(
    spl3_39 ),
    inference(avatar_contradiction_clause,[],[f869])).

fof(f869,plain,
    ( $false
    | spl3_39 ),
    inference(unit_resulting_resolution,[],[f64,f34,f857,f222])).

fof(f222,plain,(
    ! [X14,X12,X15,X13] :
      ( r1_tarski(k7_subset_1(X14,X12,X13),X15)
      | ~ r1_tarski(X12,X15)
      | ~ m1_subset_1(X12,k1_zfmisc_1(X14)) ) ),
    inference(superposition,[],[f58,f59])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f51,f56])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X2),X1)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X1)
     => r1_tarski(k4_xboole_0(X0,X2),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).

fof(f857,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0))
    | spl3_39 ),
    inference(resolution,[],[f606,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f606,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_39 ),
    inference(avatar_component_clause,[],[f604])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).

fof(f64,plain,(
    r1_tarski(sK1,u1_struct_0(sK0)) ),
    inference(resolution,[],[f47,f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f637,plain,(
    spl3_38 ),
    inference(avatar_contradiction_clause,[],[f633])).

fof(f633,plain,
    ( $false
    | spl3_38 ),
    inference(unit_resulting_resolution,[],[f61,f34,f602,f222])).

fof(f602,plain,
    ( ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | spl3_38 ),
    inference(avatar_component_clause,[],[f600])).

fof(f600,plain,
    ( spl3_38
  <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f61,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f607,plain,
    ( ~ spl3_6
    | ~ spl3_38
    | ~ spl3_14
    | ~ spl3_39
    | spl3_21 ),
    inference(avatar_split_clause,[],[f596,f401,f604,f312,f600,f147])).

fof(f401,plain,
    ( spl3_21
  <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f596,plain,
    ( ~ m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)
    | ~ l1_pre_topc(sK0)
    | spl3_21 ),
    inference(resolution,[],[f403,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f403,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f401])).

fof(f421,plain,
    ( ~ spl3_7
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f413])).

fof(f413,plain,
    ( $false
    | ~ spl3_7
    | spl3_20 ),
    inference(unit_resulting_resolution,[],[f64,f154,f409,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f409,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0))
    | spl3_20 ),
    inference(resolution,[],[f399,f46])).

fof(f399,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f397])).

fof(f397,plain,
    ( spl3_20
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f154,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f152])).

fof(f152,plain,
    ( spl3_7
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f408,plain,
    ( ~ spl3_20
    | ~ spl3_21
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f392,f405,f401,f397])).

fof(f392,plain,
    ( ~ r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))
    | ~ m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f219,f33])).

fof(f33,plain,(
    ~ r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2))) ),
    inference(cnf_transformation,[],[f18])).

fof(f219,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(X3,k7_subset_1(X2,X0,X1))
      | ~ r1_xboole_0(X3,X1)
      | ~ r1_tarski(X3,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f60,f59])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f54,f56])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_xboole_0(X0,X2)
      | r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k4_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_xboole_0(X0,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,k4_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

fof(f330,plain,(
    spl3_14 ),
    inference(avatar_contradiction_clause,[],[f326])).

fof(f326,plain,
    ( $false
    | spl3_14 ),
    inference(subsumption_resolution,[],[f34,f314])).

fof(f314,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f312])).

fof(f157,plain,(
    spl3_6 ),
    inference(avatar_contradiction_clause,[],[f156])).

fof(f156,plain,
    ( $false
    | spl3_6 ),
    inference(subsumption_resolution,[],[f36,f149])).

fof(f149,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_6 ),
    inference(avatar_component_clause,[],[f147])).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f155,plain,
    ( spl3_7
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f140,f147,f152])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    inference(resolution,[],[f37,f34])).

fof(f150,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f139,f147,f143])).

fof(f139,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    inference(resolution,[],[f37,f32])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 13:26:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.49/0.56  % (27203)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.49/0.56  % (27219)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.49/0.56  % (27210)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.49/0.56  % (27211)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.49/0.57  % (27199)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.49/0.57  % (27198)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.49/0.57  % (27196)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.63/0.57  % (27200)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.58  % (27202)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.63/0.58  % (27195)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.63/0.58  % (27218)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.63/0.59  % (27194)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.63/0.59  % (27197)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 1.63/0.59  % (27217)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.63/0.59  % (27222)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.63/0.59  % (27209)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.63/0.60  % (27223)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.63/0.60  % (27214)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.63/0.60  % (27212)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 1.63/0.60  % (27213)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.63/0.61  % (27201)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.63/0.61  % (27216)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 1.63/0.61  % (27215)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.63/0.61  % (27206)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.63/0.61  % (27205)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.63/0.61  % (27204)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.63/0.61  % (27220)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.63/0.62  % (27207)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.63/0.62  % (27208)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.63/0.62  % (27221)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 3.06/0.82  % (27218)Time limit reached!
% 3.06/0.82  % (27218)------------------------------
% 3.06/0.82  % (27218)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.83  % (27218)Termination reason: Time limit
% 3.61/0.83  % (27218)Termination phase: Saturation
% 3.61/0.83  
% 3.61/0.83  % (27218)Memory used [KB]: 12025
% 3.61/0.83  % (27218)Time elapsed: 0.400 s
% 3.61/0.83  % (27218)------------------------------
% 3.61/0.83  % (27218)------------------------------
% 3.61/0.85  % (27196)Time limit reached!
% 3.61/0.85  % (27196)------------------------------
% 3.61/0.85  % (27196)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.85  % (27196)Termination reason: Time limit
% 3.61/0.85  
% 3.61/0.85  % (27196)Memory used [KB]: 6524
% 3.61/0.85  % (27196)Time elapsed: 0.423 s
% 3.61/0.85  % (27196)------------------------------
% 3.61/0.85  % (27196)------------------------------
% 3.95/0.89  % (27207)Refutation found. Thanks to Tanya!
% 3.95/0.89  % SZS status Theorem for theBenchmark
% 3.95/0.89  % SZS output start Proof for theBenchmark
% 3.95/0.89  fof(f3162,plain,(
% 3.95/0.89    $false),
% 3.95/0.89    inference(avatar_sat_refutation,[],[f150,f155,f157,f330,f408,f421,f607,f637,f881,f926,f3138,f3161])).
% 3.95/0.89  fof(f3161,plain,(
% 3.95/0.89    ~spl3_5 | spl3_22 | ~spl3_186),
% 3.95/0.89    inference(avatar_contradiction_clause,[],[f3150])).
% 3.95/0.89  fof(f3150,plain,(
% 3.95/0.89    $false | (~spl3_5 | spl3_22 | ~spl3_186)),
% 3.95/0.89    inference(unit_resulting_resolution,[],[f145,f407,f3137,f66])).
% 3.95/0.89  fof(f66,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (~r1_xboole_0(X2,X1) | r1_xboole_0(X2,X0) | ~r1_tarski(X0,X1)) )),
% 3.95/0.89    inference(superposition,[],[f48,f42])).
% 3.95/0.89  fof(f42,plain,(
% 3.95/0.89    ( ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f22])).
% 3.95/0.89  fof(f22,plain,(
% 3.95/0.89    ! [X0,X1] : (k2_xboole_0(X0,X1) = X1 | ~r1_tarski(X0,X1))),
% 3.95/0.89    inference(ennf_transformation,[],[f4])).
% 3.95/0.89  fof(f4,axiom,(
% 3.95/0.89    ! [X0,X1] : (r1_tarski(X0,X1) => k2_xboole_0(X0,X1) = X1)),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).
% 3.95/0.89  fof(f48,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f23])).
% 3.95/0.89  fof(f23,plain,(
% 3.95/0.89    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.95/0.89    inference(ennf_transformation,[],[f7])).
% 3.95/0.89  fof(f7,axiom,(
% 3.95/0.89    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 3.95/0.89  fof(f3137,plain,(
% 3.95/0.89    r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2) | ~spl3_186),
% 3.95/0.89    inference(avatar_component_clause,[],[f3135])).
% 3.95/0.89  fof(f3135,plain,(
% 3.95/0.89    spl3_186 <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2)),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_186])])).
% 3.95/0.89  fof(f407,plain,(
% 3.95/0.89    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | spl3_22),
% 3.95/0.89    inference(avatar_component_clause,[],[f405])).
% 3.95/0.89  fof(f405,plain,(
% 3.95/0.89    spl3_22 <=> r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2))),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 3.95/0.89  fof(f145,plain,(
% 3.95/0.89    r1_tarski(k1_tops_1(sK0,sK2),sK2) | ~spl3_5),
% 3.95/0.89    inference(avatar_component_clause,[],[f143])).
% 3.95/0.89  fof(f143,plain,(
% 3.95/0.89    spl3_5 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.95/0.89  fof(f3138,plain,(
% 3.95/0.89    ~spl3_14 | spl3_186 | ~spl3_63),
% 3.95/0.89    inference(avatar_split_clause,[],[f3125,f848,f3135,f312])).
% 3.95/0.89  fof(f312,plain,(
% 3.95/0.89    spl3_14 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 3.95/0.89  fof(f848,plain,(
% 3.95/0.89    spl3_63 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 3.95/0.89  fof(f3125,plain,(
% 3.95/0.89    r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),sK2) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_63),
% 3.95/0.89    inference(resolution,[],[f850,f221])).
% 3.95/0.89  fof(f221,plain,(
% 3.95/0.89    ( ! [X10,X8,X11,X9] : (~r1_tarski(X11,k7_subset_1(X10,X8,X9)) | r1_xboole_0(X11,X9) | ~m1_subset_1(X8,k1_zfmisc_1(X10))) )),
% 3.95/0.89    inference(superposition,[],[f91,f59])).
% 3.95/0.89  fof(f59,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2))) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.95/0.89    inference(definition_unfolding,[],[f52,f56])).
% 3.95/0.89  fof(f56,plain,(
% 3.95/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1)))) )),
% 3.95/0.89    inference(definition_unfolding,[],[f41,f40])).
% 3.95/0.89  fof(f40,plain,(
% 3.95/0.89    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.95/0.89    inference(cnf_transformation,[],[f11])).
% 3.95/0.89  fof(f11,axiom,(
% 3.95/0.89    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.95/0.89  fof(f41,plain,(
% 3.95/0.89    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.95/0.89    inference(cnf_transformation,[],[f2])).
% 3.95/0.89  fof(f2,axiom,(
% 3.95/0.89    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).
% 3.95/0.89  fof(f52,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f25])).
% 3.95/0.89  fof(f25,plain,(
% 3.95/0.89    ! [X0,X1,X2] : (k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.95/0.89    inference(ennf_transformation,[],[f10])).
% 3.95/0.89  fof(f10,axiom,(
% 3.95/0.89    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X1,X2) = k7_subset_1(X0,X1,X2))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.95/0.89  fof(f91,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) | r1_xboole_0(X0,X2)) )),
% 3.95/0.89    inference(resolution,[],[f53,f57])).
% 3.95/0.89  fof(f57,plain,(
% 3.95/0.89    ( ! [X0,X1] : (r1_xboole_0(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X1))),X1)) )),
% 3.95/0.89    inference(definition_unfolding,[],[f39,f56])).
% 3.95/0.89  fof(f39,plain,(
% 3.95/0.89    ( ! [X0,X1] : (r1_xboole_0(k4_xboole_0(X0,X1),X1)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f8])).
% 3.95/0.89  fof(f8,axiom,(
% 3.95/0.89    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1)),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).
% 3.95/0.89  fof(f53,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1) | r1_xboole_0(X0,X2)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f27])).
% 3.95/0.89  fof(f27,plain,(
% 3.95/0.89    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | ~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1))),
% 3.95/0.89    inference(flattening,[],[f26])).
% 3.95/0.89  fof(f26,plain,(
% 3.95/0.89    ! [X0,X1,X2] : (r1_xboole_0(X0,X2) | (~r1_xboole_0(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.95/0.89    inference(ennf_transformation,[],[f6])).
% 3.95/0.89  fof(f6,axiom,(
% 3.95/0.89    ! [X0,X1,X2] : ((r1_xboole_0(X1,X2) & r1_tarski(X0,X1)) => r1_xboole_0(X0,X2))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).
% 3.95/0.89  fof(f850,plain,(
% 3.95/0.89    r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~spl3_63),
% 3.95/0.89    inference(avatar_component_clause,[],[f848])).
% 3.95/0.89  fof(f926,plain,(
% 3.95/0.89    spl3_63 | ~spl3_6 | ~spl3_39),
% 3.95/0.89    inference(avatar_split_clause,[],[f920,f604,f147,f848])).
% 3.95/0.89  fof(f147,plain,(
% 3.95/0.89    spl3_6 <=> l1_pre_topc(sK0)),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 3.95/0.89  fof(f604,plain,(
% 3.95/0.89    spl3_39 <=> m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 3.95/0.89  fof(f920,plain,(
% 3.95/0.89    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~spl3_39),
% 3.95/0.89    inference(resolution,[],[f605,f37])).
% 3.95/0.89  fof(f37,plain,(
% 3.95/0.89    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f19])).
% 3.95/0.89  fof(f19,plain,(
% 3.95/0.89    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/0.89    inference(ennf_transformation,[],[f13])).
% 3.95/0.89  fof(f13,axiom,(
% 3.95/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 3.95/0.89  fof(f605,plain,(
% 3.95/0.89    m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_39),
% 3.95/0.89    inference(avatar_component_clause,[],[f604])).
% 3.95/0.89  fof(f881,plain,(
% 3.95/0.89    spl3_39),
% 3.95/0.89    inference(avatar_contradiction_clause,[],[f869])).
% 3.95/0.89  fof(f869,plain,(
% 3.95/0.89    $false | spl3_39),
% 3.95/0.89    inference(unit_resulting_resolution,[],[f64,f34,f857,f222])).
% 3.95/0.89  fof(f222,plain,(
% 3.95/0.89    ( ! [X14,X12,X15,X13] : (r1_tarski(k7_subset_1(X14,X12,X13),X15) | ~r1_tarski(X12,X15) | ~m1_subset_1(X12,k1_zfmisc_1(X14))) )),
% 3.95/0.89    inference(superposition,[],[f58,f59])).
% 3.95/0.89  fof(f58,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (r1_tarski(k5_xboole_0(X0,k1_setfam_1(k2_tarski(X0,X2))),X1) | ~r1_tarski(X0,X1)) )),
% 3.95/0.89    inference(definition_unfolding,[],[f51,f56])).
% 3.95/0.89  fof(f51,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | r1_tarski(k4_xboole_0(X0,X2),X1)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f24])).
% 3.95/0.89  fof(f24,plain,(
% 3.95/0.89    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X2),X1) | ~r1_tarski(X0,X1))),
% 3.95/0.89    inference(ennf_transformation,[],[f3])).
% 3.95/0.89  fof(f3,axiom,(
% 3.95/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X1) => r1_tarski(k4_xboole_0(X0,X2),X1))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_xboole_1)).
% 3.95/0.89  fof(f857,plain,(
% 3.95/0.89    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),u1_struct_0(sK0)) | spl3_39),
% 3.95/0.89    inference(resolution,[],[f606,f46])).
% 3.95/0.89  fof(f46,plain,(
% 3.95/0.89    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f12])).
% 3.95/0.89  fof(f12,axiom,(
% 3.95/0.89    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.95/0.89  fof(f606,plain,(
% 3.95/0.89    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_39),
% 3.95/0.89    inference(avatar_component_clause,[],[f604])).
% 3.95/0.89  fof(f34,plain,(
% 3.95/0.89    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.95/0.89    inference(cnf_transformation,[],[f18])).
% 3.95/0.89  fof(f18,plain,(
% 3.95/0.89    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.95/0.89    inference(flattening,[],[f17])).
% 3.95/0.89  fof(f17,plain,(
% 3.95/0.89    ? [X0] : (? [X1] : (? [X2] : (~r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.95/0.89    inference(ennf_transformation,[],[f16])).
% 3.95/0.89  fof(f16,negated_conjecture,(
% 3.95/0.89    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.95/0.89    inference(negated_conjecture,[],[f15])).
% 3.95/0.89  fof(f15,conjecture,(
% 3.95/0.89    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,k7_subset_1(u1_struct_0(X0),X1,X2)),k7_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tops_1)).
% 3.95/0.89  fof(f64,plain,(
% 3.95/0.89    r1_tarski(sK1,u1_struct_0(sK0))),
% 3.95/0.89    inference(resolution,[],[f47,f34])).
% 3.95/0.89  fof(f47,plain,(
% 3.95/0.89    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f12])).
% 3.95/0.89  fof(f637,plain,(
% 3.95/0.89    spl3_38),
% 3.95/0.89    inference(avatar_contradiction_clause,[],[f633])).
% 3.95/0.89  fof(f633,plain,(
% 3.95/0.89    $false | spl3_38),
% 3.95/0.89    inference(unit_resulting_resolution,[],[f61,f34,f602,f222])).
% 3.95/0.89  fof(f602,plain,(
% 3.95/0.89    ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | spl3_38),
% 3.95/0.89    inference(avatar_component_clause,[],[f600])).
% 3.95/0.89  fof(f600,plain,(
% 3.95/0.89    spl3_38 <=> r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1)),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 3.95/0.89  fof(f61,plain,(
% 3.95/0.89    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.95/0.89    inference(equality_resolution,[],[f44])).
% 3.95/0.89  fof(f44,plain,(
% 3.95/0.89    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.95/0.89    inference(cnf_transformation,[],[f1])).
% 3.95/0.89  fof(f1,axiom,(
% 3.95/0.89    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.95/0.89  fof(f607,plain,(
% 3.95/0.89    ~spl3_6 | ~spl3_38 | ~spl3_14 | ~spl3_39 | spl3_21),
% 3.95/0.89    inference(avatar_split_clause,[],[f596,f401,f604,f312,f600,f147])).
% 3.95/0.89  fof(f401,plain,(
% 3.95/0.89    spl3_21 <=> r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1))),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 3.95/0.89  fof(f596,plain,(
% 3.95/0.89    ~m1_subset_1(k7_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(k7_subset_1(u1_struct_0(sK0),sK1,sK2),sK1) | ~l1_pre_topc(sK0) | spl3_21),
% 3.95/0.89    inference(resolution,[],[f403,f38])).
% 3.95/0.89  fof(f38,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~l1_pre_topc(X0)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f21])).
% 3.95/0.89  fof(f21,plain,(
% 3.95/0.89    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/0.89    inference(flattening,[],[f20])).
% 3.95/0.89  fof(f20,plain,(
% 3.95/0.89    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.95/0.89    inference(ennf_transformation,[],[f14])).
% 3.95/0.89  fof(f14,axiom,(
% 3.95/0.89    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 3.95/0.89  fof(f403,plain,(
% 3.95/0.89    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | spl3_21),
% 3.95/0.89    inference(avatar_component_clause,[],[f401])).
% 3.95/0.89  fof(f421,plain,(
% 3.95/0.89    ~spl3_7 | spl3_20),
% 3.95/0.89    inference(avatar_contradiction_clause,[],[f413])).
% 3.95/0.89  fof(f413,plain,(
% 3.95/0.89    $false | (~spl3_7 | spl3_20)),
% 3.95/0.89    inference(unit_resulting_resolution,[],[f64,f154,f409,f55])).
% 3.95/0.89  fof(f55,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1) | r1_tarski(X0,X2)) )),
% 3.95/0.89    inference(cnf_transformation,[],[f31])).
% 3.95/0.89  fof(f31,plain,(
% 3.95/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.95/0.89    inference(flattening,[],[f30])).
% 3.95/0.89  fof(f30,plain,(
% 3.95/0.89    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.95/0.89    inference(ennf_transformation,[],[f5])).
% 3.95/0.89  fof(f5,axiom,(
% 3.95/0.89    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.95/0.89  fof(f409,plain,(
% 3.95/0.89    ~r1_tarski(k1_tops_1(sK0,sK1),u1_struct_0(sK0)) | spl3_20),
% 3.95/0.89    inference(resolution,[],[f399,f46])).
% 3.95/0.89  fof(f399,plain,(
% 3.95/0.89    ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_20),
% 3.95/0.89    inference(avatar_component_clause,[],[f397])).
% 3.95/0.89  fof(f397,plain,(
% 3.95/0.89    spl3_20 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 3.95/0.89  fof(f154,plain,(
% 3.95/0.89    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_7),
% 3.95/0.89    inference(avatar_component_clause,[],[f152])).
% 3.95/0.89  fof(f152,plain,(
% 3.95/0.89    spl3_7 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.95/0.89    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 3.95/0.89  fof(f408,plain,(
% 3.95/0.89    ~spl3_20 | ~spl3_21 | ~spl3_22),
% 3.95/0.89    inference(avatar_split_clause,[],[f392,f405,f401,f397])).
% 3.95/0.89  fof(f392,plain,(
% 3.95/0.89    ~r1_xboole_0(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k1_tops_1(sK0,sK1)) | ~m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.95/0.89    inference(resolution,[],[f219,f33])).
% 3.95/0.89  fof(f33,plain,(
% 3.95/0.89    ~r1_tarski(k1_tops_1(sK0,k7_subset_1(u1_struct_0(sK0),sK1,sK2)),k7_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK1),k1_tops_1(sK0,sK2)))),
% 3.95/0.89    inference(cnf_transformation,[],[f18])).
% 3.95/0.89  fof(f219,plain,(
% 3.95/0.89    ( ! [X2,X0,X3,X1] : (r1_tarski(X3,k7_subset_1(X2,X0,X1)) | ~r1_xboole_0(X3,X1) | ~r1_tarski(X3,X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2))) )),
% 3.95/0.89    inference(superposition,[],[f60,f59])).
% 3.95/0.89  fof(f60,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (r1_tarski(X0,k5_xboole_0(X1,k1_setfam_1(k2_tarski(X1,X2)))) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.95/0.89    inference(definition_unfolding,[],[f54,f56])).
% 3.95/0.89  fof(f54,plain,(
% 3.95/0.89    ( ! [X2,X0,X1] : (~r1_tarski(X0,X1) | ~r1_xboole_0(X0,X2) | r1_tarski(X0,k4_xboole_0(X1,X2))) )),
% 3.95/0.89    inference(cnf_transformation,[],[f29])).
% 3.95/0.89  fof(f29,plain,(
% 3.95/0.89    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1))),
% 3.95/0.89    inference(flattening,[],[f28])).
% 3.95/0.89  fof(f28,plain,(
% 3.95/0.89    ! [X0,X1,X2] : (r1_tarski(X0,k4_xboole_0(X1,X2)) | (~r1_xboole_0(X0,X2) | ~r1_tarski(X0,X1)))),
% 3.95/0.89    inference(ennf_transformation,[],[f9])).
% 3.95/0.89  fof(f9,axiom,(
% 3.95/0.89    ! [X0,X1,X2] : ((r1_xboole_0(X0,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,k4_xboole_0(X1,X2)))),
% 3.95/0.89    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).
% 3.95/0.89  fof(f330,plain,(
% 3.95/0.89    spl3_14),
% 3.95/0.89    inference(avatar_contradiction_clause,[],[f326])).
% 3.95/0.89  fof(f326,plain,(
% 3.95/0.89    $false | spl3_14),
% 3.95/0.89    inference(subsumption_resolution,[],[f34,f314])).
% 3.95/0.89  fof(f314,plain,(
% 3.95/0.89    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl3_14),
% 3.95/0.89    inference(avatar_component_clause,[],[f312])).
% 3.95/0.89  fof(f157,plain,(
% 3.95/0.89    spl3_6),
% 3.95/0.89    inference(avatar_contradiction_clause,[],[f156])).
% 3.95/0.89  fof(f156,plain,(
% 3.95/0.89    $false | spl3_6),
% 3.95/0.89    inference(subsumption_resolution,[],[f36,f149])).
% 3.95/0.89  fof(f149,plain,(
% 3.95/0.89    ~l1_pre_topc(sK0) | spl3_6),
% 3.95/0.89    inference(avatar_component_clause,[],[f147])).
% 3.95/0.89  fof(f36,plain,(
% 3.95/0.89    l1_pre_topc(sK0)),
% 3.95/0.89    inference(cnf_transformation,[],[f18])).
% 3.95/0.89  fof(f155,plain,(
% 3.95/0.89    spl3_7 | ~spl3_6),
% 3.95/0.89    inference(avatar_split_clause,[],[f140,f147,f152])).
% 3.95/0.89  fof(f140,plain,(
% 3.95/0.89    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.95/0.89    inference(resolution,[],[f37,f34])).
% 3.95/0.89  fof(f150,plain,(
% 3.95/0.89    spl3_5 | ~spl3_6),
% 3.95/0.89    inference(avatar_split_clause,[],[f139,f147,f143])).
% 3.95/0.89  fof(f139,plain,(
% 3.95/0.89    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 3.95/0.89    inference(resolution,[],[f37,f32])).
% 3.95/0.89  fof(f32,plain,(
% 3.95/0.89    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.95/0.89    inference(cnf_transformation,[],[f18])).
% 3.95/0.89  % SZS output end Proof for theBenchmark
% 3.95/0.89  % (27207)------------------------------
% 3.95/0.89  % (27207)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.95/0.89  % (27207)Termination reason: Refutation
% 3.95/0.89  
% 3.95/0.89  % (27207)Memory used [KB]: 8187
% 3.95/0.89  % (27207)Time elapsed: 0.473 s
% 3.95/0.89  % (27207)------------------------------
% 3.95/0.89  % (27207)------------------------------
% 3.95/0.90  % (27193)Success in time 0.532 s
%------------------------------------------------------------------------------
