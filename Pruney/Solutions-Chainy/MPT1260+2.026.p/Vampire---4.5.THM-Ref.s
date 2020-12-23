%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:37 EST 2020

% Result     : Theorem 3.75s
% Output     : Refutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :  215 ( 400 expanded)
%              Number of leaves         :   47 ( 146 expanded)
%              Depth                    :   13
%              Number of atoms          :  634 (1229 expanded)
%              Number of equality atoms :  112 ( 242 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3835,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f102,f103,f108,f113,f118,f126,f198,f370,f473,f534,f1009,f1019,f1044,f1090,f1095,f1109,f1119,f1151,f1334,f1913,f3395,f3790,f3833])).

fof(f3833,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_41
    | ~ spl3_221 ),
    inference(avatar_contradiction_clause,[],[f3832])).

fof(f3832,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_41
    | ~ spl3_221 ),
    inference(subsumption_resolution,[],[f3831,f112])).

fof(f112,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f3831,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_41
    | ~ spl3_221 ),
    inference(subsumption_resolution,[],[f3830,f107])).

fof(f107,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f105])).

fof(f105,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f3830,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_41
    | ~ spl3_221 ),
    inference(subsumption_resolution,[],[f3811,f542])).

fof(f542,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl3_41 ),
    inference(avatar_component_clause,[],[f541])).

fof(f541,plain,
    ( spl3_41
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f3811,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_221 ),
    inference(superposition,[],[f205,f3787])).

fof(f3787,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_221 ),
    inference(avatar_component_clause,[],[f3785])).

fof(f3785,plain,
    ( spl3_221
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_221])])).

fof(f205,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f204])).

fof(f204,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f64,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f3790,plain,
    ( spl3_221
    | ~ spl3_78
    | ~ spl3_197 ),
    inference(avatar_split_clause,[],[f3789,f3390,f1127,f3785])).

fof(f1127,plain,
    ( spl3_78
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f3390,plain,
    ( spl3_197
  <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_197])])).

fof(f3789,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_78
    | ~ spl3_197 ),
    inference(subsumption_resolution,[],[f3782,f1128])).

fof(f1128,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f3782,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_197 ),
    inference(superposition,[],[f64,f3392])).

fof(f3392,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_197 ),
    inference(avatar_component_clause,[],[f3390])).

fof(f3395,plain,
    ( spl3_197
    | ~ spl3_46
    | ~ spl3_114 ),
    inference(avatar_split_clause,[],[f3394,f1910,f654,f3390])).

fof(f654,plain,
    ( spl3_46
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f1910,plain,
    ( spl3_114
  <=> k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).

fof(f3394,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_46
    | ~ spl3_114 ),
    inference(subsumption_resolution,[],[f3384,f655])).

fof(f655,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f654])).

fof(f3384,plain,
    ( sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_114 ),
    inference(superposition,[],[f1912,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f1912,plain,
    ( k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
    | ~ spl3_114 ),
    inference(avatar_component_clause,[],[f1910])).

fof(f1913,plain,
    ( spl3_86
    | spl3_114
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f1908,f420,f410,f1910,f1280])).

fof(f1280,plain,
    ( spl3_86
  <=> ! [X1] : ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).

fof(f410,plain,
    ( spl3_26
  <=> k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f420,plain,
    ( spl3_28
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1908,plain,
    ( ! [X27] :
        ( k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f1890,f422])).

fof(f422,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f420])).

fof(f1890,plain,
    ( ! [X27] :
        ( k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X27,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_26 ),
    inference(superposition,[],[f511,f412])).

fof(f412,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f410])).

fof(f511,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = k7_subset_1(X0,k4_xboole_0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f508])).

fof(f508,plain,(
    ! [X2,X0,X1] :
      ( k4_xboole_0(X0,X1) = k7_subset_1(X0,k4_xboole_0(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f230,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f230,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f227,f87])).

fof(f87,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f227,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f71,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f1334,plain,(
    ~ spl3_86 ),
    inference(avatar_contradiction_clause,[],[f1303])).

fof(f1303,plain,
    ( $false
    | ~ spl3_86 ),
    inference(unit_resulting_resolution,[],[f128,f79,f1281,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1281,plain,
    ( ! [X1] : ~ m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_86 ),
    inference(avatar_component_clause,[],[f1280])).

fof(f79,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f57])).

fof(f57,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f12,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f128,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f90,f83])).

fof(f83,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f90,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f1151,plain,
    ( ~ spl3_46
    | spl3_78 ),
    inference(avatar_split_clause,[],[f1150,f1127,f654])).

fof(f1150,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_78 ),
    inference(resolution,[],[f1129,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1129,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_78 ),
    inference(avatar_component_clause,[],[f1127])).

fof(f1119,plain,
    ( spl3_26
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f1118,f171,f410])).

fof(f171,plain,
    ( spl3_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f1118,plain,
    ( k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f1110,f162])).

fof(f162,plain,(
    ! [X2,X3] : k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2) ),
    inference(superposition,[],[f131,f85])).

fof(f85,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f131,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0)) ),
    inference(superposition,[],[f85,f91])).

fof(f91,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f1110,plain,
    ( k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_10 ),
    inference(superposition,[],[f69,f173])).

fof(f173,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f171])).

fof(f69,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f1109,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f1108,f167,f99,f171])).

fof(f99,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f167,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1108,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f1105,f168])).

fof(f168,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f1105,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f64,f100])).

fof(f100,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f1095,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1090,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_41 ),
    inference(avatar_contradiction_clause,[],[f1089])).

fof(f1089,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f1088,f112])).

fof(f1088,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_10
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f1087,f107])).

fof(f1087,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f1084,f172])).

fof(f172,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f171])).

fof(f1084,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_41 ),
    inference(superposition,[],[f587,f543])).

fof(f543,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f541])).

fof(f587,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f236,f225])).

fof(f225,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f220,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f220,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f219])).

fof(f219,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f89,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f236,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f72,f64])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1044,plain,
    ( spl3_46
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1043,f110,f105,f654])).

fof(f1043,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f1034,f112])).

fof(f1034,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f495,f107])).

fof(f495,plain,(
    ! [X6,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6)))
      | r1_tarski(X5,k2_pre_topc(X6,X5))
      | ~ l1_pre_topc(X6) ) ),
    inference(superposition,[],[f84,f223])).

fof(f223,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f222,f74])).

fof(f222,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f217])).

fof(f217,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f73,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f84,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1019,plain,
    ( spl3_41
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f1018,f537,f123,f110,f105,f95,f541])).

fof(f95,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f123,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f537,plain,
    ( spl3_40
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f1018,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1017,f92])).

fof(f92,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1017,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f1015,f125])).

fof(f125,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f123])).

fof(f1015,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_40 ),
    inference(resolution,[],[f538,f586])).

fof(f586,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_tops_1(sK0,X0),sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0))
        | sK1 = k1_tops_1(sK0,X0)
        | ~ r1_tarski(sK1,X0) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f573,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f573,plain,
    ( ! [X30] :
        ( r1_tarski(sK1,k1_tops_1(sK0,X30))
        | ~ r1_tarski(sK1,X30)
        | ~ r1_tarski(X30,u1_struct_0(sK0)) )
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f572,f112])).

fof(f572,plain,
    ( ! [X30] :
        ( r1_tarski(sK1,k1_tops_1(sK0,X30))
        | ~ r1_tarski(sK1,X30)
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X30,u1_struct_0(sK0)) )
    | ~ spl3_1
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f563,f96])).

fof(f96,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f95])).

fof(f563,plain,
    ( ! [X30] :
        ( ~ v3_pre_topc(sK1,sK0)
        | r1_tarski(sK1,k1_tops_1(sK0,X30))
        | ~ r1_tarski(sK1,X30)
        | ~ l1_pre_topc(sK0)
        | ~ r1_tarski(X30,u1_struct_0(sK0)) )
    | ~ spl3_3 ),
    inference(resolution,[],[f238,f107])).

fof(f238,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ v3_pre_topc(X0,X2)
      | r1_tarski(X0,k1_tops_1(X2,X1))
      | ~ r1_tarski(X0,X1)
      | ~ l1_pre_topc(X2)
      | ~ r1_tarski(X1,u1_struct_0(X2)) ) ),
    inference(resolution,[],[f76,f78])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).

fof(f538,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f537])).

fof(f1009,plain,
    ( spl3_40
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1008,f110,f105,f537])).

fof(f1008,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f997,f112])).

fof(f997,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f484,f107])).

fof(f484,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7)))
      | r1_tarski(k1_tops_1(X7,X6),X6)
      | ~ l1_pre_topc(X7) ) ),
    inference(superposition,[],[f129,f205])).

fof(f129,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(resolution,[],[f128,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f534,plain,
    ( ~ spl3_10
    | spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f533,f167,f99,f171])).

fof(f533,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f532,f168])).

fof(f532,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f101,f64])).

fof(f101,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f473,plain,
    ( spl3_28
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f466,f171,f420])).

fof(f466,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f128,f173])).

fof(f370,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f369])).

fof(f369,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f368,f112])).

fof(f368,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f360,f107])).

fof(f360,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f225,f169])).

fof(f169,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f167])).

fof(f198,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f193,f115,f110,f105,f195])).

fof(f195,plain,
    ( spl3_12
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f115,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f193,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f192,f117])).

fof(f117,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f115])).

fof(f192,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f189,f112])).

fof(f189,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f75,f107])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f126,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f119,f105,f123])).

fof(f119,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f77,f107])).

fof(f118,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f59,f115])).

fof(f59,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).

fof(f51,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | ~ v3_pre_topc(X1,X0) )
            & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              | v3_pre_topc(X1,X0) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | ~ v3_pre_topc(X1,sK0) )
          & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
            | v3_pre_topc(X1,sK0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( ? [X1] :
        ( ( k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | ~ v3_pre_topc(X1,sK0) )
        & ( k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1)
          | v3_pre_topc(X1,sK0) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | ~ v3_pre_topc(sK1,sK0) )
      & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
        | v3_pre_topc(sK1,sK0) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f26])).

fof(f26,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f113,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f60,f110])).

fof(f60,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f61,f105])).

fof(f61,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f62,f99,f95])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f102,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f63,f99,f95])).

fof(f63,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:30:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (16680)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.50  % (16685)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.51  % (16703)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (16694)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (16678)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (16677)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (16673)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (16676)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.52  % (16674)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (16696)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (16687)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (16686)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (16675)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (16679)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.53  % (16692)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (16690)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (16702)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (16701)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (16691)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (16700)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.54  % (16698)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.37/0.54  % (16684)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.37/0.54  % (16682)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.37/0.54  % (16699)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.37/0.55  % (16693)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.37/0.55  % (16688)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.37/0.55  % (16683)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.37/0.55  % (16681)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.37/0.55  % (16695)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.37/0.55  % (16690)Refutation not found, incomplete strategy% (16690)------------------------------
% 1.37/0.55  % (16690)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.37/0.55  % (16690)Termination reason: Refutation not found, incomplete strategy
% 1.37/0.55  
% 1.37/0.55  % (16690)Memory used [KB]: 10746
% 1.37/0.55  % (16690)Time elapsed: 0.148 s
% 1.37/0.55  % (16690)------------------------------
% 1.37/0.55  % (16690)------------------------------
% 1.54/0.57  % (16697)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.54/0.58  % (16702)Refutation not found, incomplete strategy% (16702)------------------------------
% 1.54/0.58  % (16702)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.54/0.58  % (16702)Termination reason: Refutation not found, incomplete strategy
% 1.54/0.58  
% 1.54/0.58  % (16702)Memory used [KB]: 11129
% 1.54/0.58  % (16702)Time elapsed: 0.169 s
% 1.54/0.58  % (16702)------------------------------
% 1.54/0.58  % (16702)------------------------------
% 2.46/0.71  % (16728)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.88/0.75  % (16729)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 3.05/0.80  % (16698)Time limit reached!
% 3.05/0.80  % (16698)------------------------------
% 3.05/0.80  % (16698)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.05/0.80  % (16698)Termination reason: Time limit
% 3.05/0.80  
% 3.05/0.80  % (16698)Memory used [KB]: 13432
% 3.05/0.80  % (16698)Time elapsed: 0.403 s
% 3.05/0.80  % (16698)------------------------------
% 3.05/0.80  % (16698)------------------------------
% 3.49/0.85  % (16675)Time limit reached!
% 3.49/0.85  % (16675)------------------------------
% 3.49/0.85  % (16675)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.49/0.85  % (16675)Termination reason: Time limit
% 3.49/0.85  
% 3.49/0.85  % (16675)Memory used [KB]: 6780
% 3.49/0.85  % (16675)Time elapsed: 0.425 s
% 3.49/0.85  % (16675)------------------------------
% 3.49/0.85  % (16675)------------------------------
% 3.75/0.89  % (16695)Refutation found. Thanks to Tanya!
% 3.75/0.89  % SZS status Theorem for theBenchmark
% 3.75/0.90  % SZS output start Proof for theBenchmark
% 3.75/0.91  fof(f3835,plain,(
% 3.75/0.91    $false),
% 3.75/0.91    inference(avatar_sat_refutation,[],[f102,f103,f108,f113,f118,f126,f198,f370,f473,f534,f1009,f1019,f1044,f1090,f1095,f1109,f1119,f1151,f1334,f1913,f3395,f3790,f3833])).
% 3.75/0.91  fof(f3833,plain,(
% 3.75/0.91    ~spl3_3 | ~spl3_4 | spl3_41 | ~spl3_221),
% 3.75/0.91    inference(avatar_contradiction_clause,[],[f3832])).
% 3.75/0.91  fof(f3832,plain,(
% 3.75/0.91    $false | (~spl3_3 | ~spl3_4 | spl3_41 | ~spl3_221)),
% 3.75/0.91    inference(subsumption_resolution,[],[f3831,f112])).
% 3.75/0.91  fof(f112,plain,(
% 3.75/0.91    l1_pre_topc(sK0) | ~spl3_4),
% 3.75/0.91    inference(avatar_component_clause,[],[f110])).
% 3.75/0.91  fof(f110,plain,(
% 3.75/0.91    spl3_4 <=> l1_pre_topc(sK0)),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 3.75/0.91  fof(f3831,plain,(
% 3.75/0.91    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_41 | ~spl3_221)),
% 3.75/0.91    inference(subsumption_resolution,[],[f3830,f107])).
% 3.75/0.91  fof(f107,plain,(
% 3.75/0.91    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 3.75/0.91    inference(avatar_component_clause,[],[f105])).
% 3.75/0.91  fof(f105,plain,(
% 3.75/0.91    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.75/0.91  fof(f3830,plain,(
% 3.75/0.91    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_41 | ~spl3_221)),
% 3.75/0.91    inference(subsumption_resolution,[],[f3811,f542])).
% 3.75/0.91  fof(f542,plain,(
% 3.75/0.91    sK1 != k1_tops_1(sK0,sK1) | spl3_41),
% 3.75/0.91    inference(avatar_component_clause,[],[f541])).
% 3.75/0.91  fof(f541,plain,(
% 3.75/0.91    spl3_41 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 3.75/0.91  fof(f3811,plain,(
% 3.75/0.91    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_221),
% 3.75/0.91    inference(superposition,[],[f205,f3787])).
% 3.75/0.91  fof(f3787,plain,(
% 3.75/0.91    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_221),
% 3.75/0.91    inference(avatar_component_clause,[],[f3785])).
% 3.75/0.91  fof(f3785,plain,(
% 3.75/0.91    spl3_221 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_221])])).
% 3.75/0.91  fof(f205,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.75/0.91    inference(duplicate_literal_removal,[],[f204])).
% 3.75/0.91  fof(f204,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.75/0.91    inference(superposition,[],[f64,f70])).
% 3.75/0.91  fof(f70,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f32])).
% 3.75/0.91  fof(f32,plain,(
% 3.75/0.91    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.91    inference(ennf_transformation,[],[f25])).
% 3.75/0.91  fof(f25,axiom,(
% 3.75/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.75/0.91  fof(f64,plain,(
% 3.75/0.91    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f30])).
% 3.75/0.91  fof(f30,plain,(
% 3.75/0.91    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.91    inference(ennf_transformation,[],[f16])).
% 3.75/0.91  fof(f16,axiom,(
% 3.75/0.91    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.75/0.91  fof(f3790,plain,(
% 3.75/0.91    spl3_221 | ~spl3_78 | ~spl3_197),
% 3.75/0.91    inference(avatar_split_clause,[],[f3789,f3390,f1127,f3785])).
% 3.75/0.91  fof(f1127,plain,(
% 3.75/0.91    spl3_78 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 3.75/0.91  fof(f3390,plain,(
% 3.75/0.91    spl3_197 <=> sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_197])])).
% 3.75/0.91  fof(f3789,plain,(
% 3.75/0.91    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | (~spl3_78 | ~spl3_197)),
% 3.75/0.91    inference(subsumption_resolution,[],[f3782,f1128])).
% 3.75/0.91  fof(f1128,plain,(
% 3.75/0.91    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_78),
% 3.75/0.91    inference(avatar_component_clause,[],[f1127])).
% 3.75/0.91  fof(f3782,plain,(
% 3.75/0.91    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_197),
% 3.75/0.91    inference(superposition,[],[f64,f3392])).
% 3.75/0.91  fof(f3392,plain,(
% 3.75/0.91    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~spl3_197),
% 3.75/0.91    inference(avatar_component_clause,[],[f3390])).
% 3.75/0.91  fof(f3395,plain,(
% 3.75/0.91    spl3_197 | ~spl3_46 | ~spl3_114),
% 3.75/0.91    inference(avatar_split_clause,[],[f3394,f1910,f654,f3390])).
% 3.75/0.91  fof(f654,plain,(
% 3.75/0.91    spl3_46 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 3.75/0.91  fof(f1910,plain,(
% 3.75/0.91    spl3_114 <=> k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_114])])).
% 3.75/0.91  fof(f3394,plain,(
% 3.75/0.91    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | (~spl3_46 | ~spl3_114)),
% 3.75/0.91    inference(subsumption_resolution,[],[f3384,f655])).
% 3.75/0.91  fof(f655,plain,(
% 3.75/0.91    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_46),
% 3.75/0.91    inference(avatar_component_clause,[],[f654])).
% 3.75/0.91  fof(f3384,plain,(
% 3.75/0.91    sK1 = k7_subset_1(k2_pre_topc(sK0,sK1),sK1,k2_tops_1(sK0,sK1)) | ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_114),
% 3.75/0.91    inference(superposition,[],[f1912,f68])).
% 3.75/0.91  fof(f68,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f31])).
% 3.75/0.91  fof(f31,plain,(
% 3.75/0.91    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.75/0.91    inference(ennf_transformation,[],[f3])).
% 3.75/0.91  fof(f3,axiom,(
% 3.75/0.91    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).
% 3.75/0.91  fof(f1912,plain,(
% 3.75/0.91    k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~spl3_114),
% 3.75/0.91    inference(avatar_component_clause,[],[f1910])).
% 3.75/0.91  fof(f1913,plain,(
% 3.75/0.91    spl3_86 | spl3_114 | ~spl3_26 | ~spl3_28),
% 3.75/0.91    inference(avatar_split_clause,[],[f1908,f420,f410,f1910,f1280])).
% 3.75/0.91  fof(f1280,plain,(
% 3.75/0.91    spl3_86 <=> ! [X1] : ~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_86])])).
% 3.75/0.91  fof(f410,plain,(
% 3.75/0.91    spl3_26 <=> k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 3.75/0.91  fof(f420,plain,(
% 3.75/0.91    spl3_28 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 3.75/0.91  fof(f1908,plain,(
% 3.75/0.91    ( ! [X27] : (k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~m1_subset_1(X27,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_26 | ~spl3_28)),
% 3.75/0.91    inference(subsumption_resolution,[],[f1890,f422])).
% 3.75/0.91  fof(f422,plain,(
% 3.75/0.91    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_28),
% 3.75/0.91    inference(avatar_component_clause,[],[f420])).
% 3.75/0.91  fof(f1890,plain,(
% 3.75/0.91    ( ! [X27] : (k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) = k7_subset_1(k2_pre_topc(sK0,sK1),k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)),k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X27,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_26),
% 3.75/0.91    inference(superposition,[],[f511,f412])).
% 3.75/0.91  fof(f412,plain,(
% 3.75/0.91    k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_26),
% 3.75/0.91    inference(avatar_component_clause,[],[f410])).
% 3.75/0.91  fof(f511,plain,(
% 3.75/0.91    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,k4_xboole_0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(duplicate_literal_removal,[],[f508])).
% 3.75/0.91  fof(f508,plain,(
% 3.75/0.91    ( ! [X2,X0,X1] : (k4_xboole_0(X0,X1) = k7_subset_1(X0,k4_xboole_0(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(superposition,[],[f230,f80])).
% 3.75/0.91  fof(f80,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f42])).
% 3.75/0.91  fof(f42,plain,(
% 3.75/0.91    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.91    inference(ennf_transformation,[],[f8])).
% 3.75/0.91  fof(f8,axiom,(
% 3.75/0.91    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.75/0.91  fof(f230,plain,(
% 3.75/0.91    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.75/0.91    inference(subsumption_resolution,[],[f227,f87])).
% 3.75/0.91  fof(f87,plain,(
% 3.75/0.91    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f44])).
% 3.75/0.91  fof(f44,plain,(
% 3.75/0.91    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.91    inference(ennf_transformation,[],[f9])).
% 3.75/0.91  fof(f9,axiom,(
% 3.75/0.91    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.75/0.91  fof(f227,plain,(
% 3.75/0.91    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.75/0.91    inference(superposition,[],[f71,f86])).
% 3.75/0.91  fof(f86,plain,(
% 3.75/0.91    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f43])).
% 3.75/0.91  fof(f43,plain,(
% 3.75/0.91    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.75/0.91    inference(ennf_transformation,[],[f13])).
% 3.75/0.91  fof(f13,axiom,(
% 3.75/0.91    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 3.75/0.91  fof(f71,plain,(
% 3.75/0.91    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f33])).
% 3.75/0.91  fof(f33,plain,(
% 3.75/0.91    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.91    inference(ennf_transformation,[],[f17])).
% 3.75/0.91  fof(f17,axiom,(
% 3.75/0.91    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 3.75/0.91  fof(f1334,plain,(
% 3.75/0.91    ~spl3_86),
% 3.75/0.91    inference(avatar_contradiction_clause,[],[f1303])).
% 3.75/0.91  fof(f1303,plain,(
% 3.75/0.91    $false | ~spl3_86),
% 3.75/0.91    inference(unit_resulting_resolution,[],[f128,f79,f1281,f89])).
% 3.75/0.91  fof(f89,plain,(
% 3.75/0.91    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f48])).
% 3.75/0.91  fof(f48,plain,(
% 3.75/0.91    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.91    inference(flattening,[],[f47])).
% 3.75/0.91  fof(f47,plain,(
% 3.75/0.91    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.75/0.91    inference(ennf_transformation,[],[f10])).
% 3.75/0.91  fof(f10,axiom,(
% 3.75/0.91    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.75/0.91  fof(f1281,plain,(
% 3.75/0.91    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_86),
% 3.75/0.91    inference(avatar_component_clause,[],[f1280])).
% 3.75/0.91  fof(f79,plain,(
% 3.75/0.91    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f58])).
% 3.75/0.91  fof(f58,plain,(
% 3.75/0.91    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 3.75/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f12,f57])).
% 3.75/0.91  fof(f57,plain,(
% 3.75/0.91    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 3.75/0.91    introduced(choice_axiom,[])).
% 3.75/0.91  fof(f12,axiom,(
% 3.75/0.91    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 3.75/0.91  fof(f128,plain,(
% 3.75/0.91    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(backward_demodulation,[],[f90,f83])).
% 3.75/0.91  fof(f83,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f15])).
% 3.75/0.91  fof(f15,axiom,(
% 3.75/0.91    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.75/0.91  fof(f90,plain,(
% 3.75/0.91    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f11])).
% 3.75/0.91  fof(f11,axiom,(
% 3.75/0.91    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 3.75/0.91  fof(f1151,plain,(
% 3.75/0.91    ~spl3_46 | spl3_78),
% 3.75/0.91    inference(avatar_split_clause,[],[f1150,f1127,f654])).
% 3.75/0.91  fof(f1150,plain,(
% 3.75/0.91    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_78),
% 3.75/0.91    inference(resolution,[],[f1129,f78])).
% 3.75/0.91  fof(f78,plain,(
% 3.75/0.91    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f56])).
% 3.75/0.91  fof(f56,plain,(
% 3.75/0.91    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.75/0.91    inference(nnf_transformation,[],[f19])).
% 3.75/0.91  fof(f19,axiom,(
% 3.75/0.91    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.75/0.91  fof(f1129,plain,(
% 3.75/0.91    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_78),
% 3.75/0.91    inference(avatar_component_clause,[],[f1127])).
% 3.75/0.91  fof(f1119,plain,(
% 3.75/0.91    spl3_26 | ~spl3_10),
% 3.75/0.91    inference(avatar_split_clause,[],[f1118,f171,f410])).
% 3.75/0.91  fof(f171,plain,(
% 3.75/0.91    spl3_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 3.75/0.91  fof(f1118,plain,(
% 3.75/0.91    k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) = k3_xboole_0(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_10),
% 3.75/0.91    inference(forward_demodulation,[],[f1110,f162])).
% 3.75/0.91  fof(f162,plain,(
% 3.75/0.91    ( ! [X2,X3] : (k3_xboole_0(X2,X3) = k3_xboole_0(X3,X2)) )),
% 3.75/0.91    inference(superposition,[],[f131,f85])).
% 3.75/0.91  fof(f85,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f18])).
% 3.75/0.91  fof(f18,axiom,(
% 3.75/0.91    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 3.75/0.91  fof(f131,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X1,X0))) )),
% 3.75/0.91    inference(superposition,[],[f85,f91])).
% 3.75/0.91  fof(f91,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f7])).
% 3.75/0.91  fof(f7,axiom,(
% 3.75/0.91    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 3.75/0.91  fof(f1110,plain,(
% 3.75/0.91    k3_xboole_0(k2_pre_topc(sK0,sK1),sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_10),
% 3.75/0.91    inference(superposition,[],[f69,f173])).
% 3.75/0.91  fof(f173,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_10),
% 3.75/0.91    inference(avatar_component_clause,[],[f171])).
% 3.75/0.91  fof(f69,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f4])).
% 3.75/0.91  fof(f4,axiom,(
% 3.75/0.91    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 3.75/0.91  fof(f1109,plain,(
% 3.75/0.91    spl3_10 | ~spl3_2 | ~spl3_9),
% 3.75/0.91    inference(avatar_split_clause,[],[f1108,f167,f99,f171])).
% 3.75/0.91  fof(f99,plain,(
% 3.75/0.91    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.75/0.91  fof(f167,plain,(
% 3.75/0.91    spl3_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 3.75/0.91  fof(f1108,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_9)),
% 3.75/0.91    inference(subsumption_resolution,[],[f1105,f168])).
% 3.75/0.91  fof(f168,plain,(
% 3.75/0.91    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 3.75/0.91    inference(avatar_component_clause,[],[f167])).
% 3.75/0.91  fof(f1105,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 3.75/0.91    inference(superposition,[],[f64,f100])).
% 3.75/0.91  fof(f100,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 3.75/0.91    inference(avatar_component_clause,[],[f99])).
% 3.75/0.91  fof(f1095,plain,(
% 3.75/0.91    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.75/0.91    introduced(theory_tautology_sat_conflict,[])).
% 3.75/0.91  fof(f1090,plain,(
% 3.75/0.91    ~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_41),
% 3.75/0.91    inference(avatar_contradiction_clause,[],[f1089])).
% 3.75/0.91  fof(f1089,plain,(
% 3.75/0.91    $false | (~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_41)),
% 3.75/0.91    inference(subsumption_resolution,[],[f1088,f112])).
% 3.75/0.91  fof(f1088,plain,(
% 3.75/0.91    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_10 | ~spl3_41)),
% 3.75/0.91    inference(subsumption_resolution,[],[f1087,f107])).
% 3.75/0.91  fof(f1087,plain,(
% 3.75/0.91    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_10 | ~spl3_41)),
% 3.75/0.91    inference(subsumption_resolution,[],[f1084,f172])).
% 3.75/0.91  fof(f172,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl3_10),
% 3.75/0.91    inference(avatar_component_clause,[],[f171])).
% 3.75/0.91  fof(f1084,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_41),
% 3.75/0.91    inference(superposition,[],[f587,f543])).
% 3.75/0.91  fof(f543,plain,(
% 3.75/0.91    sK1 = k1_tops_1(sK0,sK1) | ~spl3_41),
% 3.75/0.91    inference(avatar_component_clause,[],[f541])).
% 3.75/0.91  fof(f587,plain,(
% 3.75/0.91    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.75/0.91    inference(subsumption_resolution,[],[f236,f225])).
% 3.75/0.91  fof(f225,plain,(
% 3.75/0.91    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.75/0.91    inference(subsumption_resolution,[],[f220,f74])).
% 3.75/0.91  fof(f74,plain,(
% 3.75/0.91    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f37])).
% 3.75/0.91  fof(f37,plain,(
% 3.75/0.91    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.75/0.91    inference(flattening,[],[f36])).
% 3.75/0.91  fof(f36,plain,(
% 3.75/0.91    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.75/0.91    inference(ennf_transformation,[],[f20])).
% 3.75/0.91  fof(f20,axiom,(
% 3.75/0.91    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.75/0.91  fof(f220,plain,(
% 3.75/0.91    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.75/0.91    inference(duplicate_literal_removal,[],[f219])).
% 3.75/0.91  fof(f219,plain,(
% 3.75/0.91    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.75/0.91    inference(superposition,[],[f89,f73])).
% 3.75/0.91  fof(f73,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f35])).
% 3.75/0.91  fof(f35,plain,(
% 3.75/0.91    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.91    inference(ennf_transformation,[],[f24])).
% 3.75/0.91  fof(f24,axiom,(
% 3.75/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.75/0.91  fof(f236,plain,(
% 3.75/0.91    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.75/0.91    inference(superposition,[],[f72,f64])).
% 3.75/0.91  fof(f72,plain,(
% 3.75/0.91    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f34])).
% 3.75/0.91  fof(f34,plain,(
% 3.75/0.91    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.91    inference(ennf_transformation,[],[f22])).
% 3.75/0.91  fof(f22,axiom,(
% 3.75/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.75/0.91  fof(f1044,plain,(
% 3.75/0.91    spl3_46 | ~spl3_3 | ~spl3_4),
% 3.75/0.91    inference(avatar_split_clause,[],[f1043,f110,f105,f654])).
% 3.75/0.91  fof(f1043,plain,(
% 3.75/0.91    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 3.75/0.91    inference(subsumption_resolution,[],[f1034,f112])).
% 3.75/0.91  fof(f1034,plain,(
% 3.75/0.91    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 3.75/0.91    inference(resolution,[],[f495,f107])).
% 3.75/0.91  fof(f495,plain,(
% 3.75/0.91    ( ! [X6,X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X6))) | r1_tarski(X5,k2_pre_topc(X6,X5)) | ~l1_pre_topc(X6)) )),
% 3.75/0.91    inference(superposition,[],[f84,f223])).
% 3.75/0.91  fof(f223,plain,(
% 3.75/0.91    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.75/0.91    inference(subsumption_resolution,[],[f222,f74])).
% 3.75/0.91  fof(f222,plain,(
% 3.75/0.91    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.75/0.91    inference(duplicate_literal_removal,[],[f217])).
% 3.75/0.91  fof(f217,plain,(
% 3.75/0.91    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.75/0.91    inference(superposition,[],[f73,f88])).
% 3.75/0.91  fof(f88,plain,(
% 3.75/0.91    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f46])).
% 3.75/0.91  fof(f46,plain,(
% 3.75/0.91    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.75/0.91    inference(flattening,[],[f45])).
% 3.75/0.91  fof(f45,plain,(
% 3.75/0.91    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.75/0.91    inference(ennf_transformation,[],[f14])).
% 3.75/0.91  fof(f14,axiom,(
% 3.75/0.91    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.75/0.91  fof(f84,plain,(
% 3.75/0.91    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.75/0.91    inference(cnf_transformation,[],[f5])).
% 3.75/0.91  fof(f5,axiom,(
% 3.75/0.91    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.75/0.91  fof(f1019,plain,(
% 3.75/0.91    spl3_41 | ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_40),
% 3.75/0.91    inference(avatar_split_clause,[],[f1018,f537,f123,f110,f105,f95,f541])).
% 3.75/0.91  fof(f95,plain,(
% 3.75/0.91    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.75/0.91  fof(f123,plain,(
% 3.75/0.91    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 3.75/0.91  fof(f537,plain,(
% 3.75/0.91    spl3_40 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 3.75/0.91  fof(f1018,plain,(
% 3.75/0.91    sK1 = k1_tops_1(sK0,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_40)),
% 3.75/0.91    inference(subsumption_resolution,[],[f1017,f92])).
% 3.75/0.91  fof(f92,plain,(
% 3.75/0.91    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.75/0.91    inference(equality_resolution,[],[f66])).
% 3.75/0.91  fof(f66,plain,(
% 3.75/0.91    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.75/0.91    inference(cnf_transformation,[],[f55])).
% 3.75/0.91  fof(f55,plain,(
% 3.75/0.91    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.91    inference(flattening,[],[f54])).
% 3.75/0.91  fof(f54,plain,(
% 3.75/0.91    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.75/0.91    inference(nnf_transformation,[],[f1])).
% 3.75/0.91  fof(f1,axiom,(
% 3.75/0.91    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.75/0.91  fof(f1017,plain,(
% 3.75/0.91    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_40)),
% 3.75/0.91    inference(subsumption_resolution,[],[f1015,f125])).
% 3.75/0.91  fof(f125,plain,(
% 3.75/0.91    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 3.75/0.91    inference(avatar_component_clause,[],[f123])).
% 3.75/0.91  fof(f1015,plain,(
% 3.75/0.91    ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_40)),
% 3.75/0.91    inference(resolution,[],[f538,f586])).
% 3.75/0.91  fof(f586,plain,(
% 3.75/0.91    ( ! [X0] : (~r1_tarski(k1_tops_1(sK0,X0),sK1) | ~r1_tarski(X0,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,X0) | ~r1_tarski(sK1,X0)) ) | (~spl3_1 | ~spl3_3 | ~spl3_4)),
% 3.75/0.91    inference(resolution,[],[f573,f67])).
% 3.75/0.91  fof(f67,plain,(
% 3.75/0.91    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f55])).
% 3.75/0.91  fof(f573,plain,(
% 3.75/0.91    ( ! [X30] : (r1_tarski(sK1,k1_tops_1(sK0,X30)) | ~r1_tarski(sK1,X30) | ~r1_tarski(X30,u1_struct_0(sK0))) ) | (~spl3_1 | ~spl3_3 | ~spl3_4)),
% 3.75/0.91    inference(subsumption_resolution,[],[f572,f112])).
% 3.75/0.91  fof(f572,plain,(
% 3.75/0.91    ( ! [X30] : (r1_tarski(sK1,k1_tops_1(sK0,X30)) | ~r1_tarski(sK1,X30) | ~l1_pre_topc(sK0) | ~r1_tarski(X30,u1_struct_0(sK0))) ) | (~spl3_1 | ~spl3_3)),
% 3.75/0.91    inference(subsumption_resolution,[],[f563,f96])).
% 3.75/0.91  fof(f96,plain,(
% 3.75/0.91    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 3.75/0.91    inference(avatar_component_clause,[],[f95])).
% 3.75/0.91  fof(f563,plain,(
% 3.75/0.91    ( ! [X30] : (~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,X30)) | ~r1_tarski(sK1,X30) | ~l1_pre_topc(sK0) | ~r1_tarski(X30,u1_struct_0(sK0))) ) | ~spl3_3),
% 3.75/0.91    inference(resolution,[],[f238,f107])).
% 3.75/0.91  fof(f238,plain,(
% 3.75/0.91    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X2))) | ~v3_pre_topc(X0,X2) | r1_tarski(X0,k1_tops_1(X2,X1)) | ~r1_tarski(X0,X1) | ~l1_pre_topc(X2) | ~r1_tarski(X1,u1_struct_0(X2))) )),
% 3.75/0.91    inference(resolution,[],[f76,f78])).
% 3.75/0.91  fof(f76,plain,(
% 3.75/0.91    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f41])).
% 3.75/0.91  fof(f41,plain,(
% 3.75/0.91    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.91    inference(flattening,[],[f40])).
% 3.75/0.91  fof(f40,plain,(
% 3.75/0.91    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.75/0.91    inference(ennf_transformation,[],[f23])).
% 3.75/0.91  fof(f23,axiom,(
% 3.75/0.91    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 3.75/0.91  fof(f538,plain,(
% 3.75/0.91    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_40),
% 3.75/0.91    inference(avatar_component_clause,[],[f537])).
% 3.75/0.91  fof(f1009,plain,(
% 3.75/0.91    spl3_40 | ~spl3_3 | ~spl3_4),
% 3.75/0.91    inference(avatar_split_clause,[],[f1008,f110,f105,f537])).
% 3.75/0.91  fof(f1008,plain,(
% 3.75/0.91    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 3.75/0.91    inference(subsumption_resolution,[],[f997,f112])).
% 3.75/0.91  fof(f997,plain,(
% 3.75/0.91    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 3.75/0.91    inference(resolution,[],[f484,f107])).
% 3.75/0.91  fof(f484,plain,(
% 3.75/0.91    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X7))) | r1_tarski(k1_tops_1(X7,X6),X6) | ~l1_pre_topc(X7)) )),
% 3.75/0.91    inference(superposition,[],[f129,f205])).
% 3.75/0.91  fof(f129,plain,(
% 3.75/0.91    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.75/0.91    inference(resolution,[],[f128,f77])).
% 3.75/0.91  fof(f77,plain,(
% 3.75/0.91    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f56])).
% 3.75/0.91  fof(f534,plain,(
% 3.75/0.91    ~spl3_10 | spl3_2 | ~spl3_9),
% 3.75/0.91    inference(avatar_split_clause,[],[f533,f167,f99,f171])).
% 3.75/0.91  fof(f533,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl3_2 | ~spl3_9)),
% 3.75/0.91    inference(subsumption_resolution,[],[f532,f168])).
% 3.75/0.91  fof(f532,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 3.75/0.91    inference(superposition,[],[f101,f64])).
% 3.75/0.91  fof(f101,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 3.75/0.91    inference(avatar_component_clause,[],[f99])).
% 3.75/0.91  fof(f473,plain,(
% 3.75/0.91    spl3_28 | ~spl3_10),
% 3.75/0.91    inference(avatar_split_clause,[],[f466,f171,f420])).
% 3.75/0.91  fof(f466,plain,(
% 3.75/0.91    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 3.75/0.91    inference(superposition,[],[f128,f173])).
% 3.75/0.91  fof(f370,plain,(
% 3.75/0.91    ~spl3_3 | ~spl3_4 | spl3_9),
% 3.75/0.91    inference(avatar_contradiction_clause,[],[f369])).
% 3.75/0.91  fof(f369,plain,(
% 3.75/0.91    $false | (~spl3_3 | ~spl3_4 | spl3_9)),
% 3.75/0.91    inference(subsumption_resolution,[],[f368,f112])).
% 3.75/0.91  fof(f368,plain,(
% 3.75/0.91    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_9)),
% 3.75/0.91    inference(subsumption_resolution,[],[f360,f107])).
% 3.75/0.91  fof(f360,plain,(
% 3.75/0.91    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 3.75/0.91    inference(resolution,[],[f225,f169])).
% 3.75/0.91  fof(f169,plain,(
% 3.75/0.91    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 3.75/0.91    inference(avatar_component_clause,[],[f167])).
% 3.75/0.91  fof(f198,plain,(
% 3.75/0.91    spl3_12 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 3.75/0.91    inference(avatar_split_clause,[],[f193,f115,f110,f105,f195])).
% 3.75/0.91  fof(f195,plain,(
% 3.75/0.91    spl3_12 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 3.75/0.91  fof(f115,plain,(
% 3.75/0.91    spl3_5 <=> v2_pre_topc(sK0)),
% 3.75/0.91    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.75/0.91  fof(f193,plain,(
% 3.75/0.91    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 3.75/0.91    inference(subsumption_resolution,[],[f192,f117])).
% 3.75/0.91  fof(f117,plain,(
% 3.75/0.91    v2_pre_topc(sK0) | ~spl3_5),
% 3.75/0.91    inference(avatar_component_clause,[],[f115])).
% 3.75/0.91  fof(f192,plain,(
% 3.75/0.91    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 3.75/0.91    inference(subsumption_resolution,[],[f189,f112])).
% 3.75/0.91  fof(f189,plain,(
% 3.75/0.91    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 3.75/0.91    inference(resolution,[],[f75,f107])).
% 3.75/0.91  fof(f75,plain,(
% 3.75/0.91    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.75/0.91    inference(cnf_transformation,[],[f39])).
% 3.75/0.91  fof(f39,plain,(
% 3.75/0.91    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.75/0.91    inference(flattening,[],[f38])).
% 3.75/0.91  fof(f38,plain,(
% 3.75/0.91    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.75/0.91    inference(ennf_transformation,[],[f21])).
% 3.75/0.91  fof(f21,axiom,(
% 3.75/0.91    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.75/0.91  fof(f126,plain,(
% 3.75/0.91    spl3_6 | ~spl3_3),
% 3.75/0.91    inference(avatar_split_clause,[],[f119,f105,f123])).
% 3.75/0.91  fof(f119,plain,(
% 3.75/0.91    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 3.75/0.91    inference(resolution,[],[f77,f107])).
% 3.75/0.91  fof(f118,plain,(
% 3.75/0.91    spl3_5),
% 3.75/0.91    inference(avatar_split_clause,[],[f59,f115])).
% 3.75/0.91  fof(f59,plain,(
% 3.75/0.91    v2_pre_topc(sK0)),
% 3.75/0.91    inference(cnf_transformation,[],[f53])).
% 3.75/0.91  fof(f53,plain,(
% 3.75/0.91    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.75/0.91    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f50,f52,f51])).
% 3.75/0.91  fof(f51,plain,(
% 3.75/0.91    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.75/0.91    introduced(choice_axiom,[])).
% 3.75/0.91  fof(f52,plain,(
% 3.75/0.91    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.75/0.91    introduced(choice_axiom,[])).
% 3.75/0.91  fof(f50,plain,(
% 3.75/0.91    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.75/0.91    inference(flattening,[],[f49])).
% 3.75/0.91  fof(f49,plain,(
% 3.75/0.91    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.75/0.91    inference(nnf_transformation,[],[f29])).
% 3.75/0.91  fof(f29,plain,(
% 3.75/0.91    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.75/0.91    inference(flattening,[],[f28])).
% 3.75/0.91  fof(f28,plain,(
% 3.75/0.91    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.75/0.91    inference(ennf_transformation,[],[f27])).
% 3.75/0.91  fof(f27,negated_conjecture,(
% 3.75/0.91    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.75/0.91    inference(negated_conjecture,[],[f26])).
% 3.75/0.91  fof(f26,conjecture,(
% 3.75/0.91    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.75/0.91    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 3.75/0.91  fof(f113,plain,(
% 3.75/0.91    spl3_4),
% 3.75/0.91    inference(avatar_split_clause,[],[f60,f110])).
% 3.75/0.91  fof(f60,plain,(
% 3.75/0.91    l1_pre_topc(sK0)),
% 3.75/0.91    inference(cnf_transformation,[],[f53])).
% 3.75/0.91  fof(f108,plain,(
% 3.75/0.91    spl3_3),
% 3.75/0.91    inference(avatar_split_clause,[],[f61,f105])).
% 3.75/0.91  fof(f61,plain,(
% 3.75/0.91    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.75/0.91    inference(cnf_transformation,[],[f53])).
% 3.75/0.91  fof(f103,plain,(
% 3.75/0.91    spl3_1 | spl3_2),
% 3.75/0.91    inference(avatar_split_clause,[],[f62,f99,f95])).
% 3.75/0.91  fof(f62,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.75/0.91    inference(cnf_transformation,[],[f53])).
% 3.75/0.91  fof(f102,plain,(
% 3.75/0.91    ~spl3_1 | ~spl3_2),
% 3.75/0.91    inference(avatar_split_clause,[],[f63,f99,f95])).
% 3.75/0.91  fof(f63,plain,(
% 3.75/0.91    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.75/0.91    inference(cnf_transformation,[],[f53])).
% 3.75/0.91  % SZS output end Proof for theBenchmark
% 3.75/0.91  % (16695)------------------------------
% 3.75/0.91  % (16695)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.91  % (16695)Termination reason: Refutation
% 3.75/0.91  
% 3.75/0.91  % (16695)Memory used [KB]: 9338
% 3.75/0.91  % (16695)Time elapsed: 0.472 s
% 3.75/0.91  % (16695)------------------------------
% 3.75/0.91  % (16695)------------------------------
% 3.75/0.91  % (16703)Time limit reached!
% 3.75/0.91  % (16703)------------------------------
% 3.75/0.91  % (16703)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.75/0.91  % (16703)Termination reason: Time limit
% 3.75/0.91  
% 3.75/0.91  % (16703)Memory used [KB]: 6524
% 3.75/0.91  % (16703)Time elapsed: 0.506 s
% 3.75/0.91  % (16703)------------------------------
% 3.75/0.91  % (16703)------------------------------
% 3.75/0.92  % (16668)Success in time 0.564 s
%------------------------------------------------------------------------------
