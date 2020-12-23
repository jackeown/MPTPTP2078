%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:15:28 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 157 expanded)
%              Number of leaves         :   24 (  71 expanded)
%              Depth                    :    8
%              Number of atoms          :  235 ( 446 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f169,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f75,f81,f90,f108,f116,f137,f145,f156,f168])).

fof(f168,plain,
    ( spl2_11
    | ~ spl2_16 ),
    inference(avatar_split_clause,[],[f166,f152,f113])).

fof(f113,plain,
    ( spl2_11
  <=> r1_tarski(sK1,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f152,plain,
    ( spl2_16
  <=> sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f166,plain,
    ( r1_tarski(sK1,k2_struct_0(sK0))
    | ~ spl2_16 ),
    inference(superposition,[],[f41,f154])).

fof(f154,plain,
    ( sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))
    | ~ spl2_16 ),
    inference(avatar_component_clause,[],[f152])).

fof(f41,plain,(
    ! [X0,X1] : r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0) ),
    inference(definition_unfolding,[],[f37,f38])).

fof(f38,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f37,plain,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

fof(f156,plain,
    ( spl2_16
    | ~ spl2_15 ),
    inference(avatar_split_clause,[],[f149,f141,f152])).

fof(f141,plain,
    ( spl2_15
  <=> sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f149,plain,
    ( sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))
    | ~ spl2_15 ),
    inference(superposition,[],[f42,f143])).

fof(f143,plain,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_15 ),
    inference(avatar_component_clause,[],[f141])).

fof(f42,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(definition_unfolding,[],[f39,f38])).

fof(f39,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f145,plain,
    ( spl2_15
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(avatar_split_clause,[],[f139,f134,f78,f141])).

fof(f78,plain,
    ( spl2_7
  <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f134,plain,
    ( spl2_14
  <=> sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f139,plain,
    ( sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_7
    | ~ spl2_14 ),
    inference(superposition,[],[f92,f136])).

fof(f136,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f92,plain,
    ( ! [X0] : k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = k4_xboole_0(k2_struct_0(sK0),X0)
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f80,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f80,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_7 ),
    inference(avatar_component_clause,[],[f78])).

fof(f137,plain,
    ( spl2_14
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f132,f105,f78,f134])).

fof(f105,plain,
    ( spl2_10
  <=> sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f132,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))
    | ~ spl2_7
    | ~ spl2_10 ),
    inference(forward_demodulation,[],[f107,f92])).

fof(f107,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f116,plain,
    ( ~ spl2_11
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f111,f86,f78,f59,f54,f49,f44,f113])).

fof(f44,plain,
    ( spl2_1
  <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f49,plain,
    ( spl2_2
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f54,plain,
    ( spl2_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f59,plain,
    ( spl2_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f86,plain,
    ( spl2_8
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f111,plain,
    ( ~ r1_tarski(sK1,k2_struct_0(sK0))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f109,f88])).

fof(f88,plain,
    ( k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f86])).

fof(f109,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0)))
    | spl2_1
    | ~ spl2_2
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_7 ),
    inference(unit_resulting_resolution,[],[f61,f56,f46,f51,f80,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m2_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m2_connsp_2(X2,X0,X1)
                  | ~ r1_tarski(X1,k1_tops_1(X0,X2)) )
                & ( r1_tarski(X1,k1_tops_1(X0,X2))
                  | ~ m2_connsp_2(X2,X0,X1) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m2_connsp_2(X2,X0,X1)
              <=> r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).

fof(f51,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f46,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f44])).

fof(f56,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f54])).

fof(f61,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f59])).

fof(f108,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f96,f71,f49,f105])).

fof(f71,plain,
    ( spl2_6
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f96,plain,
    ( sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))
    | ~ spl2_2
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f73,f51,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).

fof(f73,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f71])).

fof(f90,plain,
    ( spl2_8
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f84,f59,f54,f86])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))
    | ~ spl2_4 ),
    inference(resolution,[],[f34,f61])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).

fof(f81,plain,
    ( spl2_7
    | ~ spl2_6 ),
    inference(avatar_split_clause,[],[f76,f71,f78])).

fof(f76,plain,
    ( m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f73,f31])).

fof(f31,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f75,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f69,f54,f71])).

fof(f69,plain,
    ( l1_struct_0(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f33,f56])).

fof(f33,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f62,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f27,f59])).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,
    ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f23,f22])).

fof(f22,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X1] :
        ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,X1)
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1)
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ m2_connsp_2(k2_struct_0(X0),X0,X1)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => m2_connsp_2(k2_struct_0(X0),X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).

fof(f57,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f28,f54])).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f29,f49])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ~ spl2_1 ),
    inference(avatar_split_clause,[],[f30,f44])).

fof(f30,plain,(
    ~ m2_connsp_2(k2_struct_0(sK0),sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:28:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.46  % (21861)dis+11_5:4_acc=on:add=large:afr=on:afp=4000:afq=2.0:amm=off:anc=none:ccuc=small_ones:fsr=off:irw=on:nm=32:nwc=2.5:nicw=on:urr=on:updr=off_10 on theBenchmark
% 0.22/0.47  % (21856)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_123 on theBenchmark
% 0.22/0.47  % (21870)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_355 on theBenchmark
% 0.22/0.47  % (21866)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.22/0.47  % (21868)ott+1_28_av=off:bs=unit_only:cond=on:irw=on:nm=64:nwc=2:sp=occurrence:updr=off:uhcvi=on_1052 on theBenchmark
% 0.22/0.47  % (21866)Refutation not found, incomplete strategy% (21866)------------------------------
% 0.22/0.47  % (21866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (21858)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_75 on theBenchmark
% 0.22/0.48  % (21862)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.22/0.48  % (21861)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f169,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f47,f52,f57,f62,f75,f81,f90,f108,f116,f137,f145,f156,f168])).
% 0.22/0.48  fof(f168,plain,(
% 0.22/0.48    spl2_11 | ~spl2_16),
% 0.22/0.48    inference(avatar_split_clause,[],[f166,f152,f113])).
% 0.22/0.48  fof(f113,plain,(
% 0.22/0.48    spl2_11 <=> r1_tarski(sK1,k2_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.48  fof(f152,plain,(
% 0.22/0.48    spl2_16 <=> sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.48  fof(f166,plain,(
% 0.22/0.48    r1_tarski(sK1,k2_struct_0(sK0)) | ~spl2_16),
% 0.22/0.48    inference(superposition,[],[f41,f154])).
% 0.22/0.48  fof(f154,plain,(
% 0.22/0.48    sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)) | ~spl2_16),
% 0.22/0.48    inference(avatar_component_clause,[],[f152])).
% 0.22/0.48  fof(f41,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k1_setfam_1(k2_tarski(X0,X1)),X0)) )),
% 0.22/0.48    inference(definition_unfolding,[],[f37,f38])).
% 0.22/0.48  fof(f38,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f4])).
% 0.22/0.48  fof(f4,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.22/0.48  fof(f37,plain,(
% 0.22/0.48    ( ! [X0,X1] : (r1_tarski(k3_xboole_0(X0,X1),X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f1])).
% 0.22/0.48  fof(f1,axiom,(
% 0.22/0.48    ! [X0,X1] : r1_tarski(k3_xboole_0(X0,X1),X0)),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).
% 0.22/0.48  fof(f156,plain,(
% 0.22/0.48    spl2_16 | ~spl2_15),
% 0.22/0.48    inference(avatar_split_clause,[],[f149,f141,f152])).
% 0.22/0.48  fof(f141,plain,(
% 0.22/0.48    spl2_15 <=> sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.22/0.48  fof(f149,plain,(
% 0.22/0.48    sK1 = k1_setfam_1(k2_tarski(k2_struct_0(sK0),sK1)) | ~spl2_15),
% 0.22/0.48    inference(superposition,[],[f42,f143])).
% 0.22/0.48  fof(f143,plain,(
% 0.22/0.48    sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_15),
% 0.22/0.48    inference(avatar_component_clause,[],[f141])).
% 0.22/0.48  fof(f42,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.22/0.48    inference(definition_unfolding,[],[f39,f38])).
% 0.22/0.48  fof(f39,plain,(
% 0.22/0.48    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f2])).
% 0.22/0.48  fof(f2,axiom,(
% 0.22/0.48    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.22/0.48  fof(f145,plain,(
% 0.22/0.48    spl2_15 | ~spl2_7 | ~spl2_14),
% 0.22/0.48    inference(avatar_split_clause,[],[f139,f134,f78,f141])).
% 0.22/0.48  fof(f78,plain,(
% 0.22/0.48    spl2_7 <=> m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.48  fof(f134,plain,(
% 0.22/0.48    spl2_14 <=> sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).
% 0.22/0.48  fof(f139,plain,(
% 0.22/0.48    sK1 = k4_xboole_0(k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_7 | ~spl2_14)),
% 0.22/0.48    inference(superposition,[],[f92,f136])).
% 0.22/0.48  fof(f136,plain,(
% 0.22/0.48    sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | ~spl2_14),
% 0.22/0.48    inference(avatar_component_clause,[],[f134])).
% 0.22/0.48  fof(f92,plain,(
% 0.22/0.48    ( ! [X0] : (k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),X0) = k4_xboole_0(k2_struct_0(sK0),X0)) ) | ~spl2_7),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f80,f40])).
% 0.22/0.48  fof(f40,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f21])).
% 0.22/0.48  fof(f21,plain,(
% 0.22/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f3])).
% 0.22/0.48  fof(f3,axiom,(
% 0.22/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.22/0.48  fof(f80,plain,(
% 0.22/0.48    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_7),
% 0.22/0.48    inference(avatar_component_clause,[],[f78])).
% 0.22/0.48  fof(f137,plain,(
% 0.22/0.48    spl2_14 | ~spl2_7 | ~spl2_10),
% 0.22/0.48    inference(avatar_split_clause,[],[f132,f105,f78,f134])).
% 0.22/0.48  fof(f105,plain,(
% 0.22/0.48    spl2_10 <=> sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.48  fof(f132,plain,(
% 0.22/0.48    sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k4_xboole_0(k2_struct_0(sK0),sK1)) | (~spl2_7 | ~spl2_10)),
% 0.22/0.48    inference(forward_demodulation,[],[f107,f92])).
% 0.22/0.48  fof(f107,plain,(
% 0.22/0.48    sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | ~spl2_10),
% 0.22/0.48    inference(avatar_component_clause,[],[f105])).
% 0.22/0.48  fof(f116,plain,(
% 0.22/0.48    ~spl2_11 | spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8),
% 0.22/0.48    inference(avatar_split_clause,[],[f111,f86,f78,f59,f54,f49,f44,f113])).
% 0.22/0.48  fof(f44,plain,(
% 0.22/0.48    spl2_1 <=> m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.48  fof(f49,plain,(
% 0.22/0.48    spl2_2 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.48  fof(f54,plain,(
% 0.22/0.48    spl2_3 <=> l1_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 0.22/0.48  fof(f59,plain,(
% 0.22/0.48    spl2_4 <=> v2_pre_topc(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 0.22/0.48  fof(f86,plain,(
% 0.22/0.48    spl2_8 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.48  fof(f111,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k2_struct_0(sK0)) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7 | ~spl2_8)),
% 0.22/0.48    inference(forward_demodulation,[],[f109,f88])).
% 0.22/0.48  fof(f88,plain,(
% 0.22/0.48    k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl2_8),
% 0.22/0.48    inference(avatar_component_clause,[],[f86])).
% 0.22/0.48  fof(f109,plain,(
% 0.22/0.48    ~r1_tarski(sK1,k1_tops_1(sK0,k2_struct_0(sK0))) | (spl2_1 | ~spl2_2 | ~spl2_3 | ~spl2_4 | ~spl2_7)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f61,f56,f46,f51,f80,f36])).
% 0.22/0.48  fof(f36,plain,(
% 0.22/0.48    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m2_connsp_2(X2,X0,X1)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f25])).
% 0.22/0.48  fof(f25,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : (((m2_connsp_2(X2,X0,X1) | ~r1_tarski(X1,k1_tops_1(X0,X2))) & (r1_tarski(X1,k1_tops_1(X0,X2)) | ~m2_connsp_2(X2,X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(nnf_transformation,[],[f20])).
% 0.22/0.48  fof(f20,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f19])).
% 0.22/0.48  fof(f19,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (! [X2] : ((m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f9])).
% 0.22/0.48  fof(f9,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (m2_connsp_2(X2,X0,X1) <=> r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_connsp_2)).
% 0.22/0.48  fof(f51,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.22/0.48    inference(avatar_component_clause,[],[f49])).
% 0.22/0.48  fof(f46,plain,(
% 0.22/0.48    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) | spl2_1),
% 0.22/0.48    inference(avatar_component_clause,[],[f44])).
% 0.22/0.48  fof(f56,plain,(
% 0.22/0.48    l1_pre_topc(sK0) | ~spl2_3),
% 0.22/0.48    inference(avatar_component_clause,[],[f54])).
% 0.22/0.48  fof(f61,plain,(
% 0.22/0.48    v2_pre_topc(sK0) | ~spl2_4),
% 0.22/0.48    inference(avatar_component_clause,[],[f59])).
% 0.22/0.48  fof(f108,plain,(
% 0.22/0.48    spl2_10 | ~spl2_2 | ~spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f96,f71,f49,f105])).
% 0.22/0.48  fof(f71,plain,(
% 0.22/0.48    spl2_6 <=> l1_struct_0(sK0)),
% 0.22/0.48    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.22/0.48  fof(f96,plain,(
% 0.22/0.48    sK1 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),sK1)) | (~spl2_2 | ~spl2_6)),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f73,f51,f32])).
% 0.22/0.48  fof(f32,plain,(
% 0.22/0.48    ( ! [X0,X1] : (~l1_struct_0(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1) )),
% 0.22/0.48    inference(cnf_transformation,[],[f15])).
% 0.22/0.48  fof(f15,plain,(
% 0.22/0.48    ! [X0] : (! [X1] : (k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f7])).
% 0.22/0.48  fof(f7,axiom,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) = X1))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_pre_topc)).
% 0.22/0.48  fof(f73,plain,(
% 0.22/0.48    l1_struct_0(sK0) | ~spl2_6),
% 0.22/0.48    inference(avatar_component_clause,[],[f71])).
% 0.22/0.48  fof(f90,plain,(
% 0.22/0.48    spl2_8 | ~spl2_3 | ~spl2_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f84,f59,f54,f86])).
% 0.22/0.48  fof(f84,plain,(
% 0.22/0.48    ~l1_pre_topc(sK0) | k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) | ~spl2_4),
% 0.22/0.48    inference(resolution,[],[f34,f61])).
% 0.22/0.48  fof(f34,plain,(
% 0.22/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0))) )),
% 0.22/0.48    inference(cnf_transformation,[],[f18])).
% 0.22/0.48  fof(f18,plain,(
% 0.22/0.48    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.48    inference(flattening,[],[f17])).
% 0.22/0.48  fof(f17,plain,(
% 0.22/0.48    ! [X0] : (k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f8])).
% 0.22/0.48  fof(f8,axiom,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tops_1)).
% 0.22/0.48  fof(f81,plain,(
% 0.22/0.48    spl2_7 | ~spl2_6),
% 0.22/0.48    inference(avatar_split_clause,[],[f76,f71,f78])).
% 0.22/0.48  fof(f76,plain,(
% 0.22/0.48    m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_6),
% 0.22/0.48    inference(unit_resulting_resolution,[],[f73,f31])).
% 0.22/0.48  fof(f31,plain,(
% 0.22/0.48    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f14])).
% 0.22/0.48  fof(f14,plain,(
% 0.22/0.48    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f5])).
% 0.22/0.48  fof(f5,axiom,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.22/0.48  fof(f75,plain,(
% 0.22/0.48    spl2_6 | ~spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f69,f54,f71])).
% 0.22/0.48  fof(f69,plain,(
% 0.22/0.48    l1_struct_0(sK0) | ~spl2_3),
% 0.22/0.48    inference(resolution,[],[f33,f56])).
% 0.22/0.48  fof(f33,plain,(
% 0.22/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.48    inference(cnf_transformation,[],[f16])).
% 0.22/0.48  fof(f16,plain,(
% 0.22/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.48    inference(ennf_transformation,[],[f6])).
% 0.22/0.48  fof(f6,axiom,(
% 0.22/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.48  fof(f62,plain,(
% 0.22/0.48    spl2_4),
% 0.22/0.48    inference(avatar_split_clause,[],[f27,f59])).
% 0.22/0.48  fof(f27,plain,(
% 0.22/0.48    v2_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f24,plain,(
% 0.22/0.48    (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 0.22/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f13,f23,f22])).
% 0.22/0.48  fof(f22,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f23,plain,(
% 0.22/0.48    ? [X1] : (~m2_connsp_2(k2_struct_0(sK0),sK0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (~m2_connsp_2(k2_struct_0(sK0),sK0,sK1) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.48    introduced(choice_axiom,[])).
% 0.22/0.48  fof(f13,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.48    inference(flattening,[],[f12])).
% 0.22/0.48  fof(f12,plain,(
% 0.22/0.48    ? [X0] : (? [X1] : (~m2_connsp_2(k2_struct_0(X0),X0,X1) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.48    inference(ennf_transformation,[],[f11])).
% 0.22/0.48  fof(f11,negated_conjecture,(
% 0.22/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.48    inference(negated_conjecture,[],[f10])).
% 0.22/0.48  fof(f10,conjecture,(
% 0.22/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => m2_connsp_2(k2_struct_0(X0),X0,X1)))),
% 0.22/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_connsp_2)).
% 0.22/0.48  fof(f57,plain,(
% 0.22/0.48    spl2_3),
% 0.22/0.48    inference(avatar_split_clause,[],[f28,f54])).
% 0.22/0.48  fof(f28,plain,(
% 0.22/0.48    l1_pre_topc(sK0)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f52,plain,(
% 0.22/0.48    spl2_2),
% 0.22/0.48    inference(avatar_split_clause,[],[f29,f49])).
% 0.22/0.48  fof(f29,plain,(
% 0.22/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  fof(f47,plain,(
% 0.22/0.48    ~spl2_1),
% 0.22/0.48    inference(avatar_split_clause,[],[f30,f44])).
% 0.22/0.48  fof(f30,plain,(
% 0.22/0.48    ~m2_connsp_2(k2_struct_0(sK0),sK0,sK1)),
% 0.22/0.48    inference(cnf_transformation,[],[f24])).
% 0.22/0.48  % SZS output end Proof for theBenchmark
% 0.22/0.48  % (21861)------------------------------
% 0.22/0.48  % (21861)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (21861)Termination reason: Refutation
% 0.22/0.48  
% 0.22/0.48  % (21861)Memory used [KB]: 6140
% 0.22/0.48  % (21861)Time elapsed: 0.056 s
% 0.22/0.48  % (21861)------------------------------
% 0.22/0.48  % (21861)------------------------------
% 0.22/0.48  % (21866)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (21854)Success in time 0.114 s
%------------------------------------------------------------------------------
