%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:37 EST 2020

% Result     : Theorem 3.96s
% Output     : Refutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :  201 ( 385 expanded)
%              Number of leaves         :   42 ( 137 expanded)
%              Depth                    :   13
%              Number of atoms          :  610 (1201 expanded)
%              Number of equality atoms :   96 ( 223 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2833,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f116,f121,f126,f131,f139,f230,f470,f529,f580,f1494,f1525,f1571,f1583,f1598,f1619,f1621,f1632,f2712,f2752,f2798,f2832])).

fof(f2832,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2798,plain,
    ( spl2_58
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_92 ),
    inference(avatar_split_clause,[],[f2797,f2709,f123,f118,f1502])).

fof(f1502,plain,
    ( spl2_58
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).

fof(f118,plain,
    ( spl2_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).

fof(f123,plain,
    ( spl2_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).

fof(f2709,plain,
    ( spl2_92
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).

fof(f2797,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_92 ),
    inference(subsumption_resolution,[],[f2796,f125])).

fof(f125,plain,
    ( l1_pre_topc(sK0)
    | ~ spl2_4 ),
    inference(avatar_component_clause,[],[f123])).

fof(f2796,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_92 ),
    inference(subsumption_resolution,[],[f2772,f120])).

fof(f120,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_3 ),
    inference(avatar_component_clause,[],[f118])).

fof(f2772,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_92 ),
    inference(superposition,[],[f243,f2711])).

fof(f2711,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl2_92 ),
    inference(avatar_component_clause,[],[f2709])).

fof(f243,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f242])).

fof(f242,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f74,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f2752,plain,(
    ~ spl2_63 ),
    inference(avatar_contradiction_clause,[],[f2727])).

fof(f2727,plain,
    ( $false
    | ~ spl2_63 ),
    inference(unit_resulting_resolution,[],[f142,f142,f1664,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f1664,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_63 ),
    inference(avatar_component_clause,[],[f1663])).

fof(f1663,plain,
    ( spl2_63
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).

fof(f142,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f104,f94])).

fof(f94,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f104,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f2712,plain,
    ( spl2_63
    | spl2_92
    | ~ spl2_21
    | ~ spl2_25 ),
    inference(avatar_split_clause,[],[f2707,f457,f413,f2709,f1663])).

fof(f413,plain,
    ( spl2_21
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).

fof(f457,plain,
    ( spl2_25
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).

fof(f2707,plain,
    ( ! [X12] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_21
    | ~ spl2_25 ),
    inference(subsumption_resolution,[],[f2672,f415])).

fof(f415,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_21 ),
    inference(avatar_component_clause,[],[f413])).

fof(f2672,plain,
    ( ! [X12] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X12,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl2_25 ),
    inference(superposition,[],[f662,f459])).

fof(f459,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_25 ),
    inference(avatar_component_clause,[],[f457])).

fof(f662,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f657,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f657,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f271,f74])).

fof(f271,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f267,f90])).

fof(f267,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f81,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f1632,plain,
    ( ~ spl2_57
    | spl2_58
    | ~ spl2_56 ),
    inference(avatar_split_clause,[],[f1631,f1491,f1502,f1498])).

fof(f1498,plain,
    ( spl2_57
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).

fof(f1491,plain,
    ( spl2_56
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).

fof(f1631,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl2_56 ),
    inference(resolution,[],[f1493,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
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

fof(f1493,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_56 ),
    inference(avatar_component_clause,[],[f1491])).

fof(f1621,plain,
    ( spl2_25
    | ~ spl2_10
    | ~ spl2_24 ),
    inference(avatar_split_clause,[],[f1620,f453,f198,f457])).

fof(f198,plain,
    ( spl2_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f453,plain,
    ( spl2_24
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f1620,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl2_10
    | ~ spl2_24 ),
    inference(subsumption_resolution,[],[f1611,f454])).

fof(f454,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f453])).

fof(f1611,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f188,f200])).

fof(f200,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f188,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f184])).

fof(f184,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f78,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1619,plain,
    ( spl2_21
    | ~ spl2_10 ),
    inference(avatar_split_clause,[],[f1606,f198,f413])).

fof(f1606,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl2_10 ),
    inference(superposition,[],[f142,f200])).

fof(f1598,plain,
    ( spl2_10
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f1597,f194,f112,f198])).

fof(f112,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f194,plain,
    ( spl2_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f1597,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f1594,f195])).

fof(f195,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f1594,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(superposition,[],[f74,f113])).

fof(f113,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f1583,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_10
    | ~ spl2_58 ),
    inference(avatar_contradiction_clause,[],[f1582])).

fof(f1582,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_10
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f1581,f125])).

fof(f1581,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_10
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f1580,f120])).

fof(f1580,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_10
    | ~ spl2_58 ),
    inference(subsumption_resolution,[],[f1577,f199])).

fof(f199,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f198])).

fof(f1577,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_58 ),
    inference(superposition,[],[f772,f1504])).

fof(f1504,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl2_58 ),
    inference(avatar_component_clause,[],[f1502])).

fof(f772,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f273,f263])).

fof(f263,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f256,f85])).

fof(f85,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f256,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f255])).

fof(f255,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f100,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f273,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f82,f74])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1571,plain,
    ( ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | spl2_57 ),
    inference(avatar_contradiction_clause,[],[f1570])).

fof(f1570,plain,
    ( $false
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | spl2_57 ),
    inference(subsumption_resolution,[],[f1569,f105])).

fof(f105,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f67])).

fof(f1569,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl2_1
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | spl2_57 ),
    inference(subsumption_resolution,[],[f1561,f109])).

fof(f109,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl2_1 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f1561,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6
    | spl2_57 ),
    inference(resolution,[],[f1500,f300])).

fof(f300,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_6 ),
    inference(subsumption_resolution,[],[f294,f161])).

fof(f161,plain,
    ( ! [X5] :
        ( r1_tarski(X5,u1_struct_0(sK0))
        | ~ r1_tarski(X5,sK1) )
    | ~ spl2_6 ),
    inference(resolution,[],[f95,f138])).

fof(f138,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f136])).

fof(f136,plain,
    ( spl2_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f294,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(resolution,[],[f287,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f287,plain,
    ( ! [X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X16,sK1) )
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f285,f125])).

fof(f285,plain,
    ( ! [X16] :
        ( ~ r1_tarski(X16,sK1)
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl2_3 ),
    inference(resolution,[],[f87,f120])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f28,axiom,(
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

fof(f1500,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl2_57 ),
    inference(avatar_component_clause,[],[f1498])).

fof(f1525,plain,
    ( spl2_26
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f1524,f123,f118,f467])).

fof(f467,plain,
    ( spl2_26
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).

fof(f1524,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1516,f125])).

fof(f1516,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f588,f120])).

fof(f588,plain,(
    ! [X14,X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X14)))
      | r1_tarski(X13,k2_pre_topc(X14,X13))
      | ~ l1_pre_topc(X14) ) ),
    inference(superposition,[],[f97,f261])).

fof(f261,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f258,f85])).

fof(f258,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f253])).

fof(f253,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f84,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1494,plain,
    ( spl2_56
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(avatar_split_clause,[],[f1489,f123,f118,f1491])).

fof(f1489,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f1480,f125])).

fof(f1480,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f554,f120])).

fof(f554,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | r1_tarski(k1_tops_1(X5,X4),X4)
      | ~ l1_pre_topc(X5) ) ),
    inference(superposition,[],[f141,f243])).

fof(f141,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(backward_demodulation,[],[f134,f94])).

fof(f134,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(resolution,[],[f88,f104])).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f580,plain,
    ( ~ spl2_10
    | spl2_2
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f579,f194,f112,f198])).

fof(f579,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl2_2
    | ~ spl2_9 ),
    inference(subsumption_resolution,[],[f578,f195])).

fof(f578,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_2 ),
    inference(superposition,[],[f114,f74])).

fof(f114,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_2 ),
    inference(avatar_component_clause,[],[f112])).

fof(f529,plain,
    ( ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl2_3
    | ~ spl2_4
    | spl2_9 ),
    inference(subsumption_resolution,[],[f527,f125])).

fof(f527,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl2_3
    | spl2_9 ),
    inference(subsumption_resolution,[],[f520,f120])).

fof(f520,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(resolution,[],[f263,f196])).

fof(f196,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f194])).

fof(f470,plain,
    ( ~ spl2_26
    | spl2_24 ),
    inference(avatar_split_clause,[],[f465,f453,f467])).

fof(f465,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl2_24 ),
    inference(resolution,[],[f455,f89])).

fof(f455,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f453])).

fof(f230,plain,
    ( spl2_13
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(avatar_split_clause,[],[f225,f128,f123,f118,f227])).

fof(f227,plain,
    ( spl2_13
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).

fof(f128,plain,
    ( spl2_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f225,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl2_3
    | ~ spl2_4
    | ~ spl2_5 ),
    inference(subsumption_resolution,[],[f224,f130])).

fof(f130,plain,
    ( v2_pre_topc(sK0)
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f128])).

fof(f224,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3
    | ~ spl2_4 ),
    inference(subsumption_resolution,[],[f222,f125])).

fof(f222,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl2_3 ),
    inference(resolution,[],[f86,f120])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f139,plain,
    ( spl2_6
    | ~ spl2_3 ),
    inference(avatar_split_clause,[],[f133,f118,f136])).

fof(f133,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl2_3 ),
    inference(resolution,[],[f88,f120])).

fof(f131,plain,(
    spl2_5 ),
    inference(avatar_split_clause,[],[f69,f128])).

fof(f69,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f62,f64,f63])).

fof(f63,plain,
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

fof(f64,plain,
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

fof(f62,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f61])).

fof(f61,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f35,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f32])).

fof(f32,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f126,plain,(
    spl2_4 ),
    inference(avatar_split_clause,[],[f70,f123])).

fof(f70,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f121,plain,(
    spl2_3 ),
    inference(avatar_split_clause,[],[f71,f118])).

fof(f71,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f65])).

fof(f116,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f72,f112,f108])).

fof(f72,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f115,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f73,f112,f108])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:16:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.51  % (8535)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.51  % (8519)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (8517)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (8527)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.51  % (8515)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.52  % (8513)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (8514)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (8541)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.52  % (8526)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.53  % (8533)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (8516)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (8525)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (8523)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (8521)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.54  % (8536)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.54  % (8534)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (8518)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (8528)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (8539)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (8532)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (8537)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.55  % (8520)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.55  % (8531)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.55  % (8542)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (8540)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.55  % (8522)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (8529)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.56  % (8524)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.56  % (8538)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.57  % (8530)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 3.20/0.81  % (8537)Time limit reached!
% 3.20/0.81  % (8537)------------------------------
% 3.20/0.81  % (8537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.82  % (8515)Time limit reached!
% 3.20/0.82  % (8515)------------------------------
% 3.20/0.82  % (8515)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.20/0.82  % (8515)Termination reason: Time limit
% 3.20/0.82  
% 3.20/0.82  % (8515)Memory used [KB]: 6652
% 3.20/0.82  % (8515)Time elapsed: 0.409 s
% 3.20/0.82  % (8515)------------------------------
% 3.20/0.82  % (8515)------------------------------
% 3.20/0.82  % (8537)Termination reason: Time limit
% 3.20/0.82  % (8537)Termination phase: Saturation
% 3.20/0.82  
% 3.20/0.82  % (8537)Memory used [KB]: 14967
% 3.20/0.82  % (8537)Time elapsed: 0.400 s
% 3.20/0.82  % (8537)------------------------------
% 3.20/0.82  % (8537)------------------------------
% 3.96/0.90  % (8534)Refutation found. Thanks to Tanya!
% 3.96/0.90  % SZS status Theorem for theBenchmark
% 3.96/0.90  % SZS output start Proof for theBenchmark
% 3.96/0.90  fof(f2833,plain,(
% 3.96/0.90    $false),
% 3.96/0.90    inference(avatar_sat_refutation,[],[f115,f116,f121,f126,f131,f139,f230,f470,f529,f580,f1494,f1525,f1571,f1583,f1598,f1619,f1621,f1632,f2712,f2752,f2798,f2832])).
% 3.96/0.90  fof(f2832,plain,(
% 3.96/0.90    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.96/0.90    introduced(theory_tautology_sat_conflict,[])).
% 3.96/0.90  fof(f2798,plain,(
% 3.96/0.90    spl2_58 | ~spl2_3 | ~spl2_4 | ~spl2_92),
% 3.96/0.90    inference(avatar_split_clause,[],[f2797,f2709,f123,f118,f1502])).
% 3.96/0.90  fof(f1502,plain,(
% 3.96/0.90    spl2_58 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_58])])).
% 3.96/0.90  fof(f118,plain,(
% 3.96/0.90    spl2_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_3])])).
% 3.96/0.90  fof(f123,plain,(
% 3.96/0.90    spl2_4 <=> l1_pre_topc(sK0)),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_4])])).
% 3.96/0.90  fof(f2709,plain,(
% 3.96/0.90    spl2_92 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_92])])).
% 3.96/0.90  fof(f2797,plain,(
% 3.96/0.90    sK1 = k1_tops_1(sK0,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_92)),
% 3.96/0.90    inference(subsumption_resolution,[],[f2796,f125])).
% 3.96/0.90  fof(f125,plain,(
% 3.96/0.90    l1_pre_topc(sK0) | ~spl2_4),
% 3.96/0.90    inference(avatar_component_clause,[],[f123])).
% 3.96/0.90  fof(f2796,plain,(
% 3.96/0.90    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl2_3 | ~spl2_92)),
% 3.96/0.90    inference(subsumption_resolution,[],[f2772,f120])).
% 3.96/0.90  fof(f120,plain,(
% 3.96/0.90    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_3),
% 3.96/0.90    inference(avatar_component_clause,[],[f118])).
% 3.96/0.90  fof(f2772,plain,(
% 3.96/0.90    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_92),
% 3.96/0.90    inference(superposition,[],[f243,f2711])).
% 3.96/0.90  fof(f2711,plain,(
% 3.96/0.90    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl2_92),
% 3.96/0.90    inference(avatar_component_clause,[],[f2709])).
% 3.96/0.90  fof(f243,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.90    inference(duplicate_literal_removal,[],[f242])).
% 3.96/0.90  fof(f242,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.90    inference(superposition,[],[f74,f83])).
% 3.96/0.90  fof(f83,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f42])).
% 3.96/0.90  fof(f42,plain,(
% 3.96/0.90    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.90    inference(ennf_transformation,[],[f31])).
% 3.96/0.90  fof(f31,axiom,(
% 3.96/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.96/0.90  fof(f74,plain,(
% 3.96/0.90    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f36])).
% 3.96/0.90  fof(f36,plain,(
% 3.96/0.90    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.90    inference(ennf_transformation,[],[f21])).
% 3.96/0.90  fof(f21,axiom,(
% 3.96/0.90    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.96/0.90  fof(f2752,plain,(
% 3.96/0.90    ~spl2_63),
% 3.96/0.90    inference(avatar_contradiction_clause,[],[f2727])).
% 3.96/0.90  fof(f2727,plain,(
% 3.96/0.90    $false | ~spl2_63),
% 3.96/0.90    inference(unit_resulting_resolution,[],[f142,f142,f1664,f100])).
% 3.96/0.90  fof(f100,plain,(
% 3.96/0.90    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f60])).
% 3.96/0.90  fof(f60,plain,(
% 3.96/0.90    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.90    inference(flattening,[],[f59])).
% 3.96/0.90  fof(f59,plain,(
% 3.96/0.90    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.96/0.90    inference(ennf_transformation,[],[f14])).
% 3.96/0.90  fof(f14,axiom,(
% 3.96/0.90    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.96/0.90  fof(f1664,plain,(
% 3.96/0.90    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_63),
% 3.96/0.90    inference(avatar_component_clause,[],[f1663])).
% 3.96/0.90  fof(f1663,plain,(
% 3.96/0.90    spl2_63 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_63])])).
% 3.96/0.90  fof(f142,plain,(
% 3.96/0.90    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(backward_demodulation,[],[f104,f94])).
% 3.96/0.90  fof(f94,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f20])).
% 3.96/0.90  fof(f20,axiom,(
% 3.96/0.90    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.96/0.90  fof(f104,plain,(
% 3.96/0.90    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f15])).
% 3.96/0.90  fof(f15,axiom,(
% 3.96/0.90    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 3.96/0.90  fof(f2712,plain,(
% 3.96/0.90    spl2_63 | spl2_92 | ~spl2_21 | ~spl2_25),
% 3.96/0.90    inference(avatar_split_clause,[],[f2707,f457,f413,f2709,f1663])).
% 3.96/0.90  fof(f413,plain,(
% 3.96/0.90    spl2_21 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_21])])).
% 3.96/0.90  fof(f457,plain,(
% 3.96/0.90    spl2_25 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_25])])).
% 3.96/0.90  fof(f2707,plain,(
% 3.96/0.90    ( ! [X12] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X12,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl2_21 | ~spl2_25)),
% 3.96/0.90    inference(subsumption_resolution,[],[f2672,f415])).
% 3.96/0.90  fof(f415,plain,(
% 3.96/0.90    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_21),
% 3.96/0.90    inference(avatar_component_clause,[],[f413])).
% 3.96/0.90  fof(f2672,plain,(
% 3.96/0.90    ( ! [X12] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X12,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl2_25),
% 3.96/0.90    inference(superposition,[],[f662,f459])).
% 3.96/0.90  fof(f459,plain,(
% 3.96/0.90    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl2_25),
% 3.96/0.90    inference(avatar_component_clause,[],[f457])).
% 3.96/0.90  fof(f662,plain,(
% 3.96/0.90    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 3.96/0.90    inference(subsumption_resolution,[],[f657,f90])).
% 3.96/0.90  fof(f90,plain,(
% 3.96/0.90    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f50])).
% 3.96/0.90  fof(f50,plain,(
% 3.96/0.90    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.90    inference(ennf_transformation,[],[f13])).
% 3.96/0.90  fof(f13,axiom,(
% 3.96/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.96/0.90  fof(f657,plain,(
% 3.96/0.90    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 3.96/0.90    inference(superposition,[],[f271,f74])).
% 3.96/0.90  fof(f271,plain,(
% 3.96/0.90    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.96/0.90    inference(subsumption_resolution,[],[f267,f90])).
% 3.96/0.90  fof(f267,plain,(
% 3.96/0.90    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.96/0.90    inference(superposition,[],[f81,f98])).
% 3.96/0.90  fof(f98,plain,(
% 3.96/0.90    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f56])).
% 3.96/0.90  fof(f56,plain,(
% 3.96/0.90    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.96/0.90    inference(ennf_transformation,[],[f16])).
% 3.96/0.90  fof(f16,axiom,(
% 3.96/0.90    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 3.96/0.90  fof(f81,plain,(
% 3.96/0.90    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f40])).
% 3.96/0.90  fof(f40,plain,(
% 3.96/0.90    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.90    inference(ennf_transformation,[],[f22])).
% 3.96/0.90  fof(f22,axiom,(
% 3.96/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 3.96/0.90  fof(f1632,plain,(
% 3.96/0.90    ~spl2_57 | spl2_58 | ~spl2_56),
% 3.96/0.90    inference(avatar_split_clause,[],[f1631,f1491,f1502,f1498])).
% 3.96/0.90  fof(f1498,plain,(
% 3.96/0.90    spl2_57 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_57])])).
% 3.96/0.90  fof(f1491,plain,(
% 3.96/0.90    spl2_56 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_56])])).
% 3.96/0.90  fof(f1631,plain,(
% 3.96/0.90    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl2_56),
% 3.96/0.90    inference(resolution,[],[f1493,f77])).
% 3.96/0.90  fof(f77,plain,(
% 3.96/0.90    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f67])).
% 3.96/0.90  fof(f67,plain,(
% 3.96/0.90    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.96/0.90    inference(flattening,[],[f66])).
% 3.96/0.90  fof(f66,plain,(
% 3.96/0.90    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.96/0.90    inference(nnf_transformation,[],[f1])).
% 3.96/0.90  fof(f1,axiom,(
% 3.96/0.90    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.96/0.90  fof(f1493,plain,(
% 3.96/0.90    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl2_56),
% 3.96/0.90    inference(avatar_component_clause,[],[f1491])).
% 3.96/0.90  fof(f1621,plain,(
% 3.96/0.90    spl2_25 | ~spl2_10 | ~spl2_24),
% 3.96/0.90    inference(avatar_split_clause,[],[f1620,f453,f198,f457])).
% 3.96/0.90  fof(f198,plain,(
% 3.96/0.90    spl2_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 3.96/0.90  fof(f453,plain,(
% 3.96/0.90    spl2_24 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 3.96/0.90  fof(f1620,plain,(
% 3.96/0.90    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl2_10 | ~spl2_24)),
% 3.96/0.90    inference(subsumption_resolution,[],[f1611,f454])).
% 3.96/0.90  fof(f454,plain,(
% 3.96/0.90    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_24),
% 3.96/0.90    inference(avatar_component_clause,[],[f453])).
% 3.96/0.90  fof(f1611,plain,(
% 3.96/0.90    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 3.96/0.90    inference(superposition,[],[f188,f200])).
% 3.96/0.90  fof(f200,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl2_10),
% 3.96/0.90    inference(avatar_component_clause,[],[f198])).
% 3.96/0.90  fof(f188,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(duplicate_literal_removal,[],[f184])).
% 3.96/0.90  fof(f184,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(superposition,[],[f78,f79])).
% 3.96/0.90  fof(f79,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f38])).
% 3.96/0.90  fof(f38,plain,(
% 3.96/0.90    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.90    inference(ennf_transformation,[],[f12])).
% 3.96/0.90  fof(f12,axiom,(
% 3.96/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.96/0.90  fof(f78,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f37])).
% 3.96/0.90  fof(f37,plain,(
% 3.96/0.90    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.90    inference(ennf_transformation,[],[f17])).
% 3.96/0.90  fof(f17,axiom,(
% 3.96/0.90    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.96/0.90  fof(f1619,plain,(
% 3.96/0.90    spl2_21 | ~spl2_10),
% 3.96/0.90    inference(avatar_split_clause,[],[f1606,f198,f413])).
% 3.96/0.90  fof(f1606,plain,(
% 3.96/0.90    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl2_10),
% 3.96/0.90    inference(superposition,[],[f142,f200])).
% 3.96/0.90  fof(f1598,plain,(
% 3.96/0.90    spl2_10 | ~spl2_2 | ~spl2_9),
% 3.96/0.90    inference(avatar_split_clause,[],[f1597,f194,f112,f198])).
% 3.96/0.90  fof(f112,plain,(
% 3.96/0.90    spl2_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 3.96/0.90  fof(f194,plain,(
% 3.96/0.90    spl2_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 3.96/0.90  fof(f1597,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl2_2 | ~spl2_9)),
% 3.96/0.90    inference(subsumption_resolution,[],[f1594,f195])).
% 3.96/0.90  fof(f195,plain,(
% 3.96/0.90    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_9),
% 3.96/0.90    inference(avatar_component_clause,[],[f194])).
% 3.96/0.90  fof(f1594,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 3.96/0.90    inference(superposition,[],[f74,f113])).
% 3.96/0.90  fof(f113,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl2_2),
% 3.96/0.90    inference(avatar_component_clause,[],[f112])).
% 3.96/0.90  fof(f1583,plain,(
% 3.96/0.90    ~spl2_3 | ~spl2_4 | spl2_10 | ~spl2_58),
% 3.96/0.90    inference(avatar_contradiction_clause,[],[f1582])).
% 3.96/0.90  fof(f1582,plain,(
% 3.96/0.90    $false | (~spl2_3 | ~spl2_4 | spl2_10 | ~spl2_58)),
% 3.96/0.90    inference(subsumption_resolution,[],[f1581,f125])).
% 3.96/0.90  fof(f1581,plain,(
% 3.96/0.90    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_10 | ~spl2_58)),
% 3.96/0.90    inference(subsumption_resolution,[],[f1580,f120])).
% 3.96/0.90  fof(f1580,plain,(
% 3.96/0.90    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl2_10 | ~spl2_58)),
% 3.96/0.90    inference(subsumption_resolution,[],[f1577,f199])).
% 3.96/0.90  fof(f199,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl2_10),
% 3.96/0.90    inference(avatar_component_clause,[],[f198])).
% 3.96/0.90  fof(f1577,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl2_58),
% 3.96/0.90    inference(superposition,[],[f772,f1504])).
% 3.96/0.90  fof(f1504,plain,(
% 3.96/0.90    sK1 = k1_tops_1(sK0,sK1) | ~spl2_58),
% 3.96/0.90    inference(avatar_component_clause,[],[f1502])).
% 3.96/0.90  fof(f772,plain,(
% 3.96/0.90    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.96/0.90    inference(subsumption_resolution,[],[f273,f263])).
% 3.96/0.90  fof(f263,plain,(
% 3.96/0.90    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.96/0.90    inference(subsumption_resolution,[],[f256,f85])).
% 3.96/0.90  fof(f85,plain,(
% 3.96/0.90    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f45])).
% 3.96/0.90  fof(f45,plain,(
% 3.96/0.90    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.96/0.90    inference(flattening,[],[f44])).
% 3.96/0.90  fof(f44,plain,(
% 3.96/0.90    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.96/0.90    inference(ennf_transformation,[],[f25])).
% 3.96/0.90  fof(f25,axiom,(
% 3.96/0.90    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.96/0.90  fof(f256,plain,(
% 3.96/0.90    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.96/0.90    inference(duplicate_literal_removal,[],[f255])).
% 3.96/0.90  fof(f255,plain,(
% 3.96/0.90    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.96/0.90    inference(superposition,[],[f100,f84])).
% 3.96/0.90  fof(f84,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f43])).
% 3.96/0.90  fof(f43,plain,(
% 3.96/0.90    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.90    inference(ennf_transformation,[],[f30])).
% 3.96/0.90  fof(f30,axiom,(
% 3.96/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.96/0.90  fof(f273,plain,(
% 3.96/0.90    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.96/0.90    inference(superposition,[],[f82,f74])).
% 3.96/0.90  fof(f82,plain,(
% 3.96/0.90    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f41])).
% 3.96/0.90  fof(f41,plain,(
% 3.96/0.90    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.90    inference(ennf_transformation,[],[f27])).
% 3.96/0.90  fof(f27,axiom,(
% 3.96/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.96/0.90  fof(f1571,plain,(
% 3.96/0.90    ~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_6 | spl2_57),
% 3.96/0.90    inference(avatar_contradiction_clause,[],[f1570])).
% 3.96/0.90  fof(f1570,plain,(
% 3.96/0.90    $false | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_6 | spl2_57)),
% 3.96/0.90    inference(subsumption_resolution,[],[f1569,f105])).
% 3.96/0.90  fof(f105,plain,(
% 3.96/0.90    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.96/0.90    inference(equality_resolution,[],[f76])).
% 3.96/0.90  fof(f76,plain,(
% 3.96/0.90    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.96/0.90    inference(cnf_transformation,[],[f67])).
% 3.96/0.90  fof(f1569,plain,(
% 3.96/0.90    ~r1_tarski(sK1,sK1) | (~spl2_1 | ~spl2_3 | ~spl2_4 | ~spl2_6 | spl2_57)),
% 3.96/0.90    inference(subsumption_resolution,[],[f1561,f109])).
% 3.96/0.90  fof(f109,plain,(
% 3.96/0.90    v3_pre_topc(sK1,sK0) | ~spl2_1),
% 3.96/0.90    inference(avatar_component_clause,[],[f108])).
% 3.96/0.90  fof(f108,plain,(
% 3.96/0.90    spl2_1 <=> v3_pre_topc(sK1,sK0)),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 3.96/0.90  fof(f1561,plain,(
% 3.96/0.90    ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | (~spl2_3 | ~spl2_4 | ~spl2_6 | spl2_57)),
% 3.96/0.90    inference(resolution,[],[f1500,f300])).
% 3.96/0.90  fof(f300,plain,(
% 3.96/0.90    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1)) ) | (~spl2_3 | ~spl2_4 | ~spl2_6)),
% 3.96/0.90    inference(subsumption_resolution,[],[f294,f161])).
% 3.96/0.90  fof(f161,plain,(
% 3.96/0.90    ( ! [X5] : (r1_tarski(X5,u1_struct_0(sK0)) | ~r1_tarski(X5,sK1)) ) | ~spl2_6),
% 3.96/0.90    inference(resolution,[],[f95,f138])).
% 3.96/0.90  fof(f138,plain,(
% 3.96/0.90    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_6),
% 3.96/0.90    inference(avatar_component_clause,[],[f136])).
% 3.96/0.90  fof(f136,plain,(
% 3.96/0.90    spl2_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 3.96/0.90  fof(f95,plain,(
% 3.96/0.90    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f54])).
% 3.96/0.90  fof(f54,plain,(
% 3.96/0.90    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.96/0.90    inference(flattening,[],[f53])).
% 3.96/0.90  fof(f53,plain,(
% 3.96/0.90    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.96/0.90    inference(ennf_transformation,[],[f4])).
% 3.96/0.90  fof(f4,axiom,(
% 3.96/0.90    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.96/0.90  fof(f294,plain,(
% 3.96/0.90    ( ! [X0] : (~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl2_3 | ~spl2_4)),
% 3.96/0.90    inference(resolution,[],[f287,f89])).
% 3.96/0.90  fof(f89,plain,(
% 3.96/0.90    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f68])).
% 3.96/0.90  fof(f68,plain,(
% 3.96/0.90    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.96/0.90    inference(nnf_transformation,[],[f24])).
% 3.96/0.90  fof(f24,axiom,(
% 3.96/0.90    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.96/0.90  fof(f287,plain,(
% 3.96/0.90    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~r1_tarski(X16,sK1)) ) | (~spl2_3 | ~spl2_4)),
% 3.96/0.90    inference(subsumption_resolution,[],[f285,f125])).
% 3.96/0.90  fof(f285,plain,(
% 3.96/0.90    ( ! [X16] : (~r1_tarski(X16,sK1) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl2_3),
% 3.96/0.90    inference(resolution,[],[f87,f120])).
% 3.96/0.90  fof(f87,plain,(
% 3.96/0.90    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f49])).
% 3.96/0.90  fof(f49,plain,(
% 3.96/0.90    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.90    inference(flattening,[],[f48])).
% 3.96/0.90  fof(f48,plain,(
% 3.96/0.90    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.96/0.90    inference(ennf_transformation,[],[f28])).
% 3.96/0.90  fof(f28,axiom,(
% 3.96/0.90    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 3.96/0.90  fof(f1500,plain,(
% 3.96/0.90    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl2_57),
% 3.96/0.90    inference(avatar_component_clause,[],[f1498])).
% 3.96/0.90  fof(f1525,plain,(
% 3.96/0.90    spl2_26 | ~spl2_3 | ~spl2_4),
% 3.96/0.90    inference(avatar_split_clause,[],[f1524,f123,f118,f467])).
% 3.96/0.90  fof(f467,plain,(
% 3.96/0.90    spl2_26 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_26])])).
% 3.96/0.90  fof(f1524,plain,(
% 3.96/0.90    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl2_3 | ~spl2_4)),
% 3.96/0.90    inference(subsumption_resolution,[],[f1516,f125])).
% 3.96/0.90  fof(f1516,plain,(
% 3.96/0.90    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl2_3),
% 3.96/0.90    inference(resolution,[],[f588,f120])).
% 3.96/0.90  fof(f588,plain,(
% 3.96/0.90    ( ! [X14,X13] : (~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(X14))) | r1_tarski(X13,k2_pre_topc(X14,X13)) | ~l1_pre_topc(X14)) )),
% 3.96/0.90    inference(superposition,[],[f97,f261])).
% 3.96/0.90  fof(f261,plain,(
% 3.96/0.90    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.96/0.90    inference(subsumption_resolution,[],[f258,f85])).
% 3.96/0.90  fof(f258,plain,(
% 3.96/0.90    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.96/0.90    inference(duplicate_literal_removal,[],[f253])).
% 3.96/0.90  fof(f253,plain,(
% 3.96/0.90    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.96/0.90    inference(superposition,[],[f84,f99])).
% 3.96/0.90  fof(f99,plain,(
% 3.96/0.90    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f58])).
% 3.96/0.90  fof(f58,plain,(
% 3.96/0.90    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.96/0.90    inference(flattening,[],[f57])).
% 3.96/0.90  fof(f57,plain,(
% 3.96/0.90    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.96/0.90    inference(ennf_transformation,[],[f19])).
% 3.96/0.90  fof(f19,axiom,(
% 3.96/0.90    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.96/0.90  fof(f97,plain,(
% 3.96/0.90    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.96/0.90    inference(cnf_transformation,[],[f9])).
% 3.96/0.90  fof(f9,axiom,(
% 3.96/0.90    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.96/0.90  fof(f1494,plain,(
% 3.96/0.90    spl2_56 | ~spl2_3 | ~spl2_4),
% 3.96/0.90    inference(avatar_split_clause,[],[f1489,f123,f118,f1491])).
% 3.96/0.90  fof(f1489,plain,(
% 3.96/0.90    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl2_3 | ~spl2_4)),
% 3.96/0.90    inference(subsumption_resolution,[],[f1480,f125])).
% 3.96/0.90  fof(f1480,plain,(
% 3.96/0.90    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl2_3),
% 3.96/0.90    inference(resolution,[],[f554,f120])).
% 3.96/0.90  fof(f554,plain,(
% 3.96/0.90    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | r1_tarski(k1_tops_1(X5,X4),X4) | ~l1_pre_topc(X5)) )),
% 3.96/0.90    inference(superposition,[],[f141,f243])).
% 3.96/0.90  fof(f141,plain,(
% 3.96/0.90    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.96/0.90    inference(backward_demodulation,[],[f134,f94])).
% 3.96/0.90  fof(f134,plain,(
% 3.96/0.90    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 3.96/0.90    inference(resolution,[],[f88,f104])).
% 3.96/0.90  fof(f88,plain,(
% 3.96/0.90    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f68])).
% 3.96/0.90  fof(f580,plain,(
% 3.96/0.90    ~spl2_10 | spl2_2 | ~spl2_9),
% 3.96/0.90    inference(avatar_split_clause,[],[f579,f194,f112,f198])).
% 3.96/0.90  fof(f579,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl2_2 | ~spl2_9)),
% 3.96/0.90    inference(subsumption_resolution,[],[f578,f195])).
% 3.96/0.90  fof(f578,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_2),
% 3.96/0.90    inference(superposition,[],[f114,f74])).
% 3.96/0.90  fof(f114,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_2),
% 3.96/0.90    inference(avatar_component_clause,[],[f112])).
% 3.96/0.90  fof(f529,plain,(
% 3.96/0.90    ~spl2_3 | ~spl2_4 | spl2_9),
% 3.96/0.90    inference(avatar_contradiction_clause,[],[f528])).
% 3.96/0.90  fof(f528,plain,(
% 3.96/0.90    $false | (~spl2_3 | ~spl2_4 | spl2_9)),
% 3.96/0.90    inference(subsumption_resolution,[],[f527,f125])).
% 3.96/0.90  fof(f527,plain,(
% 3.96/0.90    ~l1_pre_topc(sK0) | (~spl2_3 | spl2_9)),
% 3.96/0.90    inference(subsumption_resolution,[],[f520,f120])).
% 3.96/0.90  fof(f520,plain,(
% 3.96/0.90    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_9),
% 3.96/0.90    inference(resolution,[],[f263,f196])).
% 3.96/0.90  fof(f196,plain,(
% 3.96/0.90    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_9),
% 3.96/0.90    inference(avatar_component_clause,[],[f194])).
% 3.96/0.90  fof(f470,plain,(
% 3.96/0.90    ~spl2_26 | spl2_24),
% 3.96/0.90    inference(avatar_split_clause,[],[f465,f453,f467])).
% 3.96/0.90  fof(f465,plain,(
% 3.96/0.90    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl2_24),
% 3.96/0.90    inference(resolution,[],[f455,f89])).
% 3.96/0.90  fof(f455,plain,(
% 3.96/0.90    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl2_24),
% 3.96/0.90    inference(avatar_component_clause,[],[f453])).
% 3.96/0.90  fof(f230,plain,(
% 3.96/0.90    spl2_13 | ~spl2_3 | ~spl2_4 | ~spl2_5),
% 3.96/0.90    inference(avatar_split_clause,[],[f225,f128,f123,f118,f227])).
% 3.96/0.90  fof(f227,plain,(
% 3.96/0.90    spl2_13 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_13])])).
% 3.96/0.90  fof(f128,plain,(
% 3.96/0.90    spl2_5 <=> v2_pre_topc(sK0)),
% 3.96/0.90    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).
% 3.96/0.90  fof(f225,plain,(
% 3.96/0.90    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl2_3 | ~spl2_4 | ~spl2_5)),
% 3.96/0.90    inference(subsumption_resolution,[],[f224,f130])).
% 3.96/0.90  fof(f130,plain,(
% 3.96/0.90    v2_pre_topc(sK0) | ~spl2_5),
% 3.96/0.90    inference(avatar_component_clause,[],[f128])).
% 3.96/0.90  fof(f224,plain,(
% 3.96/0.90    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl2_3 | ~spl2_4)),
% 3.96/0.90    inference(subsumption_resolution,[],[f222,f125])).
% 3.96/0.90  fof(f222,plain,(
% 3.96/0.90    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl2_3),
% 3.96/0.90    inference(resolution,[],[f86,f120])).
% 3.96/0.90  fof(f86,plain,(
% 3.96/0.90    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.96/0.90    inference(cnf_transformation,[],[f47])).
% 3.96/0.90  fof(f47,plain,(
% 3.96/0.90    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.96/0.90    inference(flattening,[],[f46])).
% 3.96/0.90  fof(f46,plain,(
% 3.96/0.90    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.96/0.90    inference(ennf_transformation,[],[f26])).
% 3.96/0.90  fof(f26,axiom,(
% 3.96/0.90    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.96/0.90  fof(f139,plain,(
% 3.96/0.90    spl2_6 | ~spl2_3),
% 3.96/0.90    inference(avatar_split_clause,[],[f133,f118,f136])).
% 3.96/0.90  fof(f133,plain,(
% 3.96/0.90    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl2_3),
% 3.96/0.90    inference(resolution,[],[f88,f120])).
% 3.96/0.90  fof(f131,plain,(
% 3.96/0.90    spl2_5),
% 3.96/0.90    inference(avatar_split_clause,[],[f69,f128])).
% 3.96/0.90  fof(f69,plain,(
% 3.96/0.90    v2_pre_topc(sK0)),
% 3.96/0.90    inference(cnf_transformation,[],[f65])).
% 3.96/0.90  fof(f65,plain,(
% 3.96/0.90    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.96/0.90    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f62,f64,f63])).
% 3.96/0.90  fof(f63,plain,(
% 3.96/0.90    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.96/0.90    introduced(choice_axiom,[])).
% 3.96/0.90  fof(f64,plain,(
% 3.96/0.90    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.96/0.90    introduced(choice_axiom,[])).
% 3.96/0.90  fof(f62,plain,(
% 3.96/0.90    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.96/0.90    inference(flattening,[],[f61])).
% 3.96/0.90  fof(f61,plain,(
% 3.96/0.90    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.96/0.90    inference(nnf_transformation,[],[f35])).
% 3.96/0.90  fof(f35,plain,(
% 3.96/0.90    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.96/0.90    inference(flattening,[],[f34])).
% 3.96/0.90  fof(f34,plain,(
% 3.96/0.90    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.96/0.90    inference(ennf_transformation,[],[f33])).
% 3.96/0.90  fof(f33,negated_conjecture,(
% 3.96/0.90    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.96/0.90    inference(negated_conjecture,[],[f32])).
% 3.96/0.90  fof(f32,conjecture,(
% 3.96/0.90    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.96/0.90    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 3.96/0.90  fof(f126,plain,(
% 3.96/0.90    spl2_4),
% 3.96/0.90    inference(avatar_split_clause,[],[f70,f123])).
% 3.96/0.90  fof(f70,plain,(
% 3.96/0.90    l1_pre_topc(sK0)),
% 3.96/0.90    inference(cnf_transformation,[],[f65])).
% 3.96/0.90  fof(f121,plain,(
% 3.96/0.90    spl2_3),
% 3.96/0.90    inference(avatar_split_clause,[],[f71,f118])).
% 3.96/0.90  fof(f71,plain,(
% 3.96/0.90    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.96/0.90    inference(cnf_transformation,[],[f65])).
% 3.96/0.90  fof(f116,plain,(
% 3.96/0.90    spl2_1 | spl2_2),
% 3.96/0.90    inference(avatar_split_clause,[],[f72,f112,f108])).
% 3.96/0.90  fof(f72,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.96/0.90    inference(cnf_transformation,[],[f65])).
% 3.96/0.90  fof(f115,plain,(
% 3.96/0.90    ~spl2_1 | ~spl2_2),
% 3.96/0.90    inference(avatar_split_clause,[],[f73,f112,f108])).
% 3.96/0.90  fof(f73,plain,(
% 3.96/0.90    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.96/0.90    inference(cnf_transformation,[],[f65])).
% 3.96/0.90  % SZS output end Proof for theBenchmark
% 3.96/0.90  % (8534)------------------------------
% 3.96/0.90  % (8534)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.96/0.90  % (8534)Termination reason: Refutation
% 3.96/0.90  
% 3.96/0.90  % (8534)Memory used [KB]: 8955
% 3.96/0.90  % (8534)Time elapsed: 0.474 s
% 3.96/0.90  % (8534)------------------------------
% 3.96/0.90  % (8534)------------------------------
% 3.96/0.90  % (8511)Success in time 0.536 s
%------------------------------------------------------------------------------
