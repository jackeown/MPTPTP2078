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
% DateTime   : Thu Dec  3 13:11:40 EST 2020

% Result     : Theorem 1.53s
% Output     : Refutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :  177 ( 313 expanded)
%              Number of leaves         :   40 ( 115 expanded)
%              Depth                    :   11
%              Number of atoms          :  530 (1016 expanded)
%              Number of equality atoms :   95 ( 205 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1948,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f100,f101,f106,f111,f116,f199,f218,f232,f322,f334,f336,f343,f446,f478,f495,f1028,f1656,f1800,f1929,f1947])).

fof(f1947,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1929,plain,(
    ~ spl3_75 ),
    inference(avatar_contradiction_clause,[],[f1893])).

fof(f1893,plain,
    ( $false
    | ~ spl3_75 ),
    inference(unit_resulting_resolution,[],[f90,f1088,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f1088,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f1087])).

fof(f1087,plain,
    ( spl3_75
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f90,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1800,plain,
    ( spl3_15
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_104 ),
    inference(avatar_split_clause,[],[f1799,f1653,f108,f103,f206])).

fof(f206,plain,
    ( spl3_15
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f103,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f108,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1653,plain,
    ( spl3_104
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).

fof(f1799,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_104 ),
    inference(subsumption_resolution,[],[f1798,f110])).

fof(f110,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1798,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_104 ),
    inference(subsumption_resolution,[],[f1780,f105])).

fof(f105,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f1780,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_104 ),
    inference(superposition,[],[f237,f1655])).

fof(f1655,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_104 ),
    inference(avatar_component_clause,[],[f1653])).

fof(f237,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f234])).

fof(f234,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f63,f70])).

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
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1656,plain,
    ( spl3_75
    | spl3_104
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f1651,f475,f443,f1653,f1087])).

fof(f443,plain,
    ( spl3_37
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f475,plain,
    ( spl3_38
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f1651,plain,
    ( ! [X18] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_37
    | ~ spl3_38 ),
    inference(subsumption_resolution,[],[f1630,f445])).

fof(f445,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f443])).

fof(f1630,plain,
    ( ! [X18] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_38 ),
    inference(superposition,[],[f575,f477])).

fof(f477,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f475])).

fof(f575,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f567,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f567,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f249,f63])).

fof(f249,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f245,f79])).

fof(f245,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f72,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f1028,plain,
    ( spl3_39
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1027,f108,f103,f492])).

fof(f492,plain,
    ( spl3_39
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f1027,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f1006,f110])).

fof(f1006,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f683,f105])).

fof(f683,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | r1_tarski(X4,k2_pre_topc(X5,X4))
      | ~ l1_pre_topc(X5) ) ),
    inference(superposition,[],[f128,f680])).

fof(f680,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f241,f277])).

fof(f277,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f274,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f274,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f71,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

fof(f241,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f240])).

fof(f240,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f87,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).

fof(f87,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f128,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(trivial_inequality_removal,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 != k1_xboole_0
      | r1_tarski(X0,k2_xboole_0(X0,X1)) ) ),
    inference(superposition,[],[f82,f85])).

fof(f85,plain,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

fof(f82,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) != k1_xboole_0
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f495,plain,
    ( ~ spl3_39
    | spl3_36 ),
    inference(avatar_split_clause,[],[f490,f439,f492])).

fof(f439,plain,
    ( spl3_36
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f490,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_36 ),
    inference(resolution,[],[f441,f78])).

fof(f441,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_36 ),
    inference(avatar_component_clause,[],[f439])).

fof(f478,plain,
    ( ~ spl3_36
    | spl3_38
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f467,f178,f475,f439])).

fof(f178,plain,
    ( spl3_11
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f467,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_11 ),
    inference(superposition,[],[f159,f180])).

fof(f180,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f178])).

fof(f159,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f155])).

fof(f155,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f67,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f446,plain,
    ( ~ spl3_36
    | spl3_37
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f437,f178,f443,f439])).

fof(f437,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_11 ),
    inference(superposition,[],[f158,f180])).

fof(f158,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f156])).

fof(f156,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f79,f68])).

fof(f343,plain,
    ( spl3_11
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f342,f165,f97,f178])).

fof(f97,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f165,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f342,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f338,f166])).

fof(f166,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f338,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f63,f98])).

fof(f98,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f336,plain,
    ( ~ spl3_14
    | spl3_15
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f335,f196,f206,f202])).

fof(f202,plain,
    ( spl3_14
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f196,plain,
    ( spl3_13
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f335,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_13 ),
    inference(resolution,[],[f198,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f198,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f196])).

fof(f334,plain,
    ( spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f333])).

fof(f333,plain,
    ( $false
    | spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f332,f110])).

fof(f332,plain,
    ( ~ l1_pre_topc(sK0)
    | spl3_2
    | ~ spl3_3
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f331,f105])).

fof(f331,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_2
    | ~ spl3_15 ),
    inference(subsumption_resolution,[],[f330,f99])).

fof(f99,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f97])).

fof(f330,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_15 ),
    inference(superposition,[],[f69,f208])).

fof(f208,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f206])).

fof(f322,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_14 ),
    inference(avatar_contradiction_clause,[],[f321])).

fof(f321,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | spl3_14 ),
    inference(unit_resulting_resolution,[],[f110,f90,f204,f105,f105,f94,f76])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
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

fof(f94,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f204,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl3_14 ),
    inference(avatar_component_clause,[],[f202])).

fof(f232,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f227,f113,f108,f103,f229])).

fof(f229,plain,
    ( spl3_16
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f113,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f227,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f226,f115])).

fof(f115,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f226,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f223,f110])).

fof(f223,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f75,f105])).

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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f218,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f216,f110])).

fof(f216,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f211,f105])).

fof(f211,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f73,f167])).

fof(f167,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f165])).

fof(f199,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f194,f108,f103,f196])).

fof(f194,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f192,f110])).

fof(f192,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f81,f105])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f116,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f58,f113])).

fof(f58,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).

fof(f49,plain,
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

fof(f50,plain,
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

fof(f48,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f24,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).

fof(f111,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f59,f108])).

fof(f59,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f60,f103])).

fof(f60,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f51])).

fof(f101,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f61,f97,f93])).

fof(f61,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).

fof(f100,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f62,f97,f93])).

fof(f62,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f51])).
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
% 0.14/0.34  % DateTime   : Tue Dec  1 19:25:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.48  % (18972)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.50  % (18975)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.51  % (18988)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.51  % (18998)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.51  % (18974)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (18970)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.51  % (18973)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.51  % (18991)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.52  % (19005)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.52  % (18983)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.53  % (18982)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.53  % (18980)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (18992)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.53  % (18989)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (18990)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.38/0.54  % (18993)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.38/0.54  % (18984)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 1.38/0.54  % (18978)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.38/0.54  % (18977)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.38/0.54  % (19000)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.38/0.55  % (18996)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.38/0.55  % (18976)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.38/0.55  % (18985)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.38/0.55  % (18979)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.38/0.55  % (18987)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.38/0.55  % (18981)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.38/0.56  % (18980)Refutation not found, incomplete strategy% (18980)------------------------------
% 1.38/0.56  % (18980)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.56  % (18980)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (18980)Memory used [KB]: 11001
% 1.38/0.56  % (18980)Time elapsed: 0.161 s
% 1.38/0.56  % (18980)------------------------------
% 1.38/0.56  % (18980)------------------------------
% 1.38/0.56  % (18986)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.53/0.56  % (18994)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.53/0.56  % (18971)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.53/0.57  % (18986)Refutation not found, incomplete strategy% (18986)------------------------------
% 1.53/0.57  % (18986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.57  % (18986)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.57  
% 1.53/0.57  % (18986)Memory used [KB]: 10746
% 1.53/0.57  % (18986)Time elapsed: 0.153 s
% 1.53/0.57  % (18986)------------------------------
% 1.53/0.57  % (18986)------------------------------
% 1.53/0.60  % (19003)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.53/0.62  % (19003)Refutation not found, incomplete strategy% (19003)------------------------------
% 1.53/0.62  % (19003)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.53/0.62  % (19003)Termination reason: Refutation not found, incomplete strategy
% 1.53/0.62  
% 1.53/0.62  % (19003)Memory used [KB]: 11001
% 1.53/0.62  % (19003)Time elapsed: 0.192 s
% 1.53/0.62  % (19003)------------------------------
% 1.53/0.62  % (19003)------------------------------
% 1.53/0.62  % (18991)Refutation found. Thanks to Tanya!
% 1.53/0.62  % SZS status Theorem for theBenchmark
% 2.09/0.64  % SZS output start Proof for theBenchmark
% 2.09/0.64  fof(f1948,plain,(
% 2.09/0.64    $false),
% 2.09/0.64    inference(avatar_sat_refutation,[],[f100,f101,f106,f111,f116,f199,f218,f232,f322,f334,f336,f343,f446,f478,f495,f1028,f1656,f1800,f1929,f1947])).
% 2.09/0.64  fof(f1947,plain,(
% 2.09/0.64    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.09/0.64    introduced(theory_tautology_sat_conflict,[])).
% 2.09/0.64  fof(f1929,plain,(
% 2.09/0.64    ~spl3_75),
% 2.09/0.64    inference(avatar_contradiction_clause,[],[f1893])).
% 2.09/0.64  fof(f1893,plain,(
% 2.09/0.64    $false | ~spl3_75),
% 2.09/0.64    inference(unit_resulting_resolution,[],[f90,f1088,f78])).
% 2.09/0.64  fof(f78,plain,(
% 2.09/0.64    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f54])).
% 2.09/0.64  fof(f54,plain,(
% 2.09/0.64    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.09/0.64    inference(nnf_transformation,[],[f16])).
% 2.09/0.64  fof(f16,axiom,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 2.09/0.64  fof(f1088,plain,(
% 2.09/0.64    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_75),
% 2.09/0.64    inference(avatar_component_clause,[],[f1087])).
% 2.09/0.64  fof(f1087,plain,(
% 2.09/0.64    spl3_75 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 2.09/0.64  fof(f90,plain,(
% 2.09/0.64    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.09/0.64    inference(equality_resolution,[],[f65])).
% 2.09/0.64  fof(f65,plain,(
% 2.09/0.64    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.09/0.64    inference(cnf_transformation,[],[f53])).
% 2.09/0.64  fof(f53,plain,(
% 2.09/0.64    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.09/0.64    inference(flattening,[],[f52])).
% 2.09/0.64  fof(f52,plain,(
% 2.09/0.64    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.09/0.64    inference(nnf_transformation,[],[f2])).
% 2.09/0.64  fof(f2,axiom,(
% 2.09/0.64    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.09/0.64  fof(f1800,plain,(
% 2.09/0.64    spl3_15 | ~spl3_3 | ~spl3_4 | ~spl3_104),
% 2.09/0.64    inference(avatar_split_clause,[],[f1799,f1653,f108,f103,f206])).
% 2.09/0.64  fof(f206,plain,(
% 2.09/0.64    spl3_15 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 2.09/0.64  fof(f103,plain,(
% 2.09/0.64    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.09/0.64  fof(f108,plain,(
% 2.09/0.64    spl3_4 <=> l1_pre_topc(sK0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.09/0.64  fof(f1653,plain,(
% 2.09/0.64    spl3_104 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_104])])).
% 2.09/0.64  fof(f1799,plain,(
% 2.09/0.64    sK1 = k1_tops_1(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_104)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1798,f110])).
% 2.09/0.64  fof(f110,plain,(
% 2.09/0.64    l1_pre_topc(sK0) | ~spl3_4),
% 2.09/0.64    inference(avatar_component_clause,[],[f108])).
% 2.09/0.64  fof(f1798,plain,(
% 2.09/0.64    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_104)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1780,f105])).
% 2.09/0.64  fof(f105,plain,(
% 2.09/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.09/0.64    inference(avatar_component_clause,[],[f103])).
% 2.09/0.64  fof(f1780,plain,(
% 2.09/0.64    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_104),
% 2.09/0.64    inference(superposition,[],[f237,f1655])).
% 2.09/0.64  fof(f1655,plain,(
% 2.09/0.64    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_104),
% 2.09/0.64    inference(avatar_component_clause,[],[f1653])).
% 2.09/0.64  fof(f237,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(duplicate_literal_removal,[],[f234])).
% 2.09/0.64  fof(f234,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(superposition,[],[f63,f70])).
% 2.09/0.64  fof(f70,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f32])).
% 2.09/0.64  fof(f32,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f23])).
% 2.09/0.64  fof(f23,axiom,(
% 2.09/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 2.09/0.64  fof(f63,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f28])).
% 2.09/0.64  fof(f28,plain,(
% 2.09/0.64    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f13])).
% 2.09/0.64  fof(f13,axiom,(
% 2.09/0.64    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.09/0.64  fof(f1656,plain,(
% 2.09/0.64    spl3_75 | spl3_104 | ~spl3_37 | ~spl3_38),
% 2.09/0.64    inference(avatar_split_clause,[],[f1651,f475,f443,f1653,f1087])).
% 2.09/0.64  fof(f443,plain,(
% 2.09/0.64    spl3_37 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.09/0.64  fof(f475,plain,(
% 2.09/0.64    spl3_38 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 2.09/0.64  fof(f1651,plain,(
% 2.09/0.64    ( ! [X18] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_37 | ~spl3_38)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1630,f445])).
% 2.09/0.64  fof(f445,plain,(
% 2.09/0.64    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_37),
% 2.09/0.64    inference(avatar_component_clause,[],[f443])).
% 2.09/0.64  fof(f1630,plain,(
% 2.09/0.64    ( ! [X18] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X18,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_38),
% 2.09/0.64    inference(superposition,[],[f575,f477])).
% 2.09/0.64  fof(f477,plain,(
% 2.09/0.64    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_38),
% 2.09/0.64    inference(avatar_component_clause,[],[f475])).
% 2.09/0.64  fof(f575,plain,(
% 2.09/0.64    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 2.09/0.64    inference(subsumption_resolution,[],[f567,f79])).
% 2.09/0.64  fof(f79,plain,(
% 2.09/0.64    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f42])).
% 2.09/0.64  fof(f42,plain,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f7])).
% 2.09/0.64  fof(f7,axiom,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.09/0.64  fof(f567,plain,(
% 2.09/0.64    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 2.09/0.64    inference(superposition,[],[f249,f63])).
% 2.09/0.64  fof(f249,plain,(
% 2.09/0.64    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 2.09/0.64    inference(subsumption_resolution,[],[f245,f79])).
% 2.09/0.64  fof(f245,plain,(
% 2.09/0.64    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 2.09/0.64    inference(superposition,[],[f72,f86])).
% 2.09/0.64  fof(f86,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f44])).
% 2.09/0.64  fof(f44,plain,(
% 2.09/0.64    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f10])).
% 2.09/0.64  fof(f10,axiom,(
% 2.09/0.64    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 2.09/0.64  fof(f72,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f34])).
% 2.09/0.64  fof(f34,plain,(
% 2.09/0.64    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f14])).
% 2.09/0.64  fof(f14,axiom,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 2.09/0.64  fof(f1028,plain,(
% 2.09/0.64    spl3_39 | ~spl3_3 | ~spl3_4),
% 2.09/0.64    inference(avatar_split_clause,[],[f1027,f108,f103,f492])).
% 2.09/0.64  fof(f492,plain,(
% 2.09/0.64    spl3_39 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 2.09/0.64  fof(f1027,plain,(
% 2.09/0.64    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 2.09/0.64    inference(subsumption_resolution,[],[f1006,f110])).
% 2.09/0.64  fof(f1006,plain,(
% 2.09/0.64    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 2.09/0.64    inference(resolution,[],[f683,f105])).
% 2.09/0.64  fof(f683,plain,(
% 2.09/0.64    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | r1_tarski(X4,k2_pre_topc(X5,X4)) | ~l1_pre_topc(X5)) )),
% 2.09/0.64    inference(superposition,[],[f128,f680])).
% 2.09/0.64  fof(f680,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(subsumption_resolution,[],[f241,f277])).
% 2.09/0.64  fof(f277,plain,(
% 2.09/0.64    ( ! [X2,X3] : (m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.09/0.64    inference(subsumption_resolution,[],[f274,f73])).
% 2.09/0.64  fof(f73,plain,(
% 2.09/0.64    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f36])).
% 2.09/0.64  fof(f36,plain,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.09/0.64    inference(flattening,[],[f35])).
% 2.09/0.64  fof(f35,plain,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f17])).
% 2.09/0.64  fof(f17,axiom,(
% 2.09/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.09/0.64  fof(f274,plain,(
% 2.09/0.64    ( ! [X2,X3] : (m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.09/0.64    inference(superposition,[],[f71,f69])).
% 2.09/0.64  fof(f69,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f31])).
% 2.09/0.64  fof(f31,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f19])).
% 2.09/0.64  fof(f19,axiom,(
% 2.09/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 2.09/0.64  fof(f71,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f33])).
% 2.09/0.64  fof(f33,plain,(
% 2.09/0.64    ! [X0,X1,X2] : (m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f8])).
% 2.09/0.64  fof(f8,axiom,(
% 2.09/0.64    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k7_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).
% 2.09/0.64  fof(f241,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(duplicate_literal_removal,[],[f240])).
% 2.09/0.64  fof(f240,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k2_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(superposition,[],[f87,f74])).
% 2.09/0.64  fof(f74,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f37])).
% 2.09/0.64  fof(f37,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f22])).
% 2.09/0.64  fof(f22,axiom,(
% 2.09/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 2.09/0.64  fof(f87,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f46])).
% 2.09/0.64  fof(f46,plain,(
% 2.09/0.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(flattening,[],[f45])).
% 2.09/0.64  fof(f45,plain,(
% 2.09/0.64    ! [X0,X1,X2] : (k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 2.09/0.64    inference(ennf_transformation,[],[f12])).
% 2.09/0.64  fof(f12,axiom,(
% 2.09/0.64    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k4_subset_1(X0,X1,X2) = k2_xboole_0(X1,X2))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 2.09/0.64  fof(f128,plain,(
% 2.09/0.64    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.09/0.64    inference(trivial_inequality_removal,[],[f127])).
% 2.09/0.64  fof(f127,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k1_xboole_0 != k1_xboole_0 | r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 2.09/0.64    inference(superposition,[],[f82,f85])).
% 2.09/0.64  fof(f85,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f5])).
% 2.09/0.64  fof(f5,axiom,(
% 2.09/0.64    ! [X0,X1] : k1_xboole_0 = k4_xboole_0(X0,k2_xboole_0(X0,X1))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).
% 2.09/0.64  fof(f82,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) != k1_xboole_0 | r1_tarski(X0,X1)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f57])).
% 2.09/0.64  fof(f57,plain,(
% 2.09/0.64    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 2.09/0.64    inference(nnf_transformation,[],[f3])).
% 2.09/0.64  fof(f3,axiom,(
% 2.09/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).
% 2.09/0.64  fof(f495,plain,(
% 2.09/0.64    ~spl3_39 | spl3_36),
% 2.09/0.64    inference(avatar_split_clause,[],[f490,f439,f492])).
% 2.09/0.64  fof(f439,plain,(
% 2.09/0.64    spl3_36 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.09/0.64  fof(f490,plain,(
% 2.09/0.64    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_36),
% 2.09/0.64    inference(resolution,[],[f441,f78])).
% 2.09/0.64  fof(f441,plain,(
% 2.09/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_36),
% 2.09/0.64    inference(avatar_component_clause,[],[f439])).
% 2.09/0.64  fof(f478,plain,(
% 2.09/0.64    ~spl3_36 | spl3_38 | ~spl3_11),
% 2.09/0.64    inference(avatar_split_clause,[],[f467,f178,f475,f439])).
% 2.09/0.64  fof(f178,plain,(
% 2.09/0.64    spl3_11 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.09/0.64  fof(f467,plain,(
% 2.09/0.64    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_11),
% 2.09/0.64    inference(superposition,[],[f159,f180])).
% 2.09/0.64  fof(f180,plain,(
% 2.09/0.64    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_11),
% 2.09/0.64    inference(avatar_component_clause,[],[f178])).
% 2.09/0.64  fof(f159,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(duplicate_literal_removal,[],[f155])).
% 2.09/0.64  fof(f155,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(superposition,[],[f67,f68])).
% 2.09/0.64  fof(f68,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f30])).
% 2.09/0.64  fof(f30,plain,(
% 2.09/0.64    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f6])).
% 2.09/0.64  fof(f6,axiom,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 2.09/0.64  fof(f67,plain,(
% 2.09/0.64    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.09/0.64    inference(cnf_transformation,[],[f29])).
% 2.09/0.64  fof(f29,plain,(
% 2.09/0.64    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f11])).
% 2.09/0.64  fof(f11,axiom,(
% 2.09/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.09/0.64  fof(f446,plain,(
% 2.09/0.64    ~spl3_36 | spl3_37 | ~spl3_11),
% 2.09/0.64    inference(avatar_split_clause,[],[f437,f178,f443,f439])).
% 2.09/0.64  fof(f437,plain,(
% 2.09/0.64    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_11),
% 2.09/0.64    inference(superposition,[],[f158,f180])).
% 2.09/0.64  fof(f158,plain,(
% 2.09/0.64    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 2.09/0.64    inference(duplicate_literal_removal,[],[f156])).
% 2.09/0.64  fof(f156,plain,(
% 2.09/0.64    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 2.09/0.64    inference(superposition,[],[f79,f68])).
% 2.09/0.64  fof(f343,plain,(
% 2.09/0.64    spl3_11 | ~spl3_2 | ~spl3_9),
% 2.09/0.64    inference(avatar_split_clause,[],[f342,f165,f97,f178])).
% 2.09/0.64  fof(f97,plain,(
% 2.09/0.64    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.09/0.64  fof(f165,plain,(
% 2.09/0.64    spl3_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 2.09/0.64  fof(f342,plain,(
% 2.09/0.64    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_9)),
% 2.09/0.64    inference(subsumption_resolution,[],[f338,f166])).
% 2.09/0.64  fof(f166,plain,(
% 2.09/0.64    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 2.09/0.64    inference(avatar_component_clause,[],[f165])).
% 2.09/0.64  fof(f338,plain,(
% 2.09/0.64    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.09/0.64    inference(superposition,[],[f63,f98])).
% 2.09/0.64  fof(f98,plain,(
% 2.09/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 2.09/0.64    inference(avatar_component_clause,[],[f97])).
% 2.09/0.64  fof(f336,plain,(
% 2.09/0.64    ~spl3_14 | spl3_15 | ~spl3_13),
% 2.09/0.64    inference(avatar_split_clause,[],[f335,f196,f206,f202])).
% 2.09/0.64  fof(f202,plain,(
% 2.09/0.64    spl3_14 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 2.09/0.64  fof(f196,plain,(
% 2.09/0.64    spl3_13 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.09/0.64  fof(f335,plain,(
% 2.09/0.64    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_13),
% 2.09/0.64    inference(resolution,[],[f198,f66])).
% 2.09/0.64  fof(f66,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f53])).
% 2.09/0.64  fof(f198,plain,(
% 2.09/0.64    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_13),
% 2.09/0.64    inference(avatar_component_clause,[],[f196])).
% 2.09/0.64  fof(f334,plain,(
% 2.09/0.64    spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_15),
% 2.09/0.64    inference(avatar_contradiction_clause,[],[f333])).
% 2.09/0.64  fof(f333,plain,(
% 2.09/0.64    $false | (spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_15)),
% 2.09/0.64    inference(subsumption_resolution,[],[f332,f110])).
% 2.09/0.64  fof(f332,plain,(
% 2.09/0.64    ~l1_pre_topc(sK0) | (spl3_2 | ~spl3_3 | ~spl3_15)),
% 2.09/0.64    inference(subsumption_resolution,[],[f331,f105])).
% 2.09/0.64  fof(f331,plain,(
% 2.09/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_2 | ~spl3_15)),
% 2.09/0.64    inference(subsumption_resolution,[],[f330,f99])).
% 2.09/0.64  fof(f99,plain,(
% 2.09/0.64    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 2.09/0.64    inference(avatar_component_clause,[],[f97])).
% 2.09/0.64  fof(f330,plain,(
% 2.09/0.64    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_15),
% 2.09/0.64    inference(superposition,[],[f69,f208])).
% 2.09/0.64  fof(f208,plain,(
% 2.09/0.64    sK1 = k1_tops_1(sK0,sK1) | ~spl3_15),
% 2.09/0.64    inference(avatar_component_clause,[],[f206])).
% 2.09/0.64  fof(f322,plain,(
% 2.09/0.64    ~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_14),
% 2.09/0.64    inference(avatar_contradiction_clause,[],[f321])).
% 2.09/0.64  fof(f321,plain,(
% 2.09/0.64    $false | (~spl3_1 | ~spl3_3 | ~spl3_4 | spl3_14)),
% 2.09/0.64    inference(unit_resulting_resolution,[],[f110,f90,f204,f105,f105,f94,f76])).
% 2.09/0.64  fof(f76,plain,(
% 2.09/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f41])).
% 2.09/0.64  fof(f41,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.64    inference(flattening,[],[f40])).
% 2.09/0.64  fof(f40,plain,(
% 2.09/0.64    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.64    inference(ennf_transformation,[],[f21])).
% 2.09/0.64  fof(f21,axiom,(
% 2.09/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.09/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 2.09/0.64  fof(f94,plain,(
% 2.09/0.64    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 2.09/0.64    inference(avatar_component_clause,[],[f93])).
% 2.09/0.64  fof(f93,plain,(
% 2.09/0.64    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.09/0.64  fof(f204,plain,(
% 2.09/0.64    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl3_14),
% 2.09/0.64    inference(avatar_component_clause,[],[f202])).
% 2.09/0.64  fof(f232,plain,(
% 2.09/0.64    spl3_16 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 2.09/0.64    inference(avatar_split_clause,[],[f227,f113,f108,f103,f229])).
% 2.09/0.64  fof(f229,plain,(
% 2.09/0.64    spl3_16 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.09/0.64  fof(f113,plain,(
% 2.09/0.64    spl3_5 <=> v2_pre_topc(sK0)),
% 2.09/0.64    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.09/0.64  fof(f227,plain,(
% 2.09/0.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.09/0.64    inference(subsumption_resolution,[],[f226,f115])).
% 2.09/0.64  fof(f115,plain,(
% 2.09/0.64    v2_pre_topc(sK0) | ~spl3_5),
% 2.09/0.64    inference(avatar_component_clause,[],[f113])).
% 2.09/0.64  fof(f226,plain,(
% 2.09/0.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 2.09/0.64    inference(subsumption_resolution,[],[f223,f110])).
% 2.09/0.64  fof(f223,plain,(
% 2.09/0.64    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 2.09/0.64    inference(resolution,[],[f75,f105])).
% 2.09/0.64  fof(f75,plain,(
% 2.09/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.09/0.64    inference(cnf_transformation,[],[f39])).
% 2.09/0.64  fof(f39,plain,(
% 2.09/0.64    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.09/0.64    inference(flattening,[],[f38])).
% 2.09/0.64  fof(f38,plain,(
% 2.09/0.64    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.09/0.64    inference(ennf_transformation,[],[f18])).
% 2.09/0.65  fof(f18,axiom,(
% 2.09/0.65    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.09/0.65  fof(f218,plain,(
% 2.09/0.65    ~spl3_3 | ~spl3_4 | spl3_9),
% 2.09/0.65    inference(avatar_contradiction_clause,[],[f217])).
% 2.09/0.65  fof(f217,plain,(
% 2.09/0.65    $false | (~spl3_3 | ~spl3_4 | spl3_9)),
% 2.09/0.65    inference(subsumption_resolution,[],[f216,f110])).
% 2.09/0.65  fof(f216,plain,(
% 2.09/0.65    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_9)),
% 2.09/0.65    inference(subsumption_resolution,[],[f211,f105])).
% 2.09/0.65  fof(f211,plain,(
% 2.09/0.65    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 2.09/0.65    inference(resolution,[],[f73,f167])).
% 2.09/0.65  fof(f167,plain,(
% 2.09/0.65    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 2.09/0.65    inference(avatar_component_clause,[],[f165])).
% 2.09/0.65  fof(f199,plain,(
% 2.09/0.65    spl3_13 | ~spl3_3 | ~spl3_4),
% 2.09/0.65    inference(avatar_split_clause,[],[f194,f108,f103,f196])).
% 2.09/0.65  fof(f194,plain,(
% 2.09/0.65    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 2.09/0.65    inference(subsumption_resolution,[],[f192,f110])).
% 2.09/0.65  fof(f192,plain,(
% 2.09/0.65    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 2.09/0.65    inference(resolution,[],[f81,f105])).
% 2.09/0.65  fof(f81,plain,(
% 2.09/0.65    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(k1_tops_1(X0,X1),X1) | ~l1_pre_topc(X0)) )),
% 2.09/0.65    inference(cnf_transformation,[],[f43])).
% 2.09/0.65  fof(f43,plain,(
% 2.09/0.65    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.09/0.65    inference(ennf_transformation,[],[f20])).
% 2.09/0.65  fof(f20,axiom,(
% 2.09/0.65    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 2.09/0.65  fof(f116,plain,(
% 2.09/0.65    spl3_5),
% 2.09/0.65    inference(avatar_split_clause,[],[f58,f113])).
% 2.09/0.65  fof(f58,plain,(
% 2.09/0.65    v2_pre_topc(sK0)),
% 2.09/0.65    inference(cnf_transformation,[],[f51])).
% 2.09/0.65  fof(f51,plain,(
% 2.09/0.65    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.09/0.65    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f48,f50,f49])).
% 2.09/0.65  fof(f49,plain,(
% 2.09/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.09/0.65    introduced(choice_axiom,[])).
% 2.09/0.65  fof(f50,plain,(
% 2.09/0.65    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.09/0.65    introduced(choice_axiom,[])).
% 2.09/0.65  fof(f48,plain,(
% 2.09/0.65    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.09/0.65    inference(flattening,[],[f47])).
% 2.09/0.65  fof(f47,plain,(
% 2.09/0.65    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.09/0.65    inference(nnf_transformation,[],[f27])).
% 2.09/0.65  fof(f27,plain,(
% 2.09/0.65    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.09/0.65    inference(flattening,[],[f26])).
% 2.09/0.65  fof(f26,plain,(
% 2.09/0.65    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.09/0.65    inference(ennf_transformation,[],[f25])).
% 2.09/0.65  fof(f25,negated_conjecture,(
% 2.09/0.65    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.09/0.65    inference(negated_conjecture,[],[f24])).
% 2.09/0.65  fof(f24,conjecture,(
% 2.09/0.65    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.09/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 2.09/0.65  fof(f111,plain,(
% 2.09/0.65    spl3_4),
% 2.09/0.65    inference(avatar_split_clause,[],[f59,f108])).
% 2.09/0.65  fof(f59,plain,(
% 2.09/0.65    l1_pre_topc(sK0)),
% 2.09/0.65    inference(cnf_transformation,[],[f51])).
% 2.09/0.65  fof(f106,plain,(
% 2.09/0.65    spl3_3),
% 2.09/0.65    inference(avatar_split_clause,[],[f60,f103])).
% 2.09/0.65  fof(f60,plain,(
% 2.09/0.65    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.09/0.65    inference(cnf_transformation,[],[f51])).
% 2.09/0.65  fof(f101,plain,(
% 2.09/0.65    spl3_1 | spl3_2),
% 2.09/0.65    inference(avatar_split_clause,[],[f61,f97,f93])).
% 2.09/0.65  fof(f61,plain,(
% 2.09/0.65    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.09/0.65    inference(cnf_transformation,[],[f51])).
% 2.09/0.65  fof(f100,plain,(
% 2.09/0.65    ~spl3_1 | ~spl3_2),
% 2.09/0.65    inference(avatar_split_clause,[],[f62,f97,f93])).
% 2.09/0.65  fof(f62,plain,(
% 2.09/0.65    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.09/0.65    inference(cnf_transformation,[],[f51])).
% 2.09/0.65  % SZS output end Proof for theBenchmark
% 2.09/0.65  % (18991)------------------------------
% 2.09/0.65  % (18991)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.09/0.65  % (18991)Termination reason: Refutation
% 2.09/0.65  
% 2.09/0.65  % (18991)Memory used [KB]: 7803
% 2.09/0.65  % (18991)Time elapsed: 0.203 s
% 2.09/0.65  % (18991)------------------------------
% 2.09/0.65  % (18991)------------------------------
% 2.09/0.65  % (18968)Success in time 0.287 s
%------------------------------------------------------------------------------
