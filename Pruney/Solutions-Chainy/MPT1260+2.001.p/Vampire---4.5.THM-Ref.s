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
% DateTime   : Thu Dec  3 13:11:32 EST 2020

% Result     : Theorem 11.98s
% Output     : Refutation 11.98s
% Verified   : 
% Statistics : Number of formulae       :  197 ( 379 expanded)
%              Number of leaves         :   42 ( 131 expanded)
%              Depth                    :   13
%              Number of atoms          :  591 (1193 expanded)
%              Number of equality atoms :   98 ( 230 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9602,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f150,f151,f156,f161,f166,f336,f1220,f1308,f1632,f1953,f3265,f5362,f5433,f5438,f5463,f6784,f7951,f7964,f8072,f9524,f9594])).

fof(f9594,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_50
    | ~ spl4_106 ),
    inference(avatar_contradiction_clause,[],[f9593])).

fof(f9593,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_50
    | ~ spl4_106 ),
    inference(subsumption_resolution,[],[f9592,f160])).

fof(f160,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f158])).

fof(f158,plain,
    ( spl4_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f9592,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_50
    | ~ spl4_106 ),
    inference(subsumption_resolution,[],[f9591,f155])).

fof(f155,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f9591,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_50
    | ~ spl4_106 ),
    inference(subsumption_resolution,[],[f9541,f2139])).

fof(f2139,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl4_50 ),
    inference(avatar_component_clause,[],[f2138])).

fof(f2138,plain,
    ( spl4_50
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).

fof(f9541,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_106 ),
    inference(superposition,[],[f372,f9523])).

fof(f9523,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl4_106 ),
    inference(avatar_component_clause,[],[f9521])).

fof(f9521,plain,
    ( spl4_106
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).

fof(f372,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f371])).

fof(f371,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f91,f102])).

fof(f102,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f35,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f9524,plain,
    ( spl4_93
    | spl4_106
    | ~ spl4_31
    | ~ spl4_32 ),
    inference(avatar_split_clause,[],[f9519,f1310,f1305,f9521,f8010])).

fof(f8010,plain,
    ( spl4_93
  <=> ! [X3] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).

fof(f1305,plain,
    ( spl4_31
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f1310,plain,
    ( spl4_32
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).

fof(f9519,plain,
    ( ! [X21] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl4_31
    | ~ spl4_32 ),
    inference(subsumption_resolution,[],[f9461,f1307])).

fof(f1307,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_31 ),
    inference(avatar_component_clause,[],[f1305])).

fof(f9461,plain,
    ( ! [X21] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X21,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl4_32 ),
    inference(superposition,[],[f1529,f1312])).

fof(f1312,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl4_32 ),
    inference(avatar_component_clause,[],[f1310])).

fof(f1529,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f1524,f110])).

fof(f110,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f1524,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f411,f91])).

fof(f411,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f407,f110])).

fof(f407,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f100,f132])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f8072,plain,(
    ~ spl4_93 ),
    inference(avatar_contradiction_clause,[],[f8041])).

fof(f8041,plain,
    ( $false
    | ~ spl4_93 ),
    inference(unit_resulting_resolution,[],[f823,f111,f8011,f134])).

fof(f134,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f66])).

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f8011,plain,
    ( ! [X3] : ~ m1_subset_1(X3,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_93 ),
    inference(avatar_component_clause,[],[f8010])).

fof(f111,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

fof(f823,plain,(
    ! [X7] : m1_subset_1(X7,k1_zfmisc_1(X7)) ),
    inference(subsumption_resolution,[],[f820,f111])).

fof(f820,plain,(
    ! [X7] :
      ( m1_subset_1(X7,k1_zfmisc_1(X7))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7)) ) ),
    inference(superposition,[],[f294,f117])).

fof(f117,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

fof(f294,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(duplicate_literal_removal,[],[f292])).

fof(f292,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f110,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f7964,plain,
    ( ~ spl4_30
    | spl4_32
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f5478,f311,f1310,f1301])).

fof(f1301,plain,
    ( spl4_30
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f311,plain,
    ( spl4_11
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f5478,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_11 ),
    inference(superposition,[],[f295,f313])).

fof(f313,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f311])).

fof(f295,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f291])).

fof(f291,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f95,f96])).

fof(f95,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f7951,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_39 ),
    inference(avatar_contradiction_clause,[],[f7931])).

fof(f7931,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_39 ),
    inference(unit_resulting_resolution,[],[f160,f137,f1631,f155,f1423])).

fof(f1423,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X10)))
      | ~ r1_tarski(X11,X9)
      | r1_tarski(X11,k2_pre_topc(X10,X9))
      | ~ l1_pre_topc(X10) ) ),
    inference(superposition,[],[f264,f394])).

fof(f394,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f391,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).

fof(f391,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f386])).

fof(f386,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f103,f133])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f103,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).

fof(f264,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(subsumption_resolution,[],[f259,f170])).

fof(f170,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(resolution,[],[f108,f111])).

fof(f108,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f259,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k1_xboole_0,X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(X0,X1) ) ),
    inference(superposition,[],[f112,f115])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ( k4_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | k4_xboole_0(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k1_xboole_0
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(k4_xboole_0(X0,X1),X2)
      | r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,k2_xboole_0(X1,X2))
      | ~ r1_tarski(k4_xboole_0(X0,X1),X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( r1_tarski(k4_xboole_0(X0,X1),X2)
     => r1_tarski(X0,k2_xboole_0(X1,X2)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

fof(f1631,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl4_39 ),
    inference(avatar_component_clause,[],[f1629])).

fof(f1629,plain,
    ( spl4_39
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).

fof(f137,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f6784,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f5463,plain,
    ( spl4_11
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f5462,f307,f147,f311])).

fof(f147,plain,
    ( spl4_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f307,plain,
    ( spl4_10
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f5462,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f5459,f308])).

fof(f308,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f307])).

fof(f5459,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2 ),
    inference(superposition,[],[f91,f148])).

fof(f148,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f5438,plain,
    ( ~ spl4_46
    | spl4_50
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f5369,f2134,f2138,f1948])).

fof(f1948,plain,
    ( spl4_46
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f2134,plain,
    ( spl4_49
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f5369,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_49 ),
    inference(resolution,[],[f2135,f94])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f2135,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f2134])).

fof(f5433,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_11
    | ~ spl4_50 ),
    inference(avatar_contradiction_clause,[],[f5432])).

fof(f5432,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_11
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f5431,f160])).

fof(f5431,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_11
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f5430,f155])).

fof(f5430,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_11
    | ~ spl4_50 ),
    inference(subsumption_resolution,[],[f5427,f312])).

fof(f312,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f311])).

fof(f5427,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_50 ),
    inference(superposition,[],[f1792,f2140])).

fof(f2140,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl4_50 ),
    inference(avatar_component_clause,[],[f2138])).

fof(f1792,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f413,f396])).

fof(f396,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f389,f104])).

fof(f389,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f388])).

fof(f388,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f134,f103])).

fof(f413,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f101,f91])).

fof(f101,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f5362,plain,
    ( spl4_49
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f5361,f158,f153,f2134])).

fof(f5361,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f5352,f160])).

fof(f5352,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f1351,f155])).

fof(f1351,plain,(
    ! [X10,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X10)))
      | r1_tarski(k1_tops_1(X10,X9),X9)
      | ~ l1_pre_topc(X10) ) ),
    inference(superposition,[],[f116,f372])).

fof(f116,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f3265,plain,
    ( ~ spl4_11
    | spl4_2
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f3264,f307,f147,f311])).

fof(f3264,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl4_2
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f3263,f308])).

fof(f3263,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_2 ),
    inference(superposition,[],[f149,f91])).

fof(f149,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl4_2 ),
    inference(avatar_component_clause,[],[f147])).

fof(f1953,plain,
    ( spl4_46
    | ~ spl4_1
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f1952,f158,f153,f143,f1948])).

fof(f143,plain,
    ( spl4_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1952,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f446,f137])).

fof(f446,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ r1_tarski(sK1,sK1)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(resolution,[],[f430,f155])).

fof(f430,plain,
    ( ! [X15] :
        ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X15,sK0)
        | r1_tarski(X15,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X15,sK1) )
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f428,f160])).

fof(f428,plain,
    ( ! [X15] :
        ( ~ r1_tarski(X15,sK1)
        | ~ v3_pre_topc(X15,sK0)
        | r1_tarski(X15,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl4_3 ),
    inference(resolution,[],[f106,f155])).

fof(f106,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | ~ v3_pre_topc(X1,X0)
      | r1_tarski(X1,k1_tops_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(X1,k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f32,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( r1_tarski(X1,X2)
                  & v3_pre_topc(X1,X0) )
               => r1_tarski(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f1632,plain,
    ( ~ spl4_39
    | spl4_30 ),
    inference(avatar_split_clause,[],[f1627,f1301,f1629])).

fof(f1627,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl4_30 ),
    inference(resolution,[],[f1303,f109])).

fof(f109,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f1303,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl4_30 ),
    inference(avatar_component_clause,[],[f1301])).

fof(f1308,plain,
    ( ~ spl4_30
    | spl4_31
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f1253,f311,f1305,f1301])).

fof(f1253,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl4_11 ),
    inference(superposition,[],[f294,f313])).

fof(f1220,plain,
    ( ~ spl4_3
    | ~ spl4_4
    | spl4_10 ),
    inference(avatar_contradiction_clause,[],[f1219])).

fof(f1219,plain,
    ( $false
    | ~ spl4_3
    | ~ spl4_4
    | spl4_10 ),
    inference(subsumption_resolution,[],[f1218,f160])).

fof(f1218,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl4_3
    | spl4_10 ),
    inference(subsumption_resolution,[],[f1209,f155])).

fof(f1209,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl4_10 ),
    inference(resolution,[],[f396,f309])).

fof(f309,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f307])).

fof(f336,plain,
    ( spl4_13
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f331,f163,f158,f153,f333])).

fof(f333,plain,
    ( spl4_13
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f163,plain,
    ( spl4_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f331,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_3
    | ~ spl4_4
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f330,f165])).

fof(f165,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f163])).

fof(f330,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f328,f160])).

fof(f328,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f105,f155])).

fof(f105,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f166,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f86,f163])).

fof(f86,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f72,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f69,f71,f70])).

fof(f70,plain,
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

fof(f71,plain,
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

fof(f69,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f68])).

fof(f68,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f37,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f36])).

fof(f36,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f161,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f87,f158])).

fof(f87,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f156,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f88,f153])).

fof(f88,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f72])).

fof(f151,plain,
    ( spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f89,f147,f143])).

fof(f89,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).

fof(f150,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f90,f147,f143])).

fof(f90,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f72])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:47:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.49  % (23989)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.19/0.49  % (23970)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.19/0.49  % (23981)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.19/0.50  % (23966)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.19/0.51  % (23975)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.19/0.51  % (23965)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.23/0.51  % (23974)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.23/0.51  % (23971)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 1.23/0.51  % (23986)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.23/0.52  % (23988)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.23/0.52  % (23987)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.23/0.52  % (23993)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.23/0.52  % (23967)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 1.23/0.52  % (23994)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.23/0.53  % (23979)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.23/0.53  % (23969)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.23/0.53  % (23968)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.23/0.53  % (23982)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.35/0.53  % (23991)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.35/0.53  % (23972)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.35/0.54  % (23985)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 1.35/0.54  % (23983)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.35/0.54  % (23977)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.35/0.54  % (23990)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.35/0.54  % (23978)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.35/0.54  % (23995)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.35/0.54  % (23976)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 1.35/0.54  % (23984)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 1.35/0.54  % (23973)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.35/0.55  % (23992)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 3.43/0.82  % (23970)Time limit reached!
% 3.43/0.82  % (23970)------------------------------
% 3.43/0.82  % (23970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.43/0.82  % (23970)Termination reason: Time limit
% 3.43/0.82  
% 3.43/0.82  % (23970)Memory used [KB]: 8315
% 3.43/0.82  % (23970)Time elapsed: 0.418 s
% 3.43/0.82  % (23970)------------------------------
% 3.43/0.82  % (23970)------------------------------
% 3.69/0.90  % (23983)Time limit reached!
% 3.69/0.90  % (23983)------------------------------
% 3.69/0.90  % (23983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.90  % (23983)Termination reason: Time limit
% 3.69/0.90  % (23983)Termination phase: Saturation
% 3.69/0.90  
% 3.69/0.90  % (23983)Memory used [KB]: 13176
% 3.69/0.90  % (23983)Time elapsed: 0.500 s
% 3.69/0.90  % (23983)------------------------------
% 3.69/0.90  % (23983)------------------------------
% 3.69/0.91  % (23975)Time limit reached!
% 3.69/0.91  % (23975)------------------------------
% 3.69/0.91  % (23975)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.91  % (23975)Termination reason: Time limit
% 3.69/0.91  
% 3.69/0.91  % (23975)Memory used [KB]: 12920
% 3.69/0.91  % (23975)Time elapsed: 0.505 s
% 3.69/0.91  % (23975)------------------------------
% 3.69/0.91  % (23975)------------------------------
% 3.69/0.91  % (23977)Time limit reached!
% 3.69/0.91  % (23977)------------------------------
% 3.69/0.91  % (23977)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.91  % (23977)Termination reason: Time limit
% 3.69/0.91  
% 3.69/0.91  % (23977)Memory used [KB]: 8571
% 3.69/0.91  % (23977)Time elapsed: 0.510 s
% 3.69/0.91  % (23977)------------------------------
% 3.69/0.91  % (23977)------------------------------
% 3.69/0.91  % (23965)Time limit reached!
% 3.69/0.91  % (23965)------------------------------
% 3.69/0.91  % (23965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.69/0.91  % (23965)Termination reason: Time limit
% 3.69/0.91  
% 3.69/0.91  % (23965)Memory used [KB]: 3709
% 3.69/0.91  % (23965)Time elapsed: 0.507 s
% 3.69/0.91  % (23965)------------------------------
% 3.69/0.91  % (23965)------------------------------
% 4.43/0.93  % (23966)Time limit reached!
% 4.43/0.93  % (23966)------------------------------
% 4.43/0.93  % (23966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.43/0.93  % (23966)Termination reason: Time limit
% 4.43/0.93  % (23966)Termination phase: Saturation
% 4.43/0.93  
% 4.43/0.93  % (23966)Memory used [KB]: 8059
% 4.43/0.93  % (23966)Time elapsed: 0.500 s
% 4.43/0.93  % (23966)------------------------------
% 4.43/0.93  % (23966)------------------------------
% 4.43/0.96  % (24007)lrs+11_1_av=off:bsr=on:gsp=input_only:gs=on:lcm=predicate:nm=64:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=all:sp=occurrence:updr=off_245 on theBenchmark
% 4.89/1.00  % (23982)Time limit reached!
% 4.89/1.00  % (23982)------------------------------
% 4.89/1.00  % (23982)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.00  % (23982)Termination reason: Time limit
% 4.89/1.00  % (23982)Termination phase: Saturation
% 4.89/1.00  
% 4.89/1.00  % (23982)Memory used [KB]: 16247
% 4.89/1.00  % (23982)Time elapsed: 0.600 s
% 4.89/1.00  % (23982)------------------------------
% 4.89/1.00  % (23982)------------------------------
% 4.89/1.02  % (23994)Time limit reached!
% 4.89/1.02  % (23994)------------------------------
% 4.89/1.02  % (23994)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.02  % (23994)Termination reason: Time limit
% 4.89/1.02  
% 4.89/1.02  % (23994)Memory used [KB]: 8571
% 4.89/1.02  % (23994)Time elapsed: 0.623 s
% 4.89/1.02  % (23994)------------------------------
% 4.89/1.02  % (23994)------------------------------
% 4.89/1.02  % (23972)Time limit reached!
% 4.89/1.02  % (23972)------------------------------
% 4.89/1.02  % (23972)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.89/1.02  % (23972)Termination reason: Time limit
% 4.89/1.02  
% 4.89/1.02  % (23972)Memory used [KB]: 10874
% 4.89/1.02  % (23972)Time elapsed: 0.627 s
% 4.89/1.02  % (23972)------------------------------
% 4.89/1.02  % (23972)------------------------------
% 4.89/1.04  % (24008)lrs+1010_4_awrs=decay:awrsf=64:add=large:afp=4000:afq=1.2:amm=off:anc=none:bs=on:bsr=on:fde=none:gs=on:gsaa=from_current:gsem=on:lma=on:newcnf=on:nwc=1.7:sas=z3:stl=30:sd=10:ss=axioms:s2a=on:st=1.2:sp=frequency:updr=off:uhcvi=on_20 on theBenchmark
% 4.89/1.04  % (24009)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_12 on theBenchmark
% 4.89/1.04  % (24011)dis+1010_8_acc=model:afp=4000:afq=1.0:anc=none:bd=off:bs=unit_only:bce=on:cond=fast:fde=unused:gs=on:gsem=off:lma=on:nm=0:nwc=4:sd=3:ss=axioms:st=2.0:sac=on:sp=occurrence:urr=ec_only_1 on theBenchmark
% 4.89/1.05  % (24010)ott+11_20_afp=10000:afq=1.1:anc=none:bs=unit_only:bsr=on:bce=on:fsr=off:gs=on:gsem=on:nwc=2.5:sas=z3:sp=occurrence:updr=off:uhcvi=on_1 on theBenchmark
% 4.89/1.06  % (24012)lrs+11_3:2_add=large:afp=1000:afq=1.1:amm=sco:anc=none:bd=off:er=filter:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:sas=z3:stl=30:sp=occurrence:urr=on:updr=off_100 on theBenchmark
% 5.97/1.14  % (24013)dis+10_4_av=off:bsr=on:cond=fast:er=filter:fde=none:gsp=input_only:lcm=reverse:lma=on:nwc=4:sp=occurrence:urr=on_8 on theBenchmark
% 6.20/1.16  % (24014)lrs+10_12_add=off:afp=100000:afq=1.4:amm=sco:anc=none:cond=on:lma=on:nm=64:nwc=1.3:stl=30:sac=on:urr=on_41 on theBenchmark
% 6.20/1.16  % (24015)lrs+10_8:1_av=off:bs=unit_only:cond=on:fde=unused:irw=on:lcm=predicate:lma=on:nm=64:nwc=1.2:stl=30:sos=all:sp=reverse_arity:urr=on:updr=off_12 on theBenchmark
% 6.20/1.21  % (23987)Time limit reached!
% 6.20/1.21  % (23987)------------------------------
% 6.20/1.21  % (23987)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.20/1.21  % (23987)Termination reason: Time limit
% 6.20/1.21  % (23987)Termination phase: Saturation
% 6.20/1.21  
% 6.20/1.21  % (23987)Memory used [KB]: 4861
% 6.20/1.21  % (23987)Time elapsed: 0.800 s
% 6.20/1.21  % (23987)------------------------------
% 6.20/1.21  % (23987)------------------------------
% 7.71/1.36  % (24016)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_143 on theBenchmark
% 7.88/1.37  % (24010)Time limit reached!
% 7.88/1.37  % (24010)------------------------------
% 7.88/1.37  % (24010)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.88/1.37  % (24010)Termination reason: Time limit
% 7.88/1.37  % (24010)Termination phase: Saturation
% 7.88/1.37  
% 7.88/1.37  % (24010)Memory used [KB]: 7803
% 7.88/1.37  % (24010)Time elapsed: 0.439 s
% 7.88/1.37  % (24010)------------------------------
% 7.88/1.37  % (24010)------------------------------
% 7.88/1.41  % (23967)Time limit reached!
% 7.88/1.41  % (23967)------------------------------
% 7.88/1.41  % (23967)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.88/1.41  % (23967)Termination reason: Time limit
% 7.88/1.41  
% 7.88/1.41  % (23967)Memory used [KB]: 21364
% 7.88/1.41  % (23967)Time elapsed: 1.005 s
% 7.88/1.41  % (23967)------------------------------
% 7.88/1.41  % (23967)------------------------------
% 9.01/1.54  % (24018)dis+1010_3:1_av=off:irw=on:nm=32:nwc=1:sos=all:urr=ec_only:updr=off_96 on theBenchmark
% 9.01/1.55  % (24017)lrs+10_8:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lcm=predicate:lwlo=on:nm=64:nwc=1:stl=30:sos=all:updr=off_78 on theBenchmark
% 9.33/1.62  % (23988)Time limit reached!
% 9.33/1.62  % (23988)------------------------------
% 9.33/1.62  % (23988)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.33/1.62  % (23988)Termination reason: Time limit
% 9.33/1.62  % (23988)Termination phase: Saturation
% 9.33/1.62  
% 9.33/1.62  % (23988)Memory used [KB]: 16886
% 9.33/1.62  % (23988)Time elapsed: 1.200 s
% 9.33/1.62  % (23988)------------------------------
% 9.33/1.62  % (23988)------------------------------
% 9.33/1.65  % (23992)Time limit reached!
% 9.33/1.65  % (23992)------------------------------
% 9.33/1.65  % (23992)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.33/1.65  % (23992)Termination reason: Time limit
% 9.33/1.65  
% 9.33/1.65  % (23992)Memory used [KB]: 22771
% 9.33/1.65  % (23992)Time elapsed: 1.225 s
% 9.33/1.65  % (23992)------------------------------
% 9.33/1.65  % (23992)------------------------------
% 10.55/1.74  % (23981)Time limit reached!
% 10.55/1.74  % (23981)------------------------------
% 10.55/1.74  % (23981)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 10.55/1.74  % (23981)Termination reason: Time limit
% 10.55/1.74  % (23981)Termination phase: Saturation
% 10.55/1.74  
% 10.55/1.74  % (23981)Memory used [KB]: 16247
% 10.55/1.74  % (23981)Time elapsed: 1.300 s
% 10.55/1.74  % (23981)------------------------------
% 10.55/1.74  % (23981)------------------------------
% 11.00/1.75  % (24020)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_113 on theBenchmark
% 11.00/1.76  % (23990)Time limit reached!
% 11.00/1.76  % (23990)------------------------------
% 11.00/1.76  % (23990)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.00/1.76  % (23990)Termination reason: Time limit
% 11.00/1.76  
% 11.00/1.76  % (23990)Memory used [KB]: 22515
% 11.00/1.76  % (23990)Time elapsed: 1.340 s
% 11.00/1.76  % (23990)------------------------------
% 11.00/1.76  % (23990)------------------------------
% 11.00/1.77  % (24011)Time limit reached!
% 11.00/1.77  % (24011)------------------------------
% 11.00/1.77  % (24011)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.00/1.77  % (24011)Termination reason: Time limit
% 11.00/1.77  
% 11.00/1.77  % (24011)Memory used [KB]: 13176
% 11.00/1.77  % (24011)Time elapsed: 0.839 s
% 11.00/1.77  % (24011)------------------------------
% 11.00/1.77  % (24011)------------------------------
% 11.00/1.79  % (24019)dis+1011_5_add=off:afr=on:afp=10000:afq=1.1:amm=off:anc=none:cond=on:fsr=off:nm=32:nwc=1:sas=z3:sd=3:ss=axioms:st=2.0:sp=occurrence:updr=off_2 on theBenchmark
% 11.67/1.89  % (24021)lrs+2_2_aac=none:afr=on:afp=1000:afq=1.1:amm=sco:anc=all:bd=off:bce=on:cond=on:gs=on:gsaa=from_current:nm=2:nwc=2.5:stl=30:sac=on:urr=on_26 on theBenchmark
% 11.98/1.92  % (24023)dis+11_2_av=off:cond=fast:ep=RST:fsr=off:lma=on:nm=16:nwc=1.2:sp=occurrence:updr=off_1 on theBenchmark
% 11.98/1.93  % (24009)Refutation found. Thanks to Tanya!
% 11.98/1.93  % SZS status Theorem for theBenchmark
% 11.98/1.93  % SZS output start Proof for theBenchmark
% 11.98/1.93  fof(f9602,plain,(
% 11.98/1.93    $false),
% 11.98/1.93    inference(avatar_sat_refutation,[],[f150,f151,f156,f161,f166,f336,f1220,f1308,f1632,f1953,f3265,f5362,f5433,f5438,f5463,f6784,f7951,f7964,f8072,f9524,f9594])).
% 11.98/1.93  fof(f9594,plain,(
% 11.98/1.93    ~spl4_3 | ~spl4_4 | spl4_50 | ~spl4_106),
% 11.98/1.93    inference(avatar_contradiction_clause,[],[f9593])).
% 11.98/1.93  fof(f9593,plain,(
% 11.98/1.93    $false | (~spl4_3 | ~spl4_4 | spl4_50 | ~spl4_106)),
% 11.98/1.93    inference(subsumption_resolution,[],[f9592,f160])).
% 11.98/1.93  fof(f160,plain,(
% 11.98/1.93    l1_pre_topc(sK0) | ~spl4_4),
% 11.98/1.93    inference(avatar_component_clause,[],[f158])).
% 11.98/1.93  fof(f158,plain,(
% 11.98/1.93    spl4_4 <=> l1_pre_topc(sK0)),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 11.98/1.93  fof(f9592,plain,(
% 11.98/1.93    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_50 | ~spl4_106)),
% 11.98/1.93    inference(subsumption_resolution,[],[f9591,f155])).
% 11.98/1.93  fof(f155,plain,(
% 11.98/1.93    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 11.98/1.93    inference(avatar_component_clause,[],[f153])).
% 11.98/1.93  fof(f153,plain,(
% 11.98/1.93    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 11.98/1.93  fof(f9591,plain,(
% 11.98/1.93    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_50 | ~spl4_106)),
% 11.98/1.93    inference(subsumption_resolution,[],[f9541,f2139])).
% 11.98/1.93  fof(f2139,plain,(
% 11.98/1.93    sK1 != k1_tops_1(sK0,sK1) | spl4_50),
% 11.98/1.93    inference(avatar_component_clause,[],[f2138])).
% 11.98/1.93  fof(f2138,plain,(
% 11.98/1.93    spl4_50 <=> sK1 = k1_tops_1(sK0,sK1)),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_50])])).
% 11.98/1.93  fof(f9541,plain,(
% 11.98/1.93    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_106),
% 11.98/1.93    inference(superposition,[],[f372,f9523])).
% 11.98/1.93  fof(f9523,plain,(
% 11.98/1.93    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl4_106),
% 11.98/1.93    inference(avatar_component_clause,[],[f9521])).
% 11.98/1.93  fof(f9521,plain,(
% 11.98/1.93    spl4_106 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_106])])).
% 11.98/1.93  fof(f372,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.98/1.93    inference(duplicate_literal_removal,[],[f371])).
% 11.98/1.93  fof(f371,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.98/1.93    inference(superposition,[],[f91,f102])).
% 11.98/1.93  fof(f102,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f46])).
% 11.98/1.93  fof(f46,plain,(
% 11.98/1.93    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.98/1.93    inference(ennf_transformation,[],[f35])).
% 11.98/1.93  fof(f35,axiom,(
% 11.98/1.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 11.98/1.93  fof(f91,plain,(
% 11.98/1.93    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f40])).
% 11.98/1.93  fof(f40,plain,(
% 11.98/1.93    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/1.93    inference(ennf_transformation,[],[f22])).
% 11.98/1.93  fof(f22,axiom,(
% 11.98/1.93    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 11.98/1.93  fof(f9524,plain,(
% 11.98/1.93    spl4_93 | spl4_106 | ~spl4_31 | ~spl4_32),
% 11.98/1.93    inference(avatar_split_clause,[],[f9519,f1310,f1305,f9521,f8010])).
% 11.98/1.93  fof(f8010,plain,(
% 11.98/1.93    spl4_93 <=> ! [X3] : ~m1_subset_1(X3,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_93])])).
% 11.98/1.93  fof(f1305,plain,(
% 11.98/1.93    spl4_31 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 11.98/1.93  fof(f1310,plain,(
% 11.98/1.93    spl4_32 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_32])])).
% 11.98/1.93  fof(f9519,plain,(
% 11.98/1.93    ( ! [X21] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X21,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl4_31 | ~spl4_32)),
% 11.98/1.93    inference(subsumption_resolution,[],[f9461,f1307])).
% 11.98/1.93  fof(f1307,plain,(
% 11.98/1.93    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl4_31),
% 11.98/1.93    inference(avatar_component_clause,[],[f1305])).
% 11.98/1.93  fof(f9461,plain,(
% 11.98/1.93    ( ! [X21] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X21,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl4_32),
% 11.98/1.93    inference(superposition,[],[f1529,f1312])).
% 11.98/1.93  fof(f1312,plain,(
% 11.98/1.93    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl4_32),
% 11.98/1.93    inference(avatar_component_clause,[],[f1310])).
% 11.98/1.93  fof(f1529,plain,(
% 11.98/1.93    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 11.98/1.93    inference(subsumption_resolution,[],[f1524,f110])).
% 11.98/1.93  fof(f110,plain,(
% 11.98/1.93    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f56])).
% 11.98/1.93  fof(f56,plain,(
% 11.98/1.93    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/1.93    inference(ennf_transformation,[],[f17])).
% 11.98/1.93  fof(f17,axiom,(
% 11.98/1.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 11.98/1.93  fof(f1524,plain,(
% 11.98/1.93    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 11.98/1.93    inference(superposition,[],[f411,f91])).
% 11.98/1.93  fof(f411,plain,(
% 11.98/1.93    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 11.98/1.93    inference(subsumption_resolution,[],[f407,f110])).
% 11.98/1.93  fof(f407,plain,(
% 11.98/1.93    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 11.98/1.93    inference(superposition,[],[f100,f132])).
% 11.98/1.93  fof(f132,plain,(
% 11.98/1.93    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f63])).
% 11.98/1.93  fof(f63,plain,(
% 11.98/1.93    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 11.98/1.93    inference(ennf_transformation,[],[f19])).
% 11.98/1.93  fof(f19,axiom,(
% 11.98/1.93    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 11.98/1.93  fof(f100,plain,(
% 11.98/1.93    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f44])).
% 11.98/1.93  fof(f44,plain,(
% 11.98/1.93    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/1.93    inference(ennf_transformation,[],[f23])).
% 11.98/1.93  fof(f23,axiom,(
% 11.98/1.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 11.98/1.93  fof(f8072,plain,(
% 11.98/1.93    ~spl4_93),
% 11.98/1.93    inference(avatar_contradiction_clause,[],[f8041])).
% 11.98/1.93  fof(f8041,plain,(
% 11.98/1.93    $false | ~spl4_93),
% 11.98/1.93    inference(unit_resulting_resolution,[],[f823,f111,f8011,f134])).
% 11.98/1.93  fof(f134,plain,(
% 11.98/1.93    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f67])).
% 11.98/1.93  fof(f67,plain,(
% 11.98/1.93    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/1.93    inference(flattening,[],[f66])).
% 11.98/1.93  fof(f66,plain,(
% 11.98/1.93    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.98/1.93    inference(ennf_transformation,[],[f18])).
% 11.98/1.93  fof(f18,axiom,(
% 11.98/1.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 11.98/1.93  fof(f8011,plain,(
% 11.98/1.93    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl4_93),
% 11.98/1.93    inference(avatar_component_clause,[],[f8010])).
% 11.98/1.93  fof(f111,plain,(
% 11.98/1.93    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f24])).
% 11.98/1.93  fof(f24,axiom,(
% 11.98/1.93    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).
% 11.98/1.93  fof(f823,plain,(
% 11.98/1.93    ( ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X7))) )),
% 11.98/1.93    inference(subsumption_resolution,[],[f820,f111])).
% 11.98/1.93  fof(f820,plain,(
% 11.98/1.93    ( ! [X7] : (m1_subset_1(X7,k1_zfmisc_1(X7)) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(X7))) )),
% 11.98/1.93    inference(superposition,[],[f294,f117])).
% 11.98/1.93  fof(f117,plain,(
% 11.98/1.93    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 11.98/1.93    inference(cnf_transformation,[],[f9])).
% 11.98/1.93  fof(f9,axiom,(
% 11.98/1.93    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).
% 11.98/1.93  fof(f294,plain,(
% 11.98/1.93    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 11.98/1.93    inference(duplicate_literal_removal,[],[f292])).
% 11.98/1.93  fof(f292,plain,(
% 11.98/1.93    ( ! [X2,X3] : (m1_subset_1(k4_xboole_0(X2,X3),k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X3,k1_zfmisc_1(X2))) )),
% 11.98/1.93    inference(superposition,[],[f110,f96])).
% 11.98/1.93  fof(f96,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f42])).
% 11.98/1.93  fof(f42,plain,(
% 11.98/1.93    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/1.93    inference(ennf_transformation,[],[f16])).
% 11.98/1.93  fof(f16,axiom,(
% 11.98/1.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 11.98/1.93  fof(f7964,plain,(
% 11.98/1.93    ~spl4_30 | spl4_32 | ~spl4_11),
% 11.98/1.93    inference(avatar_split_clause,[],[f5478,f311,f1310,f1301])).
% 11.98/1.93  fof(f1301,plain,(
% 11.98/1.93    spl4_30 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 11.98/1.93  fof(f311,plain,(
% 11.98/1.93    spl4_11 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 11.98/1.93  fof(f5478,plain,(
% 11.98/1.93    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl4_11),
% 11.98/1.93    inference(superposition,[],[f295,f313])).
% 11.98/1.93  fof(f313,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl4_11),
% 11.98/1.93    inference(avatar_component_clause,[],[f311])).
% 11.98/1.93  fof(f295,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(duplicate_literal_removal,[],[f291])).
% 11.98/1.93  fof(f291,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(superposition,[],[f95,f96])).
% 11.98/1.93  fof(f95,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f41])).
% 11.98/1.93  fof(f41,plain,(
% 11.98/1.93    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/1.93    inference(ennf_transformation,[],[f20])).
% 11.98/1.93  fof(f20,axiom,(
% 11.98/1.93    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 11.98/1.93  fof(f7951,plain,(
% 11.98/1.93    ~spl4_3 | ~spl4_4 | spl4_39),
% 11.98/1.93    inference(avatar_contradiction_clause,[],[f7931])).
% 11.98/1.93  fof(f7931,plain,(
% 11.98/1.93    $false | (~spl4_3 | ~spl4_4 | spl4_39)),
% 11.98/1.93    inference(unit_resulting_resolution,[],[f160,f137,f1631,f155,f1423])).
% 11.98/1.93  fof(f1423,plain,(
% 11.98/1.93    ( ! [X10,X11,X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X10))) | ~r1_tarski(X11,X9) | r1_tarski(X11,k2_pre_topc(X10,X9)) | ~l1_pre_topc(X10)) )),
% 11.98/1.93    inference(superposition,[],[f264,f394])).
% 11.98/1.93  fof(f394,plain,(
% 11.98/1.93    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 11.98/1.93    inference(subsumption_resolution,[],[f391,f104])).
% 11.98/1.93  fof(f104,plain,(
% 11.98/1.93    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f49])).
% 11.98/1.93  fof(f49,plain,(
% 11.98/1.93    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 11.98/1.93    inference(flattening,[],[f48])).
% 11.98/1.93  fof(f48,plain,(
% 11.98/1.93    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 11.98/1.93    inference(ennf_transformation,[],[f29])).
% 11.98/1.93  fof(f29,axiom,(
% 11.98/1.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 11.98/1.93  fof(f391,plain,(
% 11.98/1.93    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 11.98/1.93    inference(duplicate_literal_removal,[],[f386])).
% 11.98/1.93  fof(f386,plain,(
% 11.98/1.93    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 11.98/1.93    inference(superposition,[],[f103,f133])).
% 11.98/1.93  fof(f133,plain,(
% 11.98/1.93    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f65])).
% 11.98/1.93  fof(f65,plain,(
% 11.98/1.93    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 11.98/1.93    inference(flattening,[],[f64])).
% 11.98/1.93  fof(f64,plain,(
% 11.98/1.93    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 11.98/1.93    inference(ennf_transformation,[],[f21])).
% 11.98/1.93  fof(f21,axiom,(
% 11.98/1.93    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 11.98/1.93  fof(f103,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f47])).
% 11.98/1.93  fof(f47,plain,(
% 11.98/1.93    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.98/1.93    inference(ennf_transformation,[],[f34])).
% 11.98/1.93  fof(f34,axiom,(
% 11.98/1.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_1)).
% 11.98/1.93  fof(f264,plain,(
% 11.98/1.93    ( ! [X2,X0,X1] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 11.98/1.93    inference(subsumption_resolution,[],[f259,f170])).
% 11.98/1.93  fof(f170,plain,(
% 11.98/1.93    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 11.98/1.93    inference(resolution,[],[f108,f111])).
% 11.98/1.93  fof(f108,plain,(
% 11.98/1.93    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f75])).
% 11.98/1.93  fof(f75,plain,(
% 11.98/1.93    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.98/1.93    inference(nnf_transformation,[],[f26])).
% 11.98/1.93  fof(f26,axiom,(
% 11.98/1.93    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 11.98/1.93  fof(f259,plain,(
% 11.98/1.93    ( ! [X2,X0,X1] : (~r1_tarski(k1_xboole_0,X2) | r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(X0,X1)) )),
% 11.98/1.93    inference(superposition,[],[f112,f115])).
% 11.98/1.93  fof(f115,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f76])).
% 11.98/1.93  fof(f76,plain,(
% 11.98/1.93    ! [X0,X1] : ((k4_xboole_0(X0,X1) = k1_xboole_0 | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | k4_xboole_0(X0,X1) != k1_xboole_0))),
% 11.98/1.93    inference(nnf_transformation,[],[f5])).
% 11.98/1.93  fof(f5,axiom,(
% 11.98/1.93    ! [X0,X1] : (k4_xboole_0(X0,X1) = k1_xboole_0 <=> r1_tarski(X0,X1))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).
% 11.98/1.93  fof(f112,plain,(
% 11.98/1.93    ( ! [X2,X0,X1] : (~r1_tarski(k4_xboole_0(X0,X1),X2) | r1_tarski(X0,k2_xboole_0(X1,X2))) )),
% 11.98/1.93    inference(cnf_transformation,[],[f57])).
% 11.98/1.93  fof(f57,plain,(
% 11.98/1.93    ! [X0,X1,X2] : (r1_tarski(X0,k2_xboole_0(X1,X2)) | ~r1_tarski(k4_xboole_0(X0,X1),X2))),
% 11.98/1.93    inference(ennf_transformation,[],[f11])).
% 11.98/1.93  fof(f11,axiom,(
% 11.98/1.93    ! [X0,X1,X2] : (r1_tarski(k4_xboole_0(X0,X1),X2) => r1_tarski(X0,k2_xboole_0(X1,X2)))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).
% 11.98/1.93  fof(f1631,plain,(
% 11.98/1.93    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl4_39),
% 11.98/1.93    inference(avatar_component_clause,[],[f1629])).
% 11.98/1.93  fof(f1629,plain,(
% 11.98/1.93    spl4_39 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_39])])).
% 11.98/1.93  fof(f137,plain,(
% 11.98/1.93    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.98/1.93    inference(equality_resolution,[],[f93])).
% 11.98/1.93  fof(f93,plain,(
% 11.98/1.93    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 11.98/1.93    inference(cnf_transformation,[],[f74])).
% 11.98/1.93  fof(f74,plain,(
% 11.98/1.93    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.98/1.93    inference(flattening,[],[f73])).
% 11.98/1.93  fof(f73,plain,(
% 11.98/1.93    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.98/1.93    inference(nnf_transformation,[],[f4])).
% 11.98/1.93  fof(f4,axiom,(
% 11.98/1.93    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 11.98/1.93  fof(f6784,plain,(
% 11.98/1.93    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 11.98/1.93    introduced(theory_tautology_sat_conflict,[])).
% 11.98/1.93  fof(f5463,plain,(
% 11.98/1.93    spl4_11 | ~spl4_2 | ~spl4_10),
% 11.98/1.93    inference(avatar_split_clause,[],[f5462,f307,f147,f311])).
% 11.98/1.93  fof(f147,plain,(
% 11.98/1.93    spl4_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 11.98/1.93  fof(f307,plain,(
% 11.98/1.93    spl4_10 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 11.98/1.93  fof(f5462,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl4_2 | ~spl4_10)),
% 11.98/1.93    inference(subsumption_resolution,[],[f5459,f308])).
% 11.98/1.93  fof(f308,plain,(
% 11.98/1.93    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_10),
% 11.98/1.93    inference(avatar_component_clause,[],[f307])).
% 11.98/1.93  fof(f5459,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_2),
% 11.98/1.93    inference(superposition,[],[f91,f148])).
% 11.98/1.93  fof(f148,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl4_2),
% 11.98/1.93    inference(avatar_component_clause,[],[f147])).
% 11.98/1.93  fof(f5438,plain,(
% 11.98/1.93    ~spl4_46 | spl4_50 | ~spl4_49),
% 11.98/1.93    inference(avatar_split_clause,[],[f5369,f2134,f2138,f1948])).
% 11.98/1.93  fof(f1948,plain,(
% 11.98/1.93    spl4_46 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 11.98/1.93  fof(f2134,plain,(
% 11.98/1.93    spl4_49 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 11.98/1.93  fof(f5369,plain,(
% 11.98/1.93    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl4_49),
% 11.98/1.93    inference(resolution,[],[f2135,f94])).
% 11.98/1.93  fof(f94,plain,(
% 11.98/1.93    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f74])).
% 11.98/1.93  fof(f2135,plain,(
% 11.98/1.93    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_49),
% 11.98/1.93    inference(avatar_component_clause,[],[f2134])).
% 11.98/1.93  fof(f5433,plain,(
% 11.98/1.93    ~spl4_3 | ~spl4_4 | spl4_11 | ~spl4_50),
% 11.98/1.93    inference(avatar_contradiction_clause,[],[f5432])).
% 11.98/1.93  fof(f5432,plain,(
% 11.98/1.93    $false | (~spl4_3 | ~spl4_4 | spl4_11 | ~spl4_50)),
% 11.98/1.93    inference(subsumption_resolution,[],[f5431,f160])).
% 11.98/1.93  fof(f5431,plain,(
% 11.98/1.93    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_11 | ~spl4_50)),
% 11.98/1.93    inference(subsumption_resolution,[],[f5430,f155])).
% 11.98/1.93  fof(f5430,plain,(
% 11.98/1.93    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl4_11 | ~spl4_50)),
% 11.98/1.93    inference(subsumption_resolution,[],[f5427,f312])).
% 11.98/1.93  fof(f312,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl4_11),
% 11.98/1.93    inference(avatar_component_clause,[],[f311])).
% 11.98/1.93  fof(f5427,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_50),
% 11.98/1.93    inference(superposition,[],[f1792,f2140])).
% 11.98/1.93  fof(f2140,plain,(
% 11.98/1.93    sK1 = k1_tops_1(sK0,sK1) | ~spl4_50),
% 11.98/1.93    inference(avatar_component_clause,[],[f2138])).
% 11.98/1.93  fof(f1792,plain,(
% 11.98/1.93    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 11.98/1.93    inference(subsumption_resolution,[],[f413,f396])).
% 11.98/1.93  fof(f396,plain,(
% 11.98/1.93    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 11.98/1.93    inference(subsumption_resolution,[],[f389,f104])).
% 11.98/1.93  fof(f389,plain,(
% 11.98/1.93    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 11.98/1.93    inference(duplicate_literal_removal,[],[f388])).
% 11.98/1.93  fof(f388,plain,(
% 11.98/1.93    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 11.98/1.93    inference(superposition,[],[f134,f103])).
% 11.98/1.93  fof(f413,plain,(
% 11.98/1.93    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 11.98/1.93    inference(superposition,[],[f101,f91])).
% 11.98/1.93  fof(f101,plain,(
% 11.98/1.93    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f45])).
% 11.98/1.93  fof(f45,plain,(
% 11.98/1.93    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.98/1.93    inference(ennf_transformation,[],[f31])).
% 11.98/1.93  fof(f31,axiom,(
% 11.98/1.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 11.98/1.93  fof(f5362,plain,(
% 11.98/1.93    spl4_49 | ~spl4_3 | ~spl4_4),
% 11.98/1.93    inference(avatar_split_clause,[],[f5361,f158,f153,f2134])).
% 11.98/1.93  fof(f5361,plain,(
% 11.98/1.93    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl4_3 | ~spl4_4)),
% 11.98/1.93    inference(subsumption_resolution,[],[f5352,f160])).
% 11.98/1.93  fof(f5352,plain,(
% 11.98/1.93    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl4_3),
% 11.98/1.93    inference(resolution,[],[f1351,f155])).
% 11.98/1.93  fof(f1351,plain,(
% 11.98/1.93    ( ! [X10,X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(X10))) | r1_tarski(k1_tops_1(X10,X9),X9) | ~l1_pre_topc(X10)) )),
% 11.98/1.93    inference(superposition,[],[f116,f372])).
% 11.98/1.93  fof(f116,plain,(
% 11.98/1.93    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f8])).
% 11.98/1.93  fof(f8,axiom,(
% 11.98/1.93    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).
% 11.98/1.93  fof(f3265,plain,(
% 11.98/1.93    ~spl4_11 | spl4_2 | ~spl4_10),
% 11.98/1.93    inference(avatar_split_clause,[],[f3264,f307,f147,f311])).
% 11.98/1.93  fof(f3264,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl4_2 | ~spl4_10)),
% 11.98/1.93    inference(subsumption_resolution,[],[f3263,f308])).
% 11.98/1.93  fof(f3263,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_2),
% 11.98/1.93    inference(superposition,[],[f149,f91])).
% 11.98/1.93  fof(f149,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl4_2),
% 11.98/1.93    inference(avatar_component_clause,[],[f147])).
% 11.98/1.93  fof(f1953,plain,(
% 11.98/1.93    spl4_46 | ~spl4_1 | ~spl4_3 | ~spl4_4),
% 11.98/1.93    inference(avatar_split_clause,[],[f1952,f158,f153,f143,f1948])).
% 11.98/1.93  fof(f143,plain,(
% 11.98/1.93    spl4_1 <=> v3_pre_topc(sK1,sK0)),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 11.98/1.93  fof(f1952,plain,(
% 11.98/1.93    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | (~spl4_3 | ~spl4_4)),
% 11.98/1.93    inference(subsumption_resolution,[],[f446,f137])).
% 11.98/1.93  fof(f446,plain,(
% 11.98/1.93    ~v3_pre_topc(sK1,sK0) | r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK1,sK1) | (~spl4_3 | ~spl4_4)),
% 11.98/1.93    inference(resolution,[],[f430,f155])).
% 11.98/1.93  fof(f430,plain,(
% 11.98/1.93    ( ! [X15] : (~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X15,sK0) | r1_tarski(X15,k1_tops_1(sK0,sK1)) | ~r1_tarski(X15,sK1)) ) | (~spl4_3 | ~spl4_4)),
% 11.98/1.93    inference(subsumption_resolution,[],[f428,f160])).
% 11.98/1.93  fof(f428,plain,(
% 11.98/1.93    ( ! [X15] : (~r1_tarski(X15,sK1) | ~v3_pre_topc(X15,sK0) | r1_tarski(X15,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl4_3),
% 11.98/1.93    inference(resolution,[],[f106,f155])).
% 11.98/1.93  fof(f106,plain,(
% 11.98/1.93    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f53])).
% 11.98/1.93  fof(f53,plain,(
% 11.98/1.93    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.98/1.93    inference(flattening,[],[f52])).
% 11.98/1.93  fof(f52,plain,(
% 11.98/1.93    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 11.98/1.93    inference(ennf_transformation,[],[f32])).
% 11.98/1.93  fof(f32,axiom,(
% 11.98/1.93    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 11.98/1.93  fof(f1632,plain,(
% 11.98/1.93    ~spl4_39 | spl4_30),
% 11.98/1.93    inference(avatar_split_clause,[],[f1627,f1301,f1629])).
% 11.98/1.93  fof(f1627,plain,(
% 11.98/1.93    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl4_30),
% 11.98/1.93    inference(resolution,[],[f1303,f109])).
% 11.98/1.93  fof(f109,plain,(
% 11.98/1.93    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f75])).
% 11.98/1.93  fof(f1303,plain,(
% 11.98/1.93    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl4_30),
% 11.98/1.93    inference(avatar_component_clause,[],[f1301])).
% 11.98/1.93  fof(f1308,plain,(
% 11.98/1.93    ~spl4_30 | spl4_31 | ~spl4_11),
% 11.98/1.93    inference(avatar_split_clause,[],[f1253,f311,f1305,f1301])).
% 11.98/1.93  fof(f1253,plain,(
% 11.98/1.93    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl4_11),
% 11.98/1.93    inference(superposition,[],[f294,f313])).
% 11.98/1.93  fof(f1220,plain,(
% 11.98/1.93    ~spl4_3 | ~spl4_4 | spl4_10),
% 11.98/1.93    inference(avatar_contradiction_clause,[],[f1219])).
% 11.98/1.93  fof(f1219,plain,(
% 11.98/1.93    $false | (~spl4_3 | ~spl4_4 | spl4_10)),
% 11.98/1.93    inference(subsumption_resolution,[],[f1218,f160])).
% 11.98/1.93  fof(f1218,plain,(
% 11.98/1.93    ~l1_pre_topc(sK0) | (~spl4_3 | spl4_10)),
% 11.98/1.93    inference(subsumption_resolution,[],[f1209,f155])).
% 11.98/1.93  fof(f1209,plain,(
% 11.98/1.93    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl4_10),
% 11.98/1.93    inference(resolution,[],[f396,f309])).
% 11.98/1.93  fof(f309,plain,(
% 11.98/1.93    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl4_10),
% 11.98/1.93    inference(avatar_component_clause,[],[f307])).
% 11.98/1.93  fof(f336,plain,(
% 11.98/1.93    spl4_13 | ~spl4_3 | ~spl4_4 | ~spl4_5),
% 11.98/1.93    inference(avatar_split_clause,[],[f331,f163,f158,f153,f333])).
% 11.98/1.93  fof(f333,plain,(
% 11.98/1.93    spl4_13 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 11.98/1.93  fof(f163,plain,(
% 11.98/1.93    spl4_5 <=> v2_pre_topc(sK0)),
% 11.98/1.93    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 11.98/1.93  fof(f331,plain,(
% 11.98/1.93    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl4_3 | ~spl4_4 | ~spl4_5)),
% 11.98/1.93    inference(subsumption_resolution,[],[f330,f165])).
% 11.98/1.93  fof(f165,plain,(
% 11.98/1.93    v2_pre_topc(sK0) | ~spl4_5),
% 11.98/1.93    inference(avatar_component_clause,[],[f163])).
% 11.98/1.93  fof(f330,plain,(
% 11.98/1.93    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl4_3 | ~spl4_4)),
% 11.98/1.93    inference(subsumption_resolution,[],[f328,f160])).
% 11.98/1.93  fof(f328,plain,(
% 11.98/1.93    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl4_3),
% 11.98/1.93    inference(resolution,[],[f105,f155])).
% 11.98/1.93  fof(f105,plain,(
% 11.98/1.93    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 11.98/1.93    inference(cnf_transformation,[],[f51])).
% 11.98/1.93  fof(f51,plain,(
% 11.98/1.93    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 11.98/1.93    inference(flattening,[],[f50])).
% 11.98/1.93  fof(f50,plain,(
% 11.98/1.93    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 11.98/1.93    inference(ennf_transformation,[],[f30])).
% 11.98/1.93  fof(f30,axiom,(
% 11.98/1.93    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 11.98/1.93  fof(f166,plain,(
% 11.98/1.93    spl4_5),
% 11.98/1.93    inference(avatar_split_clause,[],[f86,f163])).
% 11.98/1.93  fof(f86,plain,(
% 11.98/1.93    v2_pre_topc(sK0)),
% 11.98/1.93    inference(cnf_transformation,[],[f72])).
% 11.98/1.93  fof(f72,plain,(
% 11.98/1.93    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 11.98/1.93    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f69,f71,f70])).
% 11.98/1.93  fof(f70,plain,(
% 11.98/1.93    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 11.98/1.93    introduced(choice_axiom,[])).
% 11.98/1.93  fof(f71,plain,(
% 11.98/1.93    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 11.98/1.93    introduced(choice_axiom,[])).
% 11.98/1.93  fof(f69,plain,(
% 11.98/1.93    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.98/1.93    inference(flattening,[],[f68])).
% 11.98/1.93  fof(f68,plain,(
% 11.98/1.93    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.98/1.93    inference(nnf_transformation,[],[f39])).
% 11.98/1.93  fof(f39,plain,(
% 11.98/1.93    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 11.98/1.93    inference(flattening,[],[f38])).
% 11.98/1.93  fof(f38,plain,(
% 11.98/1.93    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 11.98/1.93    inference(ennf_transformation,[],[f37])).
% 11.98/1.93  fof(f37,negated_conjecture,(
% 11.98/1.93    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 11.98/1.93    inference(negated_conjecture,[],[f36])).
% 11.98/1.93  fof(f36,conjecture,(
% 11.98/1.93    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 11.98/1.93    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 11.98/1.93  fof(f161,plain,(
% 11.98/1.93    spl4_4),
% 11.98/1.93    inference(avatar_split_clause,[],[f87,f158])).
% 11.98/1.93  fof(f87,plain,(
% 11.98/1.93    l1_pre_topc(sK0)),
% 11.98/1.93    inference(cnf_transformation,[],[f72])).
% 11.98/1.93  fof(f156,plain,(
% 11.98/1.93    spl4_3),
% 11.98/1.93    inference(avatar_split_clause,[],[f88,f153])).
% 11.98/1.93  fof(f88,plain,(
% 11.98/1.93    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 11.98/1.93    inference(cnf_transformation,[],[f72])).
% 11.98/1.93  fof(f151,plain,(
% 11.98/1.93    spl4_1 | spl4_2),
% 11.98/1.93    inference(avatar_split_clause,[],[f89,f147,f143])).
% 11.98/1.93  fof(f89,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 11.98/1.93    inference(cnf_transformation,[],[f72])).
% 11.98/1.93  fof(f150,plain,(
% 11.98/1.93    ~spl4_1 | ~spl4_2),
% 11.98/1.93    inference(avatar_split_clause,[],[f90,f147,f143])).
% 11.98/1.93  fof(f90,plain,(
% 11.98/1.93    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 11.98/1.93    inference(cnf_transformation,[],[f72])).
% 11.98/1.93  % SZS output end Proof for theBenchmark
% 11.98/1.93  % (24009)------------------------------
% 11.98/1.93  % (24009)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.98/1.93  % (24009)Termination reason: Refutation
% 11.98/1.93  
% 11.98/1.93  % (24009)Memory used [KB]: 15351
% 11.98/1.93  % (24009)Time elapsed: 0.978 s
% 11.98/1.93  % (24009)------------------------------
% 11.98/1.93  % (24009)------------------------------
% 11.98/1.93  % (23993)Time limit reached!
% 11.98/1.93  % (23993)------------------------------
% 11.98/1.93  % (23993)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 11.98/1.94  % (24022)dis+1002_3:1_acc=model:afr=on:afp=40000:afq=1.1:anc=none:ccuc=first:fsr=off:gsp=input_only:irw=on:nm=16:nwc=1:sos=all_8 on theBenchmark
% 11.98/1.94  % (23993)Termination reason: Time limit
% 11.98/1.94  
% 11.98/1.94  % (23993)Memory used [KB]: 12920
% 11.98/1.94  % (23993)Time elapsed: 1.531 s
% 11.98/1.94  % (23993)------------------------------
% 11.98/1.94  % (23993)------------------------------
% 12.34/1.95  % (23964)Success in time 1.598 s
%------------------------------------------------------------------------------
