%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:36 EST 2020

% Result     : Theorem 3.21s
% Output     : Refutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  207 ( 376 expanded)
%              Number of leaves         :   45 ( 132 expanded)
%              Depth                    :   13
%              Number of atoms          :  622 (1190 expanded)
%              Number of equality atoms :   95 ( 217 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2973,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f117,f118,f123,f128,f133,f142,f235,f560,f661,f929,f1743,f1774,f1820,f1919,f1924,f1930,f1960,f1962,f1979,f2073,f2923,f2970])).

fof(f2970,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_64
    | ~ spl3_103 ),
    inference(avatar_contradiction_clause,[],[f2969])).

fof(f2969,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_64
    | ~ spl3_103 ),
    inference(subsumption_resolution,[],[f2968,f127])).

fof(f127,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f125])).

fof(f125,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f2968,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_64
    | ~ spl3_103 ),
    inference(subsumption_resolution,[],[f2967,f122])).

fof(f122,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f120])).

fof(f120,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f2967,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_64
    | ~ spl3_103 ),
    inference(subsumption_resolution,[],[f2938,f1752])).

fof(f1752,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | spl3_64 ),
    inference(avatar_component_clause,[],[f1751])).

fof(f1751,plain,
    ( spl3_64
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f2938,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_103 ),
    inference(superposition,[],[f248,f2922])).

fof(f2922,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_103 ),
    inference(avatar_component_clause,[],[f2920])).

fof(f2920,plain,
    ( spl3_103
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).

fof(f248,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f247])).

fof(f247,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f75,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
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

fof(f75,plain,(
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

fof(f2923,plain,
    ( spl3_69
    | spl3_103
    | ~ spl3_23
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f2918,f536,f435,f2920,f2012])).

fof(f2012,plain,
    ( spl3_69
  <=> ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f435,plain,
    ( spl3_23
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f536,plain,
    ( spl3_29
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f2918,plain,
    ( ! [X9] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_23
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f2882,f437])).

fof(f437,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f435])).

fof(f2882,plain,
    ( ! [X9] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_29 ),
    inference(superposition,[],[f676,f538])).

fof(f538,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f536])).

fof(f676,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f671,f91])).

fof(f91,plain,(
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

fof(f671,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f276,f75])).

fof(f276,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f272,f91])).

fof(f272,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f83,f100])).

fof(f100,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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

fof(f2073,plain,(
    ~ spl3_69 ),
    inference(avatar_contradiction_clause,[],[f2050])).

fof(f2050,plain,
    ( $false
    | ~ spl3_69 ),
    inference(unit_resulting_resolution,[],[f144,f92,f2013,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f58])).

fof(f58,plain,(
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

fof(f2013,plain,
    ( ! [X2] : ~ m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f2012])).

fof(f92,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(cnf_transformation,[],[f69])).

fof(f69,plain,(
    ! [X0] : m1_subset_1(sK2(X0),X0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ? [X1] : m1_subset_1(X1,X0)
     => m1_subset_1(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f16,axiom,(
    ! [X0] :
    ? [X1] : m1_subset_1(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

fof(f144,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f106,f96])).

fof(f96,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f106,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f1979,plain,
    ( ~ spl3_63
    | spl3_64
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f1978,f1740,f1751,f1747])).

fof(f1747,plain,
    ( spl3_63
  <=> r1_tarski(sK1,k1_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f1740,plain,
    ( spl3_62
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f1978,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | ~ spl3_62 ),
    inference(resolution,[],[f1742,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f65])).

fof(f65,plain,(
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

fof(f1742,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f1740])).

fof(f1962,plain,
    ( spl3_29
    | ~ spl3_10
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f1961,f532,f202,f536])).

fof(f202,plain,
    ( spl3_10
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f532,plain,
    ( spl3_28
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f1961,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_10
    | ~ spl3_28 ),
    inference(subsumption_resolution,[],[f1943,f533])).

fof(f533,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f532])).

fof(f1943,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f192,f204])).

fof(f204,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f202])).

fof(f192,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f188])).

fof(f188,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f79,f80])).

fof(f80,plain,(
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

fof(f79,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f1960,plain,
    ( spl3_23
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f1939,f202,f435])).

fof(f1939,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_10 ),
    inference(superposition,[],[f144,f204])).

fof(f1930,plain,
    ( spl3_10
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f1929,f198,f114,f202])).

fof(f114,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f198,plain,
    ( spl3_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f1929,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f1926,f199])).

fof(f199,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f198])).

fof(f1926,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f75,f115])).

fof(f115,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f1924,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f1919,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_64 ),
    inference(avatar_contradiction_clause,[],[f1918])).

fof(f1918,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_10
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f1917,f127])).

fof(f1917,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_10
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f1916,f122])).

fof(f1916,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_10
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f1913,f203])).

fof(f203,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_10 ),
    inference(avatar_component_clause,[],[f202])).

fof(f1913,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_64 ),
    inference(superposition,[],[f815,f1753])).

fof(f1753,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f1751])).

fof(f815,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f278,f268])).

fof(f268,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f261,f86])).

fof(f86,plain,(
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

fof(f261,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f260])).

fof(f260,plain,(
    ! [X2,X3] :
      ( m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(superposition,[],[f102,f85])).

fof(f85,plain,(
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

fof(f278,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f84,f75])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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

fof(f1820,plain,
    ( ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_63 ),
    inference(avatar_contradiction_clause,[],[f1819])).

fof(f1819,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_63 ),
    inference(subsumption_resolution,[],[f1818,f107])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f66])).

fof(f1818,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ spl3_1
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_63 ),
    inference(subsumption_resolution,[],[f1810,f111])).

fof(f111,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f110])).

fof(f110,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f1810,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ r1_tarski(sK1,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | spl3_63 ),
    inference(resolution,[],[f1749,f307])).

fof(f307,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1) )
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(subsumption_resolution,[],[f300,f166])).

fof(f166,plain,
    ( ! [X10] :
        ( r1_tarski(X10,u1_struct_0(sK0))
        | ~ r1_tarski(X10,sK1) )
    | ~ spl3_6 ),
    inference(resolution,[],[f98,f141])).

fof(f141,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f139])).

fof(f139,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f98,plain,(
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

fof(f300,plain,
    ( ! [X0] :
        ( ~ v3_pre_topc(X0,sK0)
        | r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f293,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f67,plain,(
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

fof(f293,plain,
    ( ! [X16] :
        ( ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X16,sK1) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f290,f127])).

fof(f290,plain,
    ( ! [X16] :
        ( ~ r1_tarski(X16,sK1)
        | ~ v3_pre_topc(X16,sK0)
        | r1_tarski(X16,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f88,f122])).

fof(f88,plain,(
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

fof(f1749,plain,
    ( ~ r1_tarski(sK1,k1_tops_1(sK0,sK1))
    | spl3_63 ),
    inference(avatar_component_clause,[],[f1747])).

fof(f1774,plain,
    ( spl3_32
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1773,f125,f120,f557])).

fof(f557,plain,
    ( spl3_32
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f1773,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f1764,f127])).

fof(f1764,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f601,f122])).

fof(f601,plain,(
    ! [X4,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4)))
      | r1_tarski(X3,k2_pre_topc(X4,X3))
      | ~ l1_pre_topc(X4) ) ),
    inference(superposition,[],[f99,f266])).

fof(f266,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f263,f86])).

fof(f263,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(duplicate_literal_removal,[],[f258])).

fof(f258,plain,(
    ! [X2,X3] :
      ( k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f85,f101])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
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

fof(f99,plain,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

fof(f1743,plain,
    ( spl3_62
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1738,f125,f120,f1740])).

fof(f1738,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f1728,f127])).

fof(f1728,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f585,f122])).

fof(f585,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5)))
      | r1_tarski(k1_tops_1(X5,X4),X4)
      | ~ l1_pre_topc(X5) ) ),
    inference(superposition,[],[f97,f248])).

fof(f97,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

fof(f929,plain,
    ( ~ spl3_10
    | spl3_2
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f928,f198,f114,f202])).

fof(f928,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_2
    | ~ spl3_9 ),
    inference(subsumption_resolution,[],[f927,f199])).

fof(f927,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f116,f75])).

fof(f116,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f114])).

fof(f661,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(avatar_contradiction_clause,[],[f660])).

fof(f660,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_9 ),
    inference(subsumption_resolution,[],[f659,f127])).

fof(f659,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_9 ),
    inference(subsumption_resolution,[],[f656,f122])).

fof(f656,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_9 ),
    inference(resolution,[],[f200,f268])).

fof(f200,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f198])).

fof(f560,plain,
    ( ~ spl3_32
    | spl3_28 ),
    inference(avatar_split_clause,[],[f555,f532,f557])).

fof(f555,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_28 ),
    inference(resolution,[],[f534,f90])).

fof(f534,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_28 ),
    inference(avatar_component_clause,[],[f532])).

fof(f235,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f230,f130,f125,f120,f232])).

fof(f232,plain,
    ( spl3_13
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f130,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f230,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f229,f132])).

fof(f132,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f130])).

fof(f229,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f226,f127])).

fof(f226,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f87,f122])).

fof(f87,plain,(
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

fof(f142,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f135,f120,f139])).

fof(f135,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f89,f122])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f133,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f70,f130])).

fof(f70,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f61,f63,f62])).

fof(f62,plain,
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

fof(f63,plain,
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
    inference(flattening,[],[f60])).

fof(f60,plain,(
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

fof(f128,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f71,f125])).

fof(f71,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f123,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f72,f120])).

fof(f72,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f64])).

fof(f118,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f73,f114,f110])).

fof(f73,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).

fof(f117,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f74,f114,f110])).

fof(f74,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 13:41:01 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (32046)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.49  % (32054)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (32032)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.51  % (32038)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.51  % (32047)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (32039)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (32029)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (32030)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (32025)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (32028)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (32036)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (32026)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.53  % (32052)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (32045)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (32043)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.53  % (32048)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.39/0.53  % (32031)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.39/0.53  % (32027)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.39/0.54  % (32053)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.39/0.54  % (32051)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.39/0.54  % (32042)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.39/0.54  % (32033)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.39/0.54  % (32035)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.39/0.54  % (32040)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.39/0.55  % (32034)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.39/0.55  % (32041)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.39/0.55  % (32044)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.39/0.55  % (32037)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.52/0.56  % (32050)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.52/0.56  % (32049)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 3.21/0.81  % (32049)Time limit reached!
% 3.21/0.81  % (32049)------------------------------
% 3.21/0.81  % (32049)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.21/0.81  % (32049)Termination reason: Time limit
% 3.21/0.81  
% 3.21/0.81  % (32049)Memory used [KB]: 12920
% 3.21/0.81  % (32049)Time elapsed: 0.412 s
% 3.21/0.81  % (32049)------------------------------
% 3.21/0.81  % (32049)------------------------------
% 3.21/0.82  % (32046)Refutation found. Thanks to Tanya!
% 3.21/0.82  % SZS status Theorem for theBenchmark
% 3.61/0.82  % SZS output start Proof for theBenchmark
% 3.61/0.83  fof(f2973,plain,(
% 3.61/0.83    $false),
% 3.61/0.83    inference(avatar_sat_refutation,[],[f117,f118,f123,f128,f133,f142,f235,f560,f661,f929,f1743,f1774,f1820,f1919,f1924,f1930,f1960,f1962,f1979,f2073,f2923,f2970])).
% 3.61/0.83  fof(f2970,plain,(
% 3.61/0.83    ~spl3_3 | ~spl3_4 | spl3_64 | ~spl3_103),
% 3.61/0.83    inference(avatar_contradiction_clause,[],[f2969])).
% 3.61/0.83  fof(f2969,plain,(
% 3.61/0.83    $false | (~spl3_3 | ~spl3_4 | spl3_64 | ~spl3_103)),
% 3.61/0.83    inference(subsumption_resolution,[],[f2968,f127])).
% 3.61/0.83  fof(f127,plain,(
% 3.61/0.83    l1_pre_topc(sK0) | ~spl3_4),
% 3.61/0.83    inference(avatar_component_clause,[],[f125])).
% 3.61/0.83  fof(f125,plain,(
% 3.61/0.83    spl3_4 <=> l1_pre_topc(sK0)),
% 3.61/0.83    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 3.61/0.83  fof(f2968,plain,(
% 3.61/0.83    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_64 | ~spl3_103)),
% 3.61/0.83    inference(subsumption_resolution,[],[f2967,f122])).
% 3.61/0.83  fof(f122,plain,(
% 3.61/0.83    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 3.61/0.83    inference(avatar_component_clause,[],[f120])).
% 3.61/0.83  fof(f120,plain,(
% 3.61/0.83    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.61/0.83    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 3.61/0.83  fof(f2967,plain,(
% 3.61/0.83    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_64 | ~spl3_103)),
% 3.61/0.83    inference(subsumption_resolution,[],[f2938,f1752])).
% 3.61/0.83  fof(f1752,plain,(
% 3.61/0.83    sK1 != k1_tops_1(sK0,sK1) | spl3_64),
% 3.61/0.83    inference(avatar_component_clause,[],[f1751])).
% 3.61/0.83  fof(f1751,plain,(
% 3.61/0.83    spl3_64 <=> sK1 = k1_tops_1(sK0,sK1)),
% 3.61/0.83    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 3.61/0.83  fof(f2938,plain,(
% 3.61/0.83    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_103),
% 3.61/0.83    inference(superposition,[],[f248,f2922])).
% 3.61/0.83  fof(f2922,plain,(
% 3.61/0.83    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_103),
% 3.61/0.83    inference(avatar_component_clause,[],[f2920])).
% 3.61/0.83  fof(f2920,plain,(
% 3.61/0.83    spl3_103 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 3.61/0.83    introduced(avatar_definition,[new_symbols(naming,[spl3_103])])).
% 3.61/0.83  fof(f248,plain,(
% 3.61/0.83    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.83    inference(duplicate_literal_removal,[],[f247])).
% 3.61/0.83  fof(f247,plain,(
% 3.61/0.83    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.83    inference(superposition,[],[f75,f81])).
% 3.61/0.83  fof(f81,plain,(
% 3.61/0.83    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.83    inference(cnf_transformation,[],[f39])).
% 3.61/0.83  fof(f39,plain,(
% 3.61/0.83    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.83    inference(ennf_transformation,[],[f31])).
% 3.61/0.83  fof(f31,axiom,(
% 3.61/0.83    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.61/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_tops_1)).
% 3.61/0.83  fof(f75,plain,(
% 3.61/0.83    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.83    inference(cnf_transformation,[],[f36])).
% 3.61/0.83  fof(f36,plain,(
% 3.61/0.83    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.83    inference(ennf_transformation,[],[f21])).
% 3.61/0.83  fof(f21,axiom,(
% 3.61/0.83    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 3.61/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 3.61/0.83  fof(f2923,plain,(
% 3.61/0.83    spl3_69 | spl3_103 | ~spl3_23 | ~spl3_29),
% 3.61/0.83    inference(avatar_split_clause,[],[f2918,f536,f435,f2920,f2012])).
% 3.61/0.83  fof(f2012,plain,(
% 3.61/0.83    spl3_69 <=> ! [X2] : ~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.61/0.83    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 3.61/0.83  fof(f435,plain,(
% 3.61/0.83    spl3_23 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.61/0.83    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 3.61/0.83  fof(f536,plain,(
% 3.61/0.83    spl3_29 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 3.61/0.83    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 3.61/0.83  fof(f2918,plain,(
% 3.61/0.83    ( ! [X9] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_23 | ~spl3_29)),
% 3.61/0.83    inference(subsumption_resolution,[],[f2882,f437])).
% 3.61/0.83  fof(f437,plain,(
% 3.61/0.83    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_23),
% 3.61/0.83    inference(avatar_component_clause,[],[f435])).
% 3.61/0.83  fof(f2882,plain,(
% 3.61/0.83    ( ! [X9] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_29),
% 3.61/0.83    inference(superposition,[],[f676,f538])).
% 3.61/0.83  fof(f538,plain,(
% 3.61/0.83    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_29),
% 3.61/0.83    inference(avatar_component_clause,[],[f536])).
% 3.61/0.83  fof(f676,plain,(
% 3.61/0.83    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 3.61/0.83    inference(subsumption_resolution,[],[f671,f91])).
% 3.61/0.83  fof(f91,plain,(
% 3.61/0.83    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.83    inference(cnf_transformation,[],[f50])).
% 3.61/0.83  fof(f50,plain,(
% 3.61/0.83    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.83    inference(ennf_transformation,[],[f13])).
% 3.61/0.83  fof(f13,axiom,(
% 3.61/0.83    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 3.61/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 3.61/0.83  fof(f671,plain,(
% 3.61/0.83    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 3.61/0.83    inference(superposition,[],[f276,f75])).
% 3.61/0.83  fof(f276,plain,(
% 3.61/0.83    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.61/0.83    inference(subsumption_resolution,[],[f272,f91])).
% 3.61/0.83  fof(f272,plain,(
% 3.61/0.83    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 3.61/0.83    inference(superposition,[],[f83,f100])).
% 3.61/0.83  fof(f100,plain,(
% 3.61/0.83    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 3.61/0.83    inference(cnf_transformation,[],[f55])).
% 3.61/0.83  fof(f55,plain,(
% 3.61/0.83    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 3.61/0.83    inference(ennf_transformation,[],[f17])).
% 3.61/0.83  fof(f17,axiom,(
% 3.61/0.83    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 3.61/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 3.61/0.83  fof(f83,plain,(
% 3.61/0.83    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.83    inference(cnf_transformation,[],[f41])).
% 3.61/0.83  fof(f41,plain,(
% 3.61/0.83    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.83    inference(ennf_transformation,[],[f22])).
% 3.61/0.83  fof(f22,axiom,(
% 3.61/0.83    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 3.61/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 3.61/0.83  fof(f2073,plain,(
% 3.61/0.83    ~spl3_69),
% 3.61/0.83    inference(avatar_contradiction_clause,[],[f2050])).
% 3.61/0.83  fof(f2050,plain,(
% 3.61/0.83    $false | ~spl3_69),
% 3.61/0.83    inference(unit_resulting_resolution,[],[f144,f92,f2013,f102])).
% 3.61/0.83  fof(f102,plain,(
% 3.61/0.83    ( ! [X2,X0,X1] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.83    inference(cnf_transformation,[],[f59])).
% 3.61/0.83  fof(f59,plain,(
% 3.61/0.83    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.83    inference(flattening,[],[f58])).
% 3.61/0.83  fof(f58,plain,(
% 3.61/0.83    ! [X0,X1,X2] : (m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.61/0.83    inference(ennf_transformation,[],[f14])).
% 3.61/0.83  fof(f14,axiom,(
% 3.61/0.83    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.61/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_subset_1)).
% 3.61/0.83  fof(f2013,plain,(
% 3.61/0.83    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_69),
% 3.61/0.83    inference(avatar_component_clause,[],[f2012])).
% 3.61/0.83  fof(f92,plain,(
% 3.61/0.83    ( ! [X0] : (m1_subset_1(sK2(X0),X0)) )),
% 3.61/0.83    inference(cnf_transformation,[],[f69])).
% 3.61/0.83  fof(f69,plain,(
% 3.61/0.83    ! [X0] : m1_subset_1(sK2(X0),X0)),
% 3.61/0.83    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f16,f68])).
% 3.61/0.83  fof(f68,plain,(
% 3.61/0.83    ! [X0] : (? [X1] : m1_subset_1(X1,X0) => m1_subset_1(sK2(X0),X0))),
% 3.61/0.83    introduced(choice_axiom,[])).
% 3.61/0.83  fof(f16,axiom,(
% 3.61/0.83    ! [X0] : ? [X1] : m1_subset_1(X1,X0)),
% 3.61/0.83    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).
% 3.61/0.83  fof(f144,plain,(
% 3.61/0.83    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 3.61/0.83    inference(backward_demodulation,[],[f106,f96])).
% 3.61/0.83  fof(f96,plain,(
% 3.61/0.83    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 3.61/0.83    inference(cnf_transformation,[],[f20])).
% 3.61/0.84  fof(f20,axiom,(
% 3.61/0.84    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 3.61/0.84  fof(f106,plain,(
% 3.61/0.84    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 3.61/0.84    inference(cnf_transformation,[],[f15])).
% 3.61/0.84  fof(f15,axiom,(
% 3.61/0.84    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 3.61/0.84  fof(f1979,plain,(
% 3.61/0.84    ~spl3_63 | spl3_64 | ~spl3_62),
% 3.61/0.84    inference(avatar_split_clause,[],[f1978,f1740,f1751,f1747])).
% 3.61/0.84  fof(f1747,plain,(
% 3.61/0.84    spl3_63 <=> r1_tarski(sK1,k1_tops_1(sK0,sK1))),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 3.61/0.84  fof(f1740,plain,(
% 3.61/0.84    spl3_62 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 3.61/0.84  fof(f1978,plain,(
% 3.61/0.84    sK1 = k1_tops_1(sK0,sK1) | ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | ~spl3_62),
% 3.61/0.84    inference(resolution,[],[f1742,f78])).
% 3.61/0.84  fof(f78,plain,(
% 3.61/0.84    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f66])).
% 3.61/0.84  fof(f66,plain,(
% 3.61/0.84    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.84    inference(flattening,[],[f65])).
% 3.61/0.84  fof(f65,plain,(
% 3.61/0.84    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.84    inference(nnf_transformation,[],[f1])).
% 3.61/0.84  fof(f1,axiom,(
% 3.61/0.84    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 3.61/0.84  fof(f1742,plain,(
% 3.61/0.84    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_62),
% 3.61/0.84    inference(avatar_component_clause,[],[f1740])).
% 3.61/0.84  fof(f1962,plain,(
% 3.61/0.84    spl3_29 | ~spl3_10 | ~spl3_28),
% 3.61/0.84    inference(avatar_split_clause,[],[f1961,f532,f202,f536])).
% 3.61/0.84  fof(f202,plain,(
% 3.61/0.84    spl3_10 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 3.61/0.84  fof(f532,plain,(
% 3.61/0.84    spl3_28 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 3.61/0.84  fof(f1961,plain,(
% 3.61/0.84    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | (~spl3_10 | ~spl3_28)),
% 3.61/0.84    inference(subsumption_resolution,[],[f1943,f533])).
% 3.61/0.84  fof(f533,plain,(
% 3.61/0.84    m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_28),
% 3.61/0.84    inference(avatar_component_clause,[],[f532])).
% 3.61/0.84  fof(f1943,plain,(
% 3.61/0.84    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 3.61/0.84    inference(superposition,[],[f192,f204])).
% 3.61/0.84  fof(f204,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_10),
% 3.61/0.84    inference(avatar_component_clause,[],[f202])).
% 3.61/0.84  fof(f192,plain,(
% 3.61/0.84    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.84    inference(duplicate_literal_removal,[],[f188])).
% 3.61/0.84  fof(f188,plain,(
% 3.61/0.84    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.84    inference(superposition,[],[f79,f80])).
% 3.61/0.84  fof(f80,plain,(
% 3.61/0.84    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.84    inference(cnf_transformation,[],[f38])).
% 3.61/0.84  fof(f38,plain,(
% 3.61/0.84    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.84    inference(ennf_transformation,[],[f12])).
% 3.61/0.84  fof(f12,axiom,(
% 3.61/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 3.61/0.84  fof(f79,plain,(
% 3.61/0.84    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.84    inference(cnf_transformation,[],[f37])).
% 3.61/0.84  fof(f37,plain,(
% 3.61/0.84    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.84    inference(ennf_transformation,[],[f18])).
% 3.61/0.84  fof(f18,axiom,(
% 3.61/0.84    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 3.61/0.84  fof(f1960,plain,(
% 3.61/0.84    spl3_23 | ~spl3_10),
% 3.61/0.84    inference(avatar_split_clause,[],[f1939,f202,f435])).
% 3.61/0.84  fof(f1939,plain,(
% 3.61/0.84    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_10),
% 3.61/0.84    inference(superposition,[],[f144,f204])).
% 3.61/0.84  fof(f1930,plain,(
% 3.61/0.84    spl3_10 | ~spl3_2 | ~spl3_9),
% 3.61/0.84    inference(avatar_split_clause,[],[f1929,f198,f114,f202])).
% 3.61/0.84  fof(f114,plain,(
% 3.61/0.84    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 3.61/0.84  fof(f198,plain,(
% 3.61/0.84    spl3_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 3.61/0.84  fof(f1929,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_9)),
% 3.61/0.84    inference(subsumption_resolution,[],[f1926,f199])).
% 3.61/0.84  fof(f199,plain,(
% 3.61/0.84    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 3.61/0.84    inference(avatar_component_clause,[],[f198])).
% 3.61/0.84  fof(f1926,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 3.61/0.84    inference(superposition,[],[f75,f115])).
% 3.61/0.84  fof(f115,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 3.61/0.84    inference(avatar_component_clause,[],[f114])).
% 3.61/0.84  fof(f1924,plain,(
% 3.61/0.84    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.61/0.84    introduced(theory_tautology_sat_conflict,[])).
% 3.61/0.84  fof(f1919,plain,(
% 3.61/0.84    ~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_64),
% 3.61/0.84    inference(avatar_contradiction_clause,[],[f1918])).
% 3.61/0.84  fof(f1918,plain,(
% 3.61/0.84    $false | (~spl3_3 | ~spl3_4 | spl3_10 | ~spl3_64)),
% 3.61/0.84    inference(subsumption_resolution,[],[f1917,f127])).
% 3.61/0.84  fof(f1917,plain,(
% 3.61/0.84    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_10 | ~spl3_64)),
% 3.61/0.84    inference(subsumption_resolution,[],[f1916,f122])).
% 3.61/0.84  fof(f1916,plain,(
% 3.61/0.84    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_10 | ~spl3_64)),
% 3.61/0.84    inference(subsumption_resolution,[],[f1913,f203])).
% 3.61/0.84  fof(f203,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl3_10),
% 3.61/0.84    inference(avatar_component_clause,[],[f202])).
% 3.61/0.84  fof(f1913,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_64),
% 3.61/0.84    inference(superposition,[],[f815,f1753])).
% 3.61/0.84  fof(f1753,plain,(
% 3.61/0.84    sK1 = k1_tops_1(sK0,sK1) | ~spl3_64),
% 3.61/0.84    inference(avatar_component_clause,[],[f1751])).
% 3.61/0.84  fof(f815,plain,(
% 3.61/0.84    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.61/0.84    inference(subsumption_resolution,[],[f278,f268])).
% 3.61/0.84  fof(f268,plain,(
% 3.61/0.84    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.61/0.84    inference(subsumption_resolution,[],[f261,f86])).
% 3.61/0.84  fof(f86,plain,(
% 3.61/0.84    ( ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f45])).
% 3.61/0.84  fof(f45,plain,(
% 3.61/0.84    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 3.61/0.84    inference(flattening,[],[f44])).
% 3.61/0.84  fof(f44,plain,(
% 3.61/0.84    ! [X0,X1] : (m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 3.61/0.84    inference(ennf_transformation,[],[f25])).
% 3.61/0.84  fof(f25,axiom,(
% 3.61/0.84    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_1)).
% 3.61/0.84  fof(f261,plain,(
% 3.61/0.84    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.61/0.84    inference(duplicate_literal_removal,[],[f260])).
% 3.61/0.84  fof(f260,plain,(
% 3.61/0.84    ( ! [X2,X3] : (m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.61/0.84    inference(superposition,[],[f102,f85])).
% 3.61/0.84  fof(f85,plain,(
% 3.61/0.84    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f43])).
% 3.61/0.84  fof(f43,plain,(
% 3.61/0.84    ! [X0] : (! [X1] : (k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.84    inference(ennf_transformation,[],[f30])).
% 3.61/0.84  fof(f30,axiom,(
% 3.61/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_pre_topc(X0,X1) = k4_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_tops_1)).
% 3.61/0.84  fof(f278,plain,(
% 3.61/0.84    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.61/0.84    inference(superposition,[],[f84,f75])).
% 3.61/0.84  fof(f84,plain,(
% 3.61/0.84    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f42])).
% 3.61/0.84  fof(f42,plain,(
% 3.61/0.84    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.84    inference(ennf_transformation,[],[f27])).
% 3.61/0.84  fof(f27,axiom,(
% 3.61/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 3.61/0.84  fof(f1820,plain,(
% 3.61/0.84    ~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_63),
% 3.61/0.84    inference(avatar_contradiction_clause,[],[f1819])).
% 3.61/0.84  fof(f1819,plain,(
% 3.61/0.84    $false | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_63)),
% 3.61/0.84    inference(subsumption_resolution,[],[f1818,f107])).
% 3.61/0.84  fof(f107,plain,(
% 3.61/0.84    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.61/0.84    inference(equality_resolution,[],[f77])).
% 3.61/0.84  fof(f77,plain,(
% 3.61/0.84    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.61/0.84    inference(cnf_transformation,[],[f66])).
% 3.61/0.84  fof(f1818,plain,(
% 3.61/0.84    ~r1_tarski(sK1,sK1) | (~spl3_1 | ~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_63)),
% 3.61/0.84    inference(subsumption_resolution,[],[f1810,f111])).
% 3.61/0.84  fof(f111,plain,(
% 3.61/0.84    v3_pre_topc(sK1,sK0) | ~spl3_1),
% 3.61/0.84    inference(avatar_component_clause,[],[f110])).
% 3.61/0.84  fof(f110,plain,(
% 3.61/0.84    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 3.61/0.84  fof(f1810,plain,(
% 3.61/0.84    ~v3_pre_topc(sK1,sK0) | ~r1_tarski(sK1,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_6 | spl3_63)),
% 3.61/0.84    inference(resolution,[],[f1749,f307])).
% 3.61/0.84  fof(f307,plain,(
% 3.61/0.84    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1)) ) | (~spl3_3 | ~spl3_4 | ~spl3_6)),
% 3.61/0.84    inference(subsumption_resolution,[],[f300,f166])).
% 3.61/0.84  fof(f166,plain,(
% 3.61/0.84    ( ! [X10] : (r1_tarski(X10,u1_struct_0(sK0)) | ~r1_tarski(X10,sK1)) ) | ~spl3_6),
% 3.61/0.84    inference(resolution,[],[f98,f141])).
% 3.61/0.84  fof(f141,plain,(
% 3.61/0.84    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 3.61/0.84    inference(avatar_component_clause,[],[f139])).
% 3.61/0.84  fof(f139,plain,(
% 3.61/0.84    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 3.61/0.84  fof(f98,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (~r1_tarski(X1,X2) | r1_tarski(X0,X2) | ~r1_tarski(X0,X1)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f54])).
% 3.61/0.84  fof(f54,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 3.61/0.84    inference(flattening,[],[f53])).
% 3.61/0.84  fof(f53,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 3.61/0.84    inference(ennf_transformation,[],[f4])).
% 3.61/0.84  fof(f4,axiom,(
% 3.61/0.84    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 3.61/0.84  fof(f300,plain,(
% 3.61/0.84    ( ! [X0] : (~v3_pre_topc(X0,sK0) | r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_4)),
% 3.61/0.84    inference(resolution,[],[f293,f90])).
% 3.61/0.84  fof(f90,plain,(
% 3.61/0.84    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f67])).
% 3.61/0.84  fof(f67,plain,(
% 3.61/0.84    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.61/0.84    inference(nnf_transformation,[],[f24])).
% 3.61/0.84  fof(f24,axiom,(
% 3.61/0.84    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 3.61/0.84  fof(f293,plain,(
% 3.61/0.84    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~r1_tarski(X16,sK1)) ) | (~spl3_3 | ~spl3_4)),
% 3.61/0.84    inference(subsumption_resolution,[],[f290,f127])).
% 3.61/0.84  fof(f290,plain,(
% 3.61/0.84    ( ! [X16] : (~r1_tarski(X16,sK1) | ~v3_pre_topc(X16,sK0) | r1_tarski(X16,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X16,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 3.61/0.84    inference(resolution,[],[f88,f122])).
% 3.61/0.84  fof(f88,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f49])).
% 3.61/0.84  fof(f49,plain,(
% 3.61/0.84    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.84    inference(flattening,[],[f48])).
% 3.61/0.84  fof(f48,plain,(
% 3.61/0.84    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 3.61/0.84    inference(ennf_transformation,[],[f28])).
% 3.61/0.84  fof(f28,axiom,(
% 3.61/0.84    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t56_tops_1)).
% 3.61/0.84  fof(f1749,plain,(
% 3.61/0.84    ~r1_tarski(sK1,k1_tops_1(sK0,sK1)) | spl3_63),
% 3.61/0.84    inference(avatar_component_clause,[],[f1747])).
% 3.61/0.84  fof(f1774,plain,(
% 3.61/0.84    spl3_32 | ~spl3_3 | ~spl3_4),
% 3.61/0.84    inference(avatar_split_clause,[],[f1773,f125,f120,f557])).
% 3.61/0.84  fof(f557,plain,(
% 3.61/0.84    spl3_32 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 3.61/0.84  fof(f1773,plain,(
% 3.61/0.84    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 3.61/0.84    inference(subsumption_resolution,[],[f1764,f127])).
% 3.61/0.84  fof(f1764,plain,(
% 3.61/0.84    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 3.61/0.84    inference(resolution,[],[f601,f122])).
% 3.61/0.84  fof(f601,plain,(
% 3.61/0.84    ( ! [X4,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X4))) | r1_tarski(X3,k2_pre_topc(X4,X3)) | ~l1_pre_topc(X4)) )),
% 3.61/0.84    inference(superposition,[],[f99,f266])).
% 3.61/0.84  fof(f266,plain,(
% 3.61/0.84    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 3.61/0.84    inference(subsumption_resolution,[],[f263,f86])).
% 3.61/0.84  fof(f263,plain,(
% 3.61/0.84    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.61/0.84    inference(duplicate_literal_removal,[],[f258])).
% 3.61/0.84  fof(f258,plain,(
% 3.61/0.84    ( ! [X2,X3] : (k2_xboole_0(X3,k2_tops_1(X2,X3)) = k2_pre_topc(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_tops_1(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) )),
% 3.61/0.84    inference(superposition,[],[f85,f101])).
% 3.61/0.84  fof(f101,plain,(
% 3.61/0.84    ( ! [X2,X0,X1] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.84    inference(cnf_transformation,[],[f57])).
% 3.61/0.84  fof(f57,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.84    inference(flattening,[],[f56])).
% 3.61/0.84  fof(f56,plain,(
% 3.61/0.84    ! [X0,X1,X2] : (k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))))),
% 3.61/0.84    inference(ennf_transformation,[],[f19])).
% 3.61/0.84  fof(f19,axiom,(
% 3.61/0.84    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & m1_subset_1(X1,k1_zfmisc_1(X0))) => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).
% 3.61/0.84  fof(f99,plain,(
% 3.61/0.84    ( ! [X0,X1] : (r1_tarski(X0,k2_xboole_0(X0,X1))) )),
% 3.61/0.84    inference(cnf_transformation,[],[f9])).
% 3.61/0.84  fof(f9,axiom,(
% 3.61/0.84    ! [X0,X1] : r1_tarski(X0,k2_xboole_0(X0,X1))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).
% 3.61/0.84  fof(f1743,plain,(
% 3.61/0.84    spl3_62 | ~spl3_3 | ~spl3_4),
% 3.61/0.84    inference(avatar_split_clause,[],[f1738,f125,f120,f1740])).
% 3.61/0.84  fof(f1738,plain,(
% 3.61/0.84    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 3.61/0.84    inference(subsumption_resolution,[],[f1728,f127])).
% 3.61/0.84  fof(f1728,plain,(
% 3.61/0.84    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 3.61/0.84    inference(resolution,[],[f585,f122])).
% 3.61/0.84  fof(f585,plain,(
% 3.61/0.84    ( ! [X4,X5] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X5))) | r1_tarski(k1_tops_1(X5,X4),X4) | ~l1_pre_topc(X5)) )),
% 3.61/0.84    inference(superposition,[],[f97,f248])).
% 3.61/0.84  fof(f97,plain,(
% 3.61/0.84    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f5])).
% 3.61/0.84  fof(f5,axiom,(
% 3.61/0.84    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0)),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).
% 3.61/0.84  fof(f929,plain,(
% 3.61/0.84    ~spl3_10 | spl3_2 | ~spl3_9),
% 3.61/0.84    inference(avatar_split_clause,[],[f928,f198,f114,f202])).
% 3.61/0.84  fof(f928,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl3_2 | ~spl3_9)),
% 3.61/0.84    inference(subsumption_resolution,[],[f927,f199])).
% 3.61/0.84  fof(f927,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 3.61/0.84    inference(superposition,[],[f116,f75])).
% 3.61/0.84  fof(f116,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 3.61/0.84    inference(avatar_component_clause,[],[f114])).
% 3.61/0.84  fof(f661,plain,(
% 3.61/0.84    ~spl3_3 | ~spl3_4 | spl3_9),
% 3.61/0.84    inference(avatar_contradiction_clause,[],[f660])).
% 3.61/0.84  fof(f660,plain,(
% 3.61/0.84    $false | (~spl3_3 | ~spl3_4 | spl3_9)),
% 3.61/0.84    inference(subsumption_resolution,[],[f659,f127])).
% 3.61/0.84  fof(f659,plain,(
% 3.61/0.84    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_9)),
% 3.61/0.84    inference(subsumption_resolution,[],[f656,f122])).
% 3.61/0.84  fof(f656,plain,(
% 3.61/0.84    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_9),
% 3.61/0.84    inference(resolution,[],[f200,f268])).
% 3.61/0.84  fof(f200,plain,(
% 3.61/0.84    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_9),
% 3.61/0.84    inference(avatar_component_clause,[],[f198])).
% 3.61/0.84  fof(f560,plain,(
% 3.61/0.84    ~spl3_32 | spl3_28),
% 3.61/0.84    inference(avatar_split_clause,[],[f555,f532,f557])).
% 3.61/0.84  fof(f555,plain,(
% 3.61/0.84    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_28),
% 3.61/0.84    inference(resolution,[],[f534,f90])).
% 3.61/0.84  fof(f534,plain,(
% 3.61/0.84    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_28),
% 3.61/0.84    inference(avatar_component_clause,[],[f532])).
% 3.61/0.84  fof(f235,plain,(
% 3.61/0.84    spl3_13 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 3.61/0.84    inference(avatar_split_clause,[],[f230,f130,f125,f120,f232])).
% 3.61/0.84  fof(f232,plain,(
% 3.61/0.84    spl3_13 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 3.61/0.84  fof(f130,plain,(
% 3.61/0.84    spl3_5 <=> v2_pre_topc(sK0)),
% 3.61/0.84    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 3.61/0.84  fof(f230,plain,(
% 3.61/0.84    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 3.61/0.84    inference(subsumption_resolution,[],[f229,f132])).
% 3.61/0.84  fof(f132,plain,(
% 3.61/0.84    v2_pre_topc(sK0) | ~spl3_5),
% 3.61/0.84    inference(avatar_component_clause,[],[f130])).
% 3.61/0.84  fof(f229,plain,(
% 3.61/0.84    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 3.61/0.84    inference(subsumption_resolution,[],[f226,f127])).
% 3.61/0.84  fof(f226,plain,(
% 3.61/0.84    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 3.61/0.84    inference(resolution,[],[f87,f122])).
% 3.61/0.84  fof(f87,plain,(
% 3.61/0.84    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f47])).
% 3.61/0.84  fof(f47,plain,(
% 3.61/0.84    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 3.61/0.84    inference(flattening,[],[f46])).
% 3.61/0.84  fof(f46,plain,(
% 3.61/0.84    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 3.61/0.84    inference(ennf_transformation,[],[f26])).
% 3.61/0.84  fof(f26,axiom,(
% 3.61/0.84    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 3.61/0.84  fof(f142,plain,(
% 3.61/0.84    spl3_6 | ~spl3_3),
% 3.61/0.84    inference(avatar_split_clause,[],[f135,f120,f139])).
% 3.61/0.84  fof(f135,plain,(
% 3.61/0.84    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 3.61/0.84    inference(resolution,[],[f89,f122])).
% 3.61/0.84  fof(f89,plain,(
% 3.61/0.84    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 3.61/0.84    inference(cnf_transformation,[],[f67])).
% 3.61/0.84  fof(f133,plain,(
% 3.61/0.84    spl3_5),
% 3.61/0.84    inference(avatar_split_clause,[],[f70,f130])).
% 3.61/0.84  fof(f70,plain,(
% 3.61/0.84    v2_pre_topc(sK0)),
% 3.61/0.84    inference(cnf_transformation,[],[f64])).
% 3.61/0.84  fof(f64,plain,(
% 3.61/0.84    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 3.61/0.84    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f61,f63,f62])).
% 3.61/0.84  fof(f62,plain,(
% 3.61/0.84    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 3.61/0.84    introduced(choice_axiom,[])).
% 3.61/0.84  fof(f63,plain,(
% 3.61/0.84    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 3.61/0.84    introduced(choice_axiom,[])).
% 3.61/0.84  fof(f61,plain,(
% 3.61/0.84    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.61/0.84    inference(flattening,[],[f60])).
% 3.61/0.84  fof(f60,plain,(
% 3.61/0.84    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.61/0.84    inference(nnf_transformation,[],[f35])).
% 3.61/0.84  fof(f35,plain,(
% 3.61/0.84    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 3.61/0.84    inference(flattening,[],[f34])).
% 3.61/0.84  fof(f34,plain,(
% 3.61/0.84    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 3.61/0.84    inference(ennf_transformation,[],[f33])).
% 3.61/0.84  fof(f33,negated_conjecture,(
% 3.61/0.84    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.61/0.84    inference(negated_conjecture,[],[f32])).
% 3.61/0.84  fof(f32,conjecture,(
% 3.61/0.84    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 3.61/0.84    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_tops_1)).
% 3.61/0.84  fof(f128,plain,(
% 3.61/0.84    spl3_4),
% 3.61/0.84    inference(avatar_split_clause,[],[f71,f125])).
% 3.61/0.84  fof(f71,plain,(
% 3.61/0.84    l1_pre_topc(sK0)),
% 3.61/0.84    inference(cnf_transformation,[],[f64])).
% 3.61/0.84  fof(f123,plain,(
% 3.61/0.84    spl3_3),
% 3.61/0.84    inference(avatar_split_clause,[],[f72,f120])).
% 3.61/0.84  fof(f72,plain,(
% 3.61/0.84    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 3.61/0.84    inference(cnf_transformation,[],[f64])).
% 3.61/0.84  fof(f118,plain,(
% 3.61/0.84    spl3_1 | spl3_2),
% 3.61/0.84    inference(avatar_split_clause,[],[f73,f114,f110])).
% 3.61/0.84  fof(f73,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 3.61/0.84    inference(cnf_transformation,[],[f64])).
% 3.61/0.84  fof(f117,plain,(
% 3.61/0.84    ~spl3_1 | ~spl3_2),
% 3.61/0.84    inference(avatar_split_clause,[],[f74,f114,f110])).
% 3.61/0.84  fof(f74,plain,(
% 3.61/0.84    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 3.61/0.84    inference(cnf_transformation,[],[f64])).
% 3.61/0.84  % SZS output end Proof for theBenchmark
% 3.61/0.84  % (32046)------------------------------
% 3.61/0.84  % (32046)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.61/0.84  % (32046)Termination reason: Refutation
% 3.61/0.84  
% 3.61/0.84  % (32046)Memory used [KB]: 11769
% 3.61/0.84  % (32046)Time elapsed: 0.415 s
% 3.61/0.84  % (32046)------------------------------
% 3.61/0.84  % (32046)------------------------------
% 3.61/0.84  % (32024)Success in time 0.482 s
%------------------------------------------------------------------------------
