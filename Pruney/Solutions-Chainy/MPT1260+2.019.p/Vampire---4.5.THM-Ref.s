%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:35 EST 2020

% Result     : Theorem 2.06s
% Output     : Refutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 332 expanded)
%              Number of leaves         :   37 ( 125 expanded)
%              Depth                    :   12
%              Number of atoms          :  533 (1053 expanded)
%              Number of equality atoms :   88 ( 207 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2042,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f122,f123,f128,f133,f138,f149,f237,f264,f278,f471,f492,f550,f1180,f1235,f1240,f1269,f1287,f1951,f1979,f2031,f2041])).

fof(f2041,plain,
    ( sK1 != k1_tops_1(sK0,sK1)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f2031,plain,(
    ~ spl3_64 ),
    inference(avatar_contradiction_clause,[],[f2021])).

fof(f2021,plain,
    ( $false
    | ~ spl3_64 ),
    inference(resolution,[],[f1257,f151])).

fof(f151,plain,(
    ! [X0,X1] : m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0)) ),
    inference(backward_demodulation,[],[f107,f99])).

fof(f99,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

fof(f107,plain,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

fof(f1257,plain,
    ( ! [X9] : ~ m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f1256])).

fof(f1256,plain,
    ( spl3_64
  <=> ! [X9] : ~ m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f1979,plain,
    ( spl3_37
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_78 ),
    inference(avatar_split_clause,[],[f1978,f1948,f130,f125,f544])).

fof(f544,plain,
    ( spl3_37
  <=> sK1 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f125,plain,
    ( spl3_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f130,plain,
    ( spl3_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f1948,plain,
    ( spl3_78
  <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f1978,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_78 ),
    inference(subsumption_resolution,[],[f1977,f132])).

fof(f132,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f130])).

fof(f1977,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_78 ),
    inference(subsumption_resolution,[],[f1956,f127])).

fof(f127,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f125])).

fof(f1956,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_78 ),
    inference(superposition,[],[f286,f1950])).

fof(f1950,plain,
    ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f1948])).

fof(f286,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f285])).

fof(f285,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(superposition,[],[f72,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f1951,plain,
    ( spl3_64
    | spl3_78
    | ~ spl3_24
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f1946,f468,f365,f1948,f1256])).

fof(f365,plain,
    ( spl3_24
  <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f468,plain,
    ( spl3_32
  <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f1946,plain,
    ( ! [X13] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_24
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f1922,f367])).

fof(f367,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f365])).

fof(f1922,plain,
    ( ! [X13] :
        ( sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))
        | ~ m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
        | ~ m1_subset_1(X13,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) )
    | ~ spl3_32 ),
    inference(superposition,[],[f631,f470])).

fof(f470,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f468])).

fof(f631,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2)) ) ),
    inference(subsumption_resolution,[],[f626,f89])).

fof(f89,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f626,plain,(
    ! [X4,X2,X3] :
      ( k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X2))
      | ~ m1_subset_1(X4,k1_zfmisc_1(X2))
      | ~ m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2)) ) ),
    inference(superposition,[],[f318,f72])).

fof(f318,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(subsumption_resolution,[],[f314,f89])).

fof(f314,plain,(
    ! [X4,X5,X3] :
      ( k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
      | ~ m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(X3)) ) ),
    inference(superposition,[],[f79,f104])).

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X1) = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

fof(f1287,plain,
    ( spl3_24
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f1275,f223,f365])).

fof(f223,plain,
    ( spl3_12
  <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f1275,plain,
    ( m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_12 ),
    inference(superposition,[],[f151,f225])).

fof(f225,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f223])).

fof(f1269,plain,
    ( spl3_12
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f1268,f219,f119,f223])).

fof(f119,plain,
    ( spl3_2
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f219,plain,
    ( spl3_11
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f1268,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f1265,f220])).

fof(f220,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f219])).

fof(f1265,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_2 ),
    inference(superposition,[],[f72,f120])).

fof(f120,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f1240,plain,
    ( ~ spl3_1
    | spl3_37
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f1194,f540,f146,f130,f125,f544,f115])).

fof(f115,plain,
    ( spl3_1
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f146,plain,
    ( spl3_6
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f540,plain,
    ( spl3_36
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f1194,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f1193,f148])).

fof(f148,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f146])).

fof(f1193,plain,
    ( ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_36 ),
    inference(subsumption_resolution,[],[f1187,f109])).

fof(f109,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f1187,plain,
    ( ~ r1_tarski(sK1,sK1)
    | ~ r1_tarski(sK1,u1_struct_0(sK0))
    | sK1 = k1_tops_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_36 ),
    inference(resolution,[],[f541,f621])).

fof(f621,plain,
    ( ! [X2] :
        ( ~ r1_tarski(k1_tops_1(sK0,sK1),X2)
        | ~ r1_tarski(X2,sK1)
        | ~ r1_tarski(X2,u1_struct_0(sK0))
        | k1_tops_1(sK0,sK1) = X2
        | ~ v3_pre_topc(X2,sK0) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f376,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f376,plain,
    ( ! [X0] :
        ( r1_tarski(X0,k1_tops_1(sK0,sK1))
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,sK1)
        | ~ r1_tarski(X0,u1_struct_0(sK0)) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(resolution,[],[f342,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f342,plain,
    ( ! [X13] :
        ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X13,sK0)
        | r1_tarski(X13,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(X13,sK1) )
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f339,f132])).

fof(f339,plain,
    ( ! [X13] :
        ( ~ r1_tarski(X13,sK1)
        | ~ v3_pre_topc(X13,sK0)
        | r1_tarski(X13,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl3_3 ),
    inference(resolution,[],[f86,f127])).

fof(f86,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).

fof(f541,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f540])).

fof(f1235,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_12
    | ~ spl3_37 ),
    inference(avatar_contradiction_clause,[],[f1234])).

fof(f1234,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_12
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f1233,f132])).

fof(f1233,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_12
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f1232,f127])).

fof(f1232,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_12
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f1228,f224])).

fof(f224,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_12 ),
    inference(avatar_component_clause,[],[f223])).

fof(f1228,plain,
    ( k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_37 ),
    inference(superposition,[],[f332,f546])).

fof(f546,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f544])).

fof(f332,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(subsumption_resolution,[],[f330,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f330,plain,(
    ! [X2,X3] :
      ( k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2)
      | ~ m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2))) ) ),
    inference(superposition,[],[f80,f72])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).

fof(f1180,plain,
    ( spl3_36
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f1179,f130,f125,f540])).

fof(f1179,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f1169,f132])).

fof(f1169,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f590,f127])).

fof(f590,plain,(
    ! [X15,X16] :
      ( ~ m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X16)))
      | r1_tarski(k1_tops_1(X16,X15),X15)
      | ~ l1_pre_topc(X16) ) ),
    inference(superposition,[],[f152,f286])).

fof(f152,plain,(
    ! [X0,X1] : r1_tarski(k4_xboole_0(X0,X1),X0) ),
    inference(forward_demodulation,[],[f144,f99])).

fof(f144,plain,(
    ! [X0,X1] : r1_tarski(k6_subset_1(X0,X1),X0) ),
    inference(resolution,[],[f87,f107])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f550,plain,
    ( ~ spl3_12
    | spl3_2
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f549,f219,f119,f223])).

fof(f549,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | spl3_2
    | ~ spl3_11 ),
    inference(subsumption_resolution,[],[f548,f220])).

fof(f548,plain,
    ( k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_2 ),
    inference(superposition,[],[f121,f72])).

fof(f121,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f119])).

fof(f492,plain,
    ( ~ spl3_13
    | spl3_31 ),
    inference(avatar_contradiction_clause,[],[f491])).

fof(f491,plain,
    ( $false
    | ~ spl3_13
    | spl3_31 ),
    inference(subsumption_resolution,[],[f489,f236])).

fof(f236,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f234])).

fof(f234,plain,
    ( spl3_13
  <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f489,plain,
    ( ~ r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | spl3_31 ),
    inference(resolution,[],[f466,f88])).

fof(f466,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f464])).

fof(f464,plain,
    ( spl3_31
  <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f471,plain,
    ( ~ spl3_31
    | spl3_32
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f455,f223,f468,f464])).

fof(f455,plain,
    ( sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))
    | ~ spl3_12 ),
    inference(superposition,[],[f207,f225])).

fof(f207,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(duplicate_literal_removal,[],[f203])).

fof(f203,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(superposition,[],[f76,f77])).

fof(f77,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f76,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f37])).

% (16882)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f278,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_11 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_4
    | spl3_11 ),
    inference(subsumption_resolution,[],[f276,f132])).

fof(f276,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ spl3_3
    | spl3_11 ),
    inference(subsumption_resolution,[],[f273,f127])).

fof(f273,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl3_11 ),
    inference(resolution,[],[f221,f82])).

fof(f221,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl3_11 ),
    inference(avatar_component_clause,[],[f219])).

fof(f264,plain,
    ( spl3_16
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f259,f135,f130,f125,f261])).

fof(f261,plain,
    ( spl3_16
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f135,plain,
    ( spl3_5
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f259,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f258,f137])).

fof(f137,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f135])).

fof(f258,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f256,f132])).

fof(f256,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f85,f127])).

fof(f85,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f237,plain,
    ( spl3_13
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f232,f130,f125,f234])).

fof(f232,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ spl3_3
    | ~ spl3_4 ),
    inference(subsumption_resolution,[],[f231,f132])).

fof(f231,plain,
    ( r1_tarski(sK1,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ spl3_3 ),
    inference(resolution,[],[f83,f127])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r1_tarski(X1,k2_pre_topc(X0,X1))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(X1,k2_pre_topc(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(X1,k2_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).

fof(f149,plain,
    ( spl3_6
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f143,f125,f146])).

fof(f143,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl3_3 ),
    inference(resolution,[],[f87,f127])).

fof(f138,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f67,f135])).

fof(f67,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,
    ( ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | ~ v3_pre_topc(sK1,sK0) )
    & ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
      | v3_pre_topc(sK1,sK0) )
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).

fof(f56,plain,
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

fof(f57,plain,
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

fof(f55,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | ~ v3_pre_topc(X1,X0) )
          & ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f54])).

fof(f54,plain,(
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
    inference(ennf_transformation,[],[f32])).

fof(f32,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    inference(negated_conjecture,[],[f31])).

fof(f31,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).

fof(f133,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f68,f130])).

fof(f68,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f128,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f69,f125])).

fof(f69,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f58])).

fof(f123,plain,
    ( spl3_1
    | spl3_2 ),
    inference(avatar_split_clause,[],[f70,f119,f115])).

fof(f70,plain,
    ( k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f122,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f71,f119,f115])).

fof(f71,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 15:27:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.50  % (16847)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.51  % (16840)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.51  % (16839)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.51  % (16845)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (16843)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.52  % (16844)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.52  % (16842)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (16856)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.53  % (16841)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.53  % (16862)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (16850)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (16854)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (16855)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (16859)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.53  % (16861)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (16849)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (16855)Refutation not found, incomplete strategy% (16855)------------------------------
% 0.21/0.54  % (16855)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16864)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (16846)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (16857)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (16866)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.54  % (16851)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (16866)Refutation not found, incomplete strategy% (16866)------------------------------
% 0.21/0.54  % (16866)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (16866)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (16866)Memory used [KB]: 6268
% 0.21/0.54  % (16866)Time elapsed: 0.131 s
% 0.21/0.54  % (16866)------------------------------
% 0.21/0.54  % (16866)------------------------------
% 0.21/0.54  % (16853)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (16868)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (16858)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.54  % (16848)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.55  % (16860)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.55  % (16855)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (16855)Memory used [KB]: 10746
% 0.21/0.55  % (16855)Time elapsed: 0.128 s
% 0.21/0.55  % (16855)------------------------------
% 0.21/0.55  % (16855)------------------------------
% 0.21/0.55  % (16867)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.55  % (16865)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (16852)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.55  % (16863)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.56  % (16849)Refutation not found, incomplete strategy% (16849)------------------------------
% 0.21/0.56  % (16849)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (16849)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (16849)Memory used [KB]: 11001
% 0.21/0.56  % (16849)Time elapsed: 0.157 s
% 0.21/0.56  % (16849)------------------------------
% 0.21/0.56  % (16849)------------------------------
% 0.21/0.57  % (16867)Refutation not found, incomplete strategy% (16867)------------------------------
% 0.21/0.57  % (16867)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.57  % (16867)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.57  
% 0.21/0.57  % (16867)Memory used [KB]: 11001
% 0.21/0.57  % (16867)Time elapsed: 0.144 s
% 0.21/0.57  % (16867)------------------------------
% 0.21/0.57  % (16867)------------------------------
% 2.06/0.67  % (16876)dis+1010_1_acc=model:add=large:afr=on:amm=off:anc=none:bd=off:bsr=on:ccuc=small_ones:gs=on:gsem=on:nm=16:nwc=2:urr=ec_only:updr=off_155 on theBenchmark
% 2.06/0.68  % (16875)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.06/0.69  % (16860)Refutation found. Thanks to Tanya!
% 2.06/0.69  % SZS status Theorem for theBenchmark
% 2.06/0.69  % SZS output start Proof for theBenchmark
% 2.06/0.69  fof(f2042,plain,(
% 2.06/0.69    $false),
% 2.06/0.69    inference(avatar_sat_refutation,[],[f122,f123,f128,f133,f138,f149,f237,f264,f278,f471,f492,f550,f1180,f1235,f1240,f1269,f1287,f1951,f1979,f2031,f2041])).
% 2.06/0.69  fof(f2041,plain,(
% 2.06/0.69    sK1 != k1_tops_1(sK0,sK1) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.06/0.69    introduced(theory_tautology_sat_conflict,[])).
% 2.06/0.69  fof(f2031,plain,(
% 2.06/0.69    ~spl3_64),
% 2.06/0.69    inference(avatar_contradiction_clause,[],[f2021])).
% 2.06/0.69  fof(f2021,plain,(
% 2.06/0.69    $false | ~spl3_64),
% 2.06/0.69    inference(resolution,[],[f1257,f151])).
% 2.06/0.69  fof(f151,plain,(
% 2.06/0.69    ( ! [X0,X1] : (m1_subset_1(k4_xboole_0(X0,X1),k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(backward_demodulation,[],[f107,f99])).
% 2.06/0.69  fof(f99,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f19])).
% 2.06/0.69  fof(f19,axiom,(
% 2.06/0.69    ! [X0,X1] : k4_xboole_0(X0,X1) = k6_subset_1(X0,X1)),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).
% 2.06/0.69  fof(f107,plain,(
% 2.06/0.69    ( ! [X0,X1] : (m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(cnf_transformation,[],[f14])).
% 2.06/0.69  fof(f14,axiom,(
% 2.06/0.69    ! [X0,X1] : m1_subset_1(k6_subset_1(X0,X1),k1_zfmisc_1(X0))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).
% 2.06/0.69  fof(f1257,plain,(
% 2.06/0.69    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_64),
% 2.06/0.69    inference(avatar_component_clause,[],[f1256])).
% 2.06/0.69  fof(f1256,plain,(
% 2.06/0.69    spl3_64 <=> ! [X9] : ~m1_subset_1(X9,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 2.06/0.69  fof(f1979,plain,(
% 2.06/0.69    spl3_37 | ~spl3_3 | ~spl3_4 | ~spl3_78),
% 2.06/0.69    inference(avatar_split_clause,[],[f1978,f1948,f130,f125,f544])).
% 2.06/0.69  fof(f544,plain,(
% 2.06/0.69    spl3_37 <=> sK1 = k1_tops_1(sK0,sK1)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 2.06/0.69  fof(f125,plain,(
% 2.06/0.69    spl3_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 2.06/0.69  fof(f130,plain,(
% 2.06/0.69    spl3_4 <=> l1_pre_topc(sK0)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 2.06/0.69  fof(f1948,plain,(
% 2.06/0.69    spl3_78 <=> sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 2.06/0.69  fof(f1978,plain,(
% 2.06/0.69    sK1 = k1_tops_1(sK0,sK1) | (~spl3_3 | ~spl3_4 | ~spl3_78)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1977,f132])).
% 2.06/0.69  fof(f132,plain,(
% 2.06/0.69    l1_pre_topc(sK0) | ~spl3_4),
% 2.06/0.69    inference(avatar_component_clause,[],[f130])).
% 2.06/0.69  fof(f1977,plain,(
% 2.06/0.69    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0) | (~spl3_3 | ~spl3_78)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1956,f127])).
% 2.06/0.69  fof(f127,plain,(
% 2.06/0.69    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_3),
% 2.06/0.69    inference(avatar_component_clause,[],[f125])).
% 2.06/0.69  fof(f1956,plain,(
% 2.06/0.69    sK1 = k1_tops_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_78),
% 2.06/0.69    inference(superposition,[],[f286,f1950])).
% 2.06/0.69  fof(f1950,plain,(
% 2.06/0.69    sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~spl3_78),
% 2.06/0.69    inference(avatar_component_clause,[],[f1948])).
% 2.06/0.69  fof(f286,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.69    inference(duplicate_literal_removal,[],[f285])).
% 2.06/0.69  fof(f285,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k4_xboole_0(X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.69    inference(superposition,[],[f72,f81])).
% 2.06/0.69  fof(f81,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f41])).
% 2.06/0.69  fof(f41,plain,(
% 2.06/0.69    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.69    inference(ennf_transformation,[],[f30])).
% 2.06/0.69  fof(f30,axiom,(
% 2.06/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),X1,k2_tops_1(X0,X1))))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_1)).
% 2.06/0.69  fof(f72,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(cnf_transformation,[],[f36])).
% 2.06/0.69  fof(f36,plain,(
% 2.06/0.69    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.69    inference(ennf_transformation,[],[f20])).
% 2.06/0.69  fof(f20,axiom,(
% 2.06/0.69    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 2.06/0.69  fof(f1951,plain,(
% 2.06/0.69    spl3_64 | spl3_78 | ~spl3_24 | ~spl3_32),
% 2.06/0.69    inference(avatar_split_clause,[],[f1946,f468,f365,f1948,f1256])).
% 2.06/0.69  fof(f365,plain,(
% 2.06/0.69    spl3_24 <=> m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 2.06/0.69  fof(f468,plain,(
% 2.06/0.69    spl3_32 <=> sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 2.06/0.69  fof(f1946,plain,(
% 2.06/0.69    ( ! [X13] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | (~spl3_24 | ~spl3_32)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1922,f367])).
% 2.06/0.69  fof(f367,plain,(
% 2.06/0.69    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_24),
% 2.06/0.69    inference(avatar_component_clause,[],[f365])).
% 2.06/0.69  fof(f1922,plain,(
% 2.06/0.69    ( ! [X13] : (sK1 = k4_xboole_0(sK1,k2_tops_1(sK0,sK1)) | ~m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~m1_subset_1(X13,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))) ) | ~spl3_32),
% 2.06/0.69    inference(superposition,[],[f631,f470])).
% 2.06/0.69  fof(f470,plain,(
% 2.06/0.69    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~spl3_32),
% 2.06/0.69    inference(avatar_component_clause,[],[f468])).
% 2.06/0.69  fof(f631,plain,(
% 2.06/0.69    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2))) )),
% 2.06/0.69    inference(subsumption_resolution,[],[f626,f89])).
% 2.06/0.69  fof(f89,plain,(
% 2.06/0.69    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(cnf_transformation,[],[f50])).
% 2.06/0.69  fof(f50,plain,(
% 2.06/0.69    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.69    inference(ennf_transformation,[],[f13])).
% 2.06/0.69  fof(f13,axiom,(
% 2.06/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 2.06/0.69  fof(f626,plain,(
% 2.06/0.69    ( ! [X4,X2,X3] : (k3_subset_1(X2,X3) = k4_xboole_0(k3_subset_1(X2,X3),X3) | ~m1_subset_1(X3,k1_zfmisc_1(X2)) | ~m1_subset_1(X4,k1_zfmisc_1(X2)) | ~m1_subset_1(k3_subset_1(X2,X3),k1_zfmisc_1(X2))) )),
% 2.06/0.69    inference(superposition,[],[f318,f72])).
% 2.06/0.69  fof(f318,plain,(
% 2.06/0.69    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 2.06/0.69    inference(subsumption_resolution,[],[f314,f89])).
% 2.06/0.69  fof(f314,plain,(
% 2.06/0.69    ( ! [X4,X5,X3] : (k3_subset_1(X3,X4) = k7_subset_1(X3,k3_subset_1(X3,X4),X4) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | ~m1_subset_1(k3_subset_1(X3,X4),k1_zfmisc_1(X3)) | ~m1_subset_1(X5,k1_zfmisc_1(X3))) )),
% 2.06/0.69    inference(superposition,[],[f79,f104])).
% 2.06/0.69  fof(f104,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(cnf_transformation,[],[f52])).
% 2.06/0.69  fof(f52,plain,(
% 2.06/0.69    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X1) = X1 | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 2.06/0.69    inference(ennf_transformation,[],[f15])).
% 2.06/0.69  fof(f15,axiom,(
% 2.06/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X1) = X1)),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k9_subset_1)).
% 2.06/0.69  fof(f79,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(cnf_transformation,[],[f39])).
% 2.06/0.69  fof(f39,plain,(
% 2.06/0.69    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.69    inference(ennf_transformation,[],[f21])).
% 2.06/0.69  fof(f21,axiom,(
% 2.06/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).
% 2.06/0.69  fof(f1287,plain,(
% 2.06/0.69    spl3_24 | ~spl3_12),
% 2.06/0.69    inference(avatar_split_clause,[],[f1275,f223,f365])).
% 2.06/0.69  fof(f223,plain,(
% 2.06/0.69    spl3_12 <=> k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 2.06/0.69  fof(f1275,plain,(
% 2.06/0.69    m1_subset_1(k2_tops_1(sK0,sK1),k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_12),
% 2.06/0.69    inference(superposition,[],[f151,f225])).
% 2.06/0.69  fof(f225,plain,(
% 2.06/0.69    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~spl3_12),
% 2.06/0.69    inference(avatar_component_clause,[],[f223])).
% 2.06/0.69  fof(f1269,plain,(
% 2.06/0.69    spl3_12 | ~spl3_2 | ~spl3_11),
% 2.06/0.69    inference(avatar_split_clause,[],[f1268,f219,f119,f223])).
% 2.06/0.69  fof(f119,plain,(
% 2.06/0.69    spl3_2 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 2.06/0.69  fof(f219,plain,(
% 2.06/0.69    spl3_11 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 2.06/0.69  fof(f1268,plain,(
% 2.06/0.69    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (~spl3_2 | ~spl3_11)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1265,f220])).
% 2.06/0.69  fof(f220,plain,(
% 2.06/0.69    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_11),
% 2.06/0.69    inference(avatar_component_clause,[],[f219])).
% 2.06/0.69  fof(f1265,plain,(
% 2.06/0.69    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_2),
% 2.06/0.69    inference(superposition,[],[f72,f120])).
% 2.06/0.69  fof(f120,plain,(
% 2.06/0.69    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~spl3_2),
% 2.06/0.69    inference(avatar_component_clause,[],[f119])).
% 2.06/0.69  fof(f1240,plain,(
% 2.06/0.69    ~spl3_1 | spl3_37 | ~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_36),
% 2.06/0.69    inference(avatar_split_clause,[],[f1194,f540,f146,f130,f125,f544,f115])).
% 2.06/0.69  fof(f115,plain,(
% 2.06/0.69    spl3_1 <=> v3_pre_topc(sK1,sK0)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 2.06/0.69  fof(f146,plain,(
% 2.06/0.69    spl3_6 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 2.06/0.69  fof(f540,plain,(
% 2.06/0.69    spl3_36 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 2.06/0.69  fof(f1194,plain,(
% 2.06/0.69    sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_6 | ~spl3_36)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1193,f148])).
% 2.06/0.69  fof(f148,plain,(
% 2.06/0.69    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_6),
% 2.06/0.69    inference(avatar_component_clause,[],[f146])).
% 2.06/0.69  fof(f1193,plain,(
% 2.06/0.69    ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_36)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1187,f109])).
% 2.06/0.69  fof(f109,plain,(
% 2.06/0.69    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.06/0.69    inference(equality_resolution,[],[f74])).
% 2.06/0.69  fof(f74,plain,(
% 2.06/0.69    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 2.06/0.69    inference(cnf_transformation,[],[f60])).
% 2.06/0.69  fof(f60,plain,(
% 2.06/0.69    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.69    inference(flattening,[],[f59])).
% 2.06/0.69  fof(f59,plain,(
% 2.06/0.69    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.06/0.69    inference(nnf_transformation,[],[f3])).
% 2.06/0.69  fof(f3,axiom,(
% 2.06/0.69    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.06/0.69  fof(f1187,plain,(
% 2.06/0.69    ~r1_tarski(sK1,sK1) | ~r1_tarski(sK1,u1_struct_0(sK0)) | sK1 = k1_tops_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0) | (~spl3_3 | ~spl3_4 | ~spl3_36)),
% 2.06/0.69    inference(resolution,[],[f541,f621])).
% 2.06/0.69  fof(f621,plain,(
% 2.06/0.69    ( ! [X2] : (~r1_tarski(k1_tops_1(sK0,sK1),X2) | ~r1_tarski(X2,sK1) | ~r1_tarski(X2,u1_struct_0(sK0)) | k1_tops_1(sK0,sK1) = X2 | ~v3_pre_topc(X2,sK0)) ) | (~spl3_3 | ~spl3_4)),
% 2.06/0.69    inference(resolution,[],[f376,f75])).
% 2.06/0.69  fof(f75,plain,(
% 2.06/0.69    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f60])).
% 2.06/0.69  fof(f376,plain,(
% 2.06/0.69    ( ! [X0] : (r1_tarski(X0,k1_tops_1(sK0,sK1)) | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,sK1) | ~r1_tarski(X0,u1_struct_0(sK0))) ) | (~spl3_3 | ~spl3_4)),
% 2.06/0.69    inference(resolution,[],[f342,f88])).
% 2.06/0.69  fof(f88,plain,(
% 2.06/0.69    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f61])).
% 2.06/0.69  fof(f61,plain,(
% 2.06/0.69    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.06/0.69    inference(nnf_transformation,[],[f23])).
% 2.06/0.69  fof(f23,axiom,(
% 2.06/0.69    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 2.06/0.69  fof(f342,plain,(
% 2.06/0.69    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X13,sK0) | r1_tarski(X13,k1_tops_1(sK0,sK1)) | ~r1_tarski(X13,sK1)) ) | (~spl3_3 | ~spl3_4)),
% 2.06/0.69    inference(subsumption_resolution,[],[f339,f132])).
% 2.06/0.69  fof(f339,plain,(
% 2.06/0.69    ( ! [X13] : (~r1_tarski(X13,sK1) | ~v3_pre_topc(X13,sK0) | r1_tarski(X13,k1_tops_1(sK0,sK1)) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl3_3),
% 2.06/0.69    inference(resolution,[],[f86,f127])).
% 2.06/0.69  fof(f86,plain,(
% 2.06/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | r1_tarski(X1,k1_tops_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f49])).
% 2.06/0.69  fof(f49,plain,(
% 2.06/0.69    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(X1,k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.69    inference(flattening,[],[f48])).
% 2.06/0.69  fof(f48,plain,(
% 2.06/0.69    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(X1,k1_tops_1(X0,X2)) | (~r1_tarski(X1,X2) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.69    inference(ennf_transformation,[],[f28])).
% 2.06/0.69  fof(f28,axiom,(
% 2.06/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v3_pre_topc(X1,X0)) => r1_tarski(X1,k1_tops_1(X0,X2))))))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_tops_1)).
% 2.06/0.69  fof(f541,plain,(
% 2.06/0.69    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl3_36),
% 2.06/0.69    inference(avatar_component_clause,[],[f540])).
% 2.06/0.69  fof(f1235,plain,(
% 2.06/0.69    ~spl3_3 | ~spl3_4 | spl3_12 | ~spl3_37),
% 2.06/0.69    inference(avatar_contradiction_clause,[],[f1234])).
% 2.06/0.69  fof(f1234,plain,(
% 2.06/0.69    $false | (~spl3_3 | ~spl3_4 | spl3_12 | ~spl3_37)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1233,f132])).
% 2.06/0.69  fof(f1233,plain,(
% 2.06/0.69    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_12 | ~spl3_37)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1232,f127])).
% 2.06/0.69  fof(f1232,plain,(
% 2.06/0.69    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (spl3_12 | ~spl3_37)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1228,f224])).
% 2.06/0.69  fof(f224,plain,(
% 2.06/0.69    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | spl3_12),
% 2.06/0.69    inference(avatar_component_clause,[],[f223])).
% 2.06/0.69  fof(f1228,plain,(
% 2.06/0.69    k2_tops_1(sK0,sK1) = k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl3_37),
% 2.06/0.69    inference(superposition,[],[f332,f546])).
% 2.06/0.69  fof(f546,plain,(
% 2.06/0.69    sK1 = k1_tops_1(sK0,sK1) | ~spl3_37),
% 2.06/0.69    inference(avatar_component_clause,[],[f544])).
% 2.06/0.69  fof(f332,plain,(
% 2.06/0.69    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 2.06/0.69    inference(subsumption_resolution,[],[f330,f82])).
% 2.06/0.69  fof(f82,plain,(
% 2.06/0.69    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f43])).
% 2.06/0.69  fof(f43,plain,(
% 2.06/0.69    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 2.06/0.69    inference(flattening,[],[f42])).
% 2.06/0.69  fof(f42,plain,(
% 2.06/0.69    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 2.06/0.69    inference(ennf_transformation,[],[f24])).
% 2.06/0.69  fof(f24,axiom,(
% 2.06/0.69    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 2.06/0.69  fof(f330,plain,(
% 2.06/0.69    ( ! [X2,X3] : (k2_tops_1(X2,X3) = k4_xboole_0(k2_pre_topc(X2,X3),k1_tops_1(X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2) | ~m1_subset_1(k2_pre_topc(X2,X3),k1_zfmisc_1(u1_struct_0(X2)))) )),
% 2.06/0.69    inference(superposition,[],[f80,f72])).
% 2.06/0.69  fof(f80,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f40])).
% 2.06/0.69  fof(f40,plain,(
% 2.06/0.69    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.06/0.69    inference(ennf_transformation,[],[f27])).
% 2.06/0.69  fof(f27,axiom,(
% 2.06/0.69    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l78_tops_1)).
% 2.06/0.69  fof(f1180,plain,(
% 2.06/0.69    spl3_36 | ~spl3_3 | ~spl3_4),
% 2.06/0.69    inference(avatar_split_clause,[],[f1179,f130,f125,f540])).
% 2.06/0.69  fof(f1179,plain,(
% 2.06/0.69    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl3_3 | ~spl3_4)),
% 2.06/0.69    inference(subsumption_resolution,[],[f1169,f132])).
% 2.06/0.69  fof(f1169,plain,(
% 2.06/0.69    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~l1_pre_topc(sK0) | ~spl3_3),
% 2.06/0.69    inference(resolution,[],[f590,f127])).
% 2.06/0.69  fof(f590,plain,(
% 2.06/0.69    ( ! [X15,X16] : (~m1_subset_1(X15,k1_zfmisc_1(u1_struct_0(X16))) | r1_tarski(k1_tops_1(X16,X15),X15) | ~l1_pre_topc(X16)) )),
% 2.06/0.69    inference(superposition,[],[f152,f286])).
% 2.06/0.69  fof(f152,plain,(
% 2.06/0.69    ( ! [X0,X1] : (r1_tarski(k4_xboole_0(X0,X1),X0)) )),
% 2.06/0.69    inference(forward_demodulation,[],[f144,f99])).
% 2.06/0.69  fof(f144,plain,(
% 2.06/0.69    ( ! [X0,X1] : (r1_tarski(k6_subset_1(X0,X1),X0)) )),
% 2.06/0.69    inference(resolution,[],[f87,f107])).
% 2.06/0.69  fof(f87,plain,(
% 2.06/0.69    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 2.06/0.69    inference(cnf_transformation,[],[f61])).
% 2.06/0.69  fof(f550,plain,(
% 2.06/0.69    ~spl3_12 | spl3_2 | ~spl3_11),
% 2.06/0.69    inference(avatar_split_clause,[],[f549,f219,f119,f223])).
% 2.06/0.69  fof(f549,plain,(
% 2.06/0.69    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | (spl3_2 | ~spl3_11)),
% 2.06/0.69    inference(subsumption_resolution,[],[f548,f220])).
% 2.06/0.69  fof(f548,plain,(
% 2.06/0.69    k2_tops_1(sK0,sK1) != k4_xboole_0(k2_pre_topc(sK0,sK1),sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_2),
% 2.06/0.69    inference(superposition,[],[f121,f72])).
% 2.06/0.69  fof(f121,plain,(
% 2.06/0.69    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl3_2),
% 2.06/0.69    inference(avatar_component_clause,[],[f119])).
% 2.06/0.69  fof(f492,plain,(
% 2.06/0.69    ~spl3_13 | spl3_31),
% 2.06/0.69    inference(avatar_contradiction_clause,[],[f491])).
% 2.06/0.69  fof(f491,plain,(
% 2.06/0.69    $false | (~spl3_13 | spl3_31)),
% 2.06/0.69    inference(subsumption_resolution,[],[f489,f236])).
% 2.06/0.69  fof(f236,plain,(
% 2.06/0.69    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~spl3_13),
% 2.06/0.69    inference(avatar_component_clause,[],[f234])).
% 2.06/0.69  fof(f234,plain,(
% 2.06/0.69    spl3_13 <=> r1_tarski(sK1,k2_pre_topc(sK0,sK1))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 2.06/0.69  fof(f489,plain,(
% 2.06/0.69    ~r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | spl3_31),
% 2.06/0.69    inference(resolution,[],[f466,f88])).
% 2.06/0.69  fof(f466,plain,(
% 2.06/0.69    ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | spl3_31),
% 2.06/0.69    inference(avatar_component_clause,[],[f464])).
% 2.06/0.69  fof(f464,plain,(
% 2.06/0.69    spl3_31 <=> m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1)))),
% 2.06/0.69    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 2.06/0.69  fof(f471,plain,(
% 2.06/0.69    ~spl3_31 | spl3_32 | ~spl3_12),
% 2.06/0.69    inference(avatar_split_clause,[],[f455,f223,f468,f464])).
% 2.06/0.69  fof(f455,plain,(
% 2.06/0.69    sK1 = k3_subset_1(k2_pre_topc(sK0,sK1),k2_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_pre_topc(sK0,sK1))) | ~spl3_12),
% 2.06/0.69    inference(superposition,[],[f207,f225])).
% 2.06/0.69  fof(f207,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(duplicate_literal_removal,[],[f203])).
% 2.06/0.69  fof(f203,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k3_subset_1(X0,k4_xboole_0(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(superposition,[],[f76,f77])).
% 2.06/0.69  fof(f77,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(cnf_transformation,[],[f38])).
% 2.06/0.69  fof(f38,plain,(
% 2.06/0.69    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.06/0.69    inference(ennf_transformation,[],[f12])).
% 2.06/0.69  fof(f12,axiom,(
% 2.06/0.69    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 2.06/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).
% 2.06/0.69  fof(f76,plain,(
% 2.06/0.69    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 2.06/0.69    inference(cnf_transformation,[],[f37])).
% 2.06/0.71  % (16882)lrs+11_2:1_av=off:bsr=on:gs=on:gsem=on:irw=on:lma=on:lwlo=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sp=reverse_arity_4 on theBenchmark
% 2.71/0.71  fof(f37,plain,(
% 2.71/0.71    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.71/0.71    inference(ennf_transformation,[],[f16])).
% 2.71/0.71  fof(f16,axiom,(
% 2.71/0.71    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 2.71/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 2.71/0.71  fof(f278,plain,(
% 2.71/0.71    ~spl3_3 | ~spl3_4 | spl3_11),
% 2.71/0.71    inference(avatar_contradiction_clause,[],[f277])).
% 2.71/0.71  fof(f277,plain,(
% 2.71/0.71    $false | (~spl3_3 | ~spl3_4 | spl3_11)),
% 2.71/0.71    inference(subsumption_resolution,[],[f276,f132])).
% 2.71/0.71  fof(f276,plain,(
% 2.71/0.71    ~l1_pre_topc(sK0) | (~spl3_3 | spl3_11)),
% 2.71/0.71    inference(subsumption_resolution,[],[f273,f127])).
% 2.71/0.71  fof(f273,plain,(
% 2.71/0.71    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl3_11),
% 2.71/0.71    inference(resolution,[],[f221,f82])).
% 2.71/0.71  fof(f221,plain,(
% 2.71/0.71    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl3_11),
% 2.71/0.71    inference(avatar_component_clause,[],[f219])).
% 2.71/0.71  fof(f264,plain,(
% 2.71/0.71    spl3_16 | ~spl3_3 | ~spl3_4 | ~spl3_5),
% 2.71/0.71    inference(avatar_split_clause,[],[f259,f135,f130,f125,f261])).
% 2.71/0.71  fof(f261,plain,(
% 2.71/0.71    spl3_16 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 2.71/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 2.71/0.71  fof(f135,plain,(
% 2.71/0.71    spl3_5 <=> v2_pre_topc(sK0)),
% 2.71/0.71    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 2.71/0.71  fof(f259,plain,(
% 2.71/0.71    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl3_3 | ~spl3_4 | ~spl3_5)),
% 2.71/0.71    inference(subsumption_resolution,[],[f258,f137])).
% 2.71/0.71  fof(f137,plain,(
% 2.71/0.71    v2_pre_topc(sK0) | ~spl3_5),
% 2.71/0.71    inference(avatar_component_clause,[],[f135])).
% 2.71/0.71  fof(f258,plain,(
% 2.71/0.71    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~v2_pre_topc(sK0) | (~spl3_3 | ~spl3_4)),
% 2.71/0.71    inference(subsumption_resolution,[],[f256,f132])).
% 2.71/0.71  fof(f256,plain,(
% 2.71/0.71    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~spl3_3),
% 2.71/0.71    inference(resolution,[],[f85,f127])).
% 2.71/0.71  fof(f85,plain,(
% 2.71/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k1_tops_1(X0,X1),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 2.71/0.71    inference(cnf_transformation,[],[f47])).
% 2.71/0.71  fof(f47,plain,(
% 2.71/0.71    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.71/0.71    inference(flattening,[],[f46])).
% 2.71/0.71  fof(f46,plain,(
% 2.71/0.71    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.71/0.71    inference(ennf_transformation,[],[f26])).
% 2.71/0.71  fof(f26,axiom,(
% 2.71/0.71    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 2.71/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_tops_1)).
% 2.71/0.71  fof(f237,plain,(
% 2.71/0.71    spl3_13 | ~spl3_3 | ~spl3_4),
% 2.71/0.71    inference(avatar_split_clause,[],[f232,f130,f125,f234])).
% 2.71/0.71  fof(f232,plain,(
% 2.71/0.71    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | (~spl3_3 | ~spl3_4)),
% 2.71/0.71    inference(subsumption_resolution,[],[f231,f132])).
% 2.71/0.71  fof(f231,plain,(
% 2.71/0.71    r1_tarski(sK1,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~spl3_3),
% 2.71/0.71    inference(resolution,[],[f83,f127])).
% 2.71/0.71  fof(f83,plain,(
% 2.71/0.71    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r1_tarski(X1,k2_pre_topc(X0,X1)) | ~l1_pre_topc(X0)) )),
% 2.71/0.71    inference(cnf_transformation,[],[f44])).
% 2.71/0.71  fof(f44,plain,(
% 2.71/0.71    ! [X0] : (! [X1] : (r1_tarski(X1,k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 2.71/0.71    inference(ennf_transformation,[],[f25])).
% 2.71/0.71  fof(f25,axiom,(
% 2.71/0.71    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(X1,k2_pre_topc(X0,X1))))),
% 2.71/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_pre_topc)).
% 2.71/0.71  fof(f149,plain,(
% 2.71/0.71    spl3_6 | ~spl3_3),
% 2.71/0.71    inference(avatar_split_clause,[],[f143,f125,f146])).
% 2.71/0.71  fof(f143,plain,(
% 2.71/0.71    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl3_3),
% 2.71/0.71    inference(resolution,[],[f87,f127])).
% 2.71/0.71  fof(f138,plain,(
% 2.71/0.71    spl3_5),
% 2.71/0.71    inference(avatar_split_clause,[],[f67,f135])).
% 2.71/0.71  fof(f67,plain,(
% 2.71/0.71    v2_pre_topc(sK0)),
% 2.71/0.71    inference(cnf_transformation,[],[f58])).
% 2.71/0.71  fof(f58,plain,(
% 2.71/0.71    ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 2.71/0.71    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f55,f57,f56])).
% 2.71/0.71  fof(f56,plain,(
% 2.71/0.71    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 2.71/0.71    introduced(choice_axiom,[])).
% 2.71/0.71  fof(f57,plain,(
% 2.71/0.71    ? [X1] : ((k2_tops_1(sK0,X1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | ~v3_pre_topc(X1,sK0)) & (k2_tops_1(sK0,X1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,X1),X1) | v3_pre_topc(X1,sK0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => ((k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)) & (k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 2.71/0.71    introduced(choice_axiom,[])).
% 2.71/0.71  fof(f55,plain,(
% 2.71/0.71    ? [X0] : (? [X1] : ((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.71/0.71    inference(flattening,[],[f54])).
% 2.71/0.71  fof(f54,plain,(
% 2.71/0.71    ? [X0] : (? [X1] : (((k2_tops_1(X0,X1) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | ~v3_pre_topc(X1,X0)) & (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.71/0.71    inference(nnf_transformation,[],[f35])).
% 2.71/0.71  fof(f35,plain,(
% 2.71/0.71    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 2.71/0.71    inference(flattening,[],[f34])).
% 2.71/0.71  fof(f34,plain,(
% 2.71/0.71    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 2.71/0.71    inference(ennf_transformation,[],[f32])).
% 2.71/0.71  fof(f32,negated_conjecture,(
% 2.71/0.71    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.71/0.71    inference(negated_conjecture,[],[f31])).
% 2.71/0.71  fof(f31,conjecture,(
% 2.71/0.71    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1))))),
% 2.71/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_tops_1)).
% 2.71/0.71  fof(f133,plain,(
% 2.71/0.71    spl3_4),
% 2.71/0.71    inference(avatar_split_clause,[],[f68,f130])).
% 2.71/0.71  fof(f68,plain,(
% 2.71/0.71    l1_pre_topc(sK0)),
% 2.71/0.71    inference(cnf_transformation,[],[f58])).
% 2.71/0.71  fof(f128,plain,(
% 2.71/0.71    spl3_3),
% 2.71/0.71    inference(avatar_split_clause,[],[f69,f125])).
% 2.71/0.71  fof(f69,plain,(
% 2.71/0.71    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.71/0.71    inference(cnf_transformation,[],[f58])).
% 2.71/0.71  fof(f123,plain,(
% 2.71/0.71    spl3_1 | spl3_2),
% 2.71/0.71    inference(avatar_split_clause,[],[f70,f119,f115])).
% 2.71/0.71  fof(f70,plain,(
% 2.71/0.71    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | v3_pre_topc(sK1,sK0)),
% 2.71/0.71    inference(cnf_transformation,[],[f58])).
% 2.71/0.71  fof(f122,plain,(
% 2.71/0.71    ~spl3_1 | ~spl3_2),
% 2.71/0.71    inference(avatar_split_clause,[],[f71,f119,f115])).
% 2.71/0.71  fof(f71,plain,(
% 2.71/0.71    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | ~v3_pre_topc(sK1,sK0)),
% 2.71/0.71    inference(cnf_transformation,[],[f58])).
% 2.71/0.71  % SZS output end Proof for theBenchmark
% 2.71/0.71  % (16860)------------------------------
% 2.71/0.71  % (16860)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.71/0.71  % (16860)Termination reason: Refutation
% 2.71/0.71  
% 2.71/0.71  % (16860)Memory used [KB]: 7803
% 2.71/0.71  % (16860)Time elapsed: 0.288 s
% 2.71/0.71  % (16860)------------------------------
% 2.71/0.71  % (16860)------------------------------
% 2.71/0.71  % (16838)Success in time 0.345 s
%------------------------------------------------------------------------------
