%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:53 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 233 expanded)
%              Number of leaves         :   20 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  273 (1014 expanded)
%              Number of equality atoms :   21 (  36 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f272,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f58,f94,f110,f131,f187,f197,f246,f250,f270])).

fof(f270,plain,
    ( spl5_21
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_31 ),
    inference(avatar_split_clause,[],[f262,f242,f185,f88,f182])).

fof(f182,plain,
    ( spl5_21
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f88,plain,
    ( spl5_5
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f185,plain,
    ( spl5_22
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f242,plain,
    ( spl5_31
  <=> k1_xboole_0 = u1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).

fof(f262,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_31 ),
    inference(superposition,[],[f45,f243])).

fof(f243,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl5_31 ),
    inference(avatar_component_clause,[],[f242])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f250,plain,
    ( ~ spl5_5
    | ~ spl5_4
    | spl5_31
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f249,f53,f242,f85,f88])).

fof(f85,plain,
    ( spl5_4
  <=> l1_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f53,plain,
    ( spl5_1
  <=> r1_tsep_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f249,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f247,f76])).

fof(f76,plain,(
    u1_struct_0(sK1) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(global_subsumption,[],[f62,f73])).

fof(f73,plain,
    ( ~ l1_pre_topc(sK2)
    | u1_struct_0(sK1) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(resolution,[],[f68,f34])).

fof(f34,plain,(
    m1_pre_topc(sK1,sK2) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( r1_tsep_1(X2,X1)
                | r1_tsep_1(X1,X2) )
              & m1_pre_topc(X1,X2)
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,plain,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ( m1_pre_topc(X1,X2)
                 => ( ~ r1_tsep_1(X2,X1)
                    & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( m1_pre_topc(X1,X2)
               => ( ~ r1_tsep_1(X2,X1)
                  & ~ r1_tsep_1(X1,X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(resolution,[],[f67,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X1)
      | ~ m1_pre_topc(X0,X1) ) ),
    inference(resolution,[],[f44,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f62,plain,(
    l1_pre_topc(sK2) ),
    inference(global_subsumption,[],[f38,f59])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2) ),
    inference(resolution,[],[f43,f33])).

fof(f33,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f247,plain,
    ( ~ l1_struct_0(sK2)
    | k1_xboole_0 = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ l1_struct_0(sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f54,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | k1_xboole_0 = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ l1_struct_0(X0)
      | ~ l1_struct_0(X1)
      | k1_xboole_0 = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1) ) ),
    inference(resolution,[],[f70,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ l1_struct_0(X1)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f70,plain,(
    ! [X2,X3] :
      ( ~ r1_tsep_1(X3,X2)
      | ~ l1_struct_0(X3)
      | ~ l1_struct_0(X2)
      | k1_xboole_0 = k3_xboole_0(u1_struct_0(X3),u1_struct_0(X2)) ) ),
    inference(resolution,[],[f41,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k3_xboole_0(X0,X1) ) ),
    inference(resolution,[],[f47,f46])).

fof(f46,plain,(
    ! [X0] :
      ( r2_hidden(sK3(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ~ ( ! [X1] : ~ r2_hidden(X1,X0)
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,k3_xboole_0(X0,X1))
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ( ? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1))
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X3] : ~ r2_hidden(X3,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1)) )
      & ~ ( ! [X2] : ~ r2_hidden(X2,k3_xboole_0(X0,X1))
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

fof(f41,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0)
      | ~ r1_tsep_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f54,plain,
    ( r1_tsep_1(sK2,sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f53])).

fof(f246,plain,(
    ~ spl5_21 ),
    inference(avatar_contradiction_clause,[],[f245])).

fof(f245,plain,
    ( $false
    | ~ spl5_21 ),
    inference(resolution,[],[f183,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f183,plain,
    ( v2_struct_0(sK1)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f182])).

fof(f197,plain,(
    spl5_22 ),
    inference(avatar_contradiction_clause,[],[f196])).

fof(f196,plain,
    ( $false
    | spl5_22 ),
    inference(resolution,[],[f186,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f186,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl5_22 ),
    inference(avatar_component_clause,[],[f185])).

fof(f187,plain,
    ( spl5_21
    | ~ spl5_5
    | ~ spl5_22
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f155,f82,f185,f88,f182])).

fof(f82,plain,
    ( spl5_3
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f155,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl5_3 ),
    inference(superposition,[],[f45,f145])).

fof(f145,plain,
    ( k1_xboole_0 = u1_struct_0(sK1)
    | ~ spl5_3 ),
    inference(forward_demodulation,[],[f76,f83])).

fof(f83,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f82])).

fof(f131,plain,
    ( spl5_3
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f130,f56,f88,f85,f82])).

fof(f56,plain,
    ( spl5_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f130,plain,
    ( ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK2)
    | k1_xboole_0 = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl5_2 ),
    inference(resolution,[],[f57,f70])).

fof(f57,plain,
    ( r1_tsep_1(sK1,sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f110,plain,(
    spl5_5 ),
    inference(avatar_contradiction_clause,[],[f109])).

fof(f109,plain,
    ( $false
    | spl5_5 ),
    inference(resolution,[],[f92,f63])).

fof(f63,plain,(
    l1_pre_topc(sK1) ),
    inference(global_subsumption,[],[f62,f60])).

fof(f60,plain,
    ( ~ l1_pre_topc(sK2)
    | l1_pre_topc(sK1) ),
    inference(resolution,[],[f43,f34])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK1)
    | spl5_5 ),
    inference(resolution,[],[f89,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f89,plain,
    ( ~ l1_struct_0(sK1)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f94,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f93])).

fof(f93,plain,
    ( $false
    | spl5_4 ),
    inference(resolution,[],[f91,f62])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK2)
    | spl5_4 ),
    inference(resolution,[],[f86,f42])).

fof(f86,plain,
    ( ~ l1_struct_0(sK2)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f85])).

fof(f58,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f31,f56,f53])).

fof(f31,plain,
    ( r1_tsep_1(sK1,sK2)
    | r1_tsep_1(sK2,sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:10:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (24970)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.47  % (24970)Refutation not found, incomplete strategy% (24970)------------------------------
% 0.22/0.47  % (24970)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (24970)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.47  
% 0.22/0.47  % (24970)Memory used [KB]: 1663
% 0.22/0.47  % (24970)Time elapsed: 0.061 s
% 0.22/0.47  % (24970)------------------------------
% 0.22/0.47  % (24970)------------------------------
% 0.22/0.48  % (24953)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.48  % (24960)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.48  % (24960)Refutation not found, incomplete strategy% (24960)------------------------------
% 0.22/0.48  % (24960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (24960)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (24960)Memory used [KB]: 6140
% 0.22/0.48  % (24960)Time elapsed: 0.060 s
% 0.22/0.48  % (24960)------------------------------
% 0.22/0.48  % (24960)------------------------------
% 0.22/0.48  % (24975)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.49  % (24965)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.49  % (24965)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f272,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(avatar_sat_refutation,[],[f58,f94,f110,f131,f187,f197,f246,f250,f270])).
% 0.22/0.49  fof(f270,plain,(
% 0.22/0.49    spl5_21 | ~spl5_5 | ~spl5_22 | ~spl5_31),
% 0.22/0.49    inference(avatar_split_clause,[],[f262,f242,f185,f88,f182])).
% 0.22/0.49  fof(f182,plain,(
% 0.22/0.49    spl5_21 <=> v2_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    spl5_5 <=> l1_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.22/0.49  fof(f185,plain,(
% 0.22/0.49    spl5_22 <=> v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.22/0.49  fof(f242,plain,(
% 0.22/0.49    spl5_31 <=> k1_xboole_0 = u1_struct_0(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_31])])).
% 0.22/0.49  fof(f262,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_31),
% 0.22/0.49    inference(superposition,[],[f45,f243])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    k1_xboole_0 = u1_struct_0(sK1) | ~spl5_31),
% 0.22/0.49    inference(avatar_component_clause,[],[f242])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    ~spl5_5 | ~spl5_4 | spl5_31 | ~spl5_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f249,f53,f242,f85,f88])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    spl5_4 <=> l1_struct_0(sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    spl5_1 <=> r1_tsep_1(sK2,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.22/0.49  fof(f249,plain,(
% 0.22/0.49    k1_xboole_0 = u1_struct_0(sK1) | ~l1_struct_0(sK2) | ~l1_struct_0(sK1) | ~spl5_1),
% 0.22/0.49    inference(forward_demodulation,[],[f247,f76])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    u1_struct_0(sK1) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.49    inference(global_subsumption,[],[f62,f73])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ~l1_pre_topc(sK2) | u1_struct_0(sK1) = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.49    inference(resolution,[],[f68,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    m1_pre_topc(sK1,sK2)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : ((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (? [X2] : (((r1_tsep_1(X2,X1) | r1_tsep_1(X1,X2)) & m1_pre_topc(X1,X2)) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f13])).
% 0.22/0.49  fof(f13,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.22/0.49    inference(negated_conjecture,[],[f12])).
% 0.22/0.49  fof(f12,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) => (~r1_tsep_1(X2,X1) & ~r1_tsep_1(X1,X2))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tmap_1)).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.22/0.49    inference(resolution,[],[f67,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k3_xboole_0(X0,X1) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tarski(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X1) | ~m1_pre_topc(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f44,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) => r1_tarski(X0,X1))),
% 0.22/0.49    inference(unused_predicate_definition_removal,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.49  fof(f44,plain,(
% 0.22/0.49    ( ! [X0,X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    l1_pre_topc(sK2)),
% 0.22/0.49    inference(global_subsumption,[],[f38,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(sK2)),
% 0.22/0.49    inference(resolution,[],[f43,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    m1_pre_topc(sK2,sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f247,plain,(
% 0.22/0.49    ~l1_struct_0(sK2) | k1_xboole_0 = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~l1_struct_0(sK1) | ~spl5_1),
% 0.22/0.49    inference(resolution,[],[f54,f80])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | k1_xboole_0 = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0)) )),
% 0.22/0.49    inference(duplicate_literal_removal,[],[f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~l1_struct_0(X0) | ~l1_struct_0(X1) | k1_xboole_0 = k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X0) | ~r1_tsep_1(X1,X0) | ~l1_struct_0(X1)) )),
% 0.22/0.49    inference(resolution,[],[f70,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~l1_struct_0(X1) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ( ! [X2,X3] : (~r1_tsep_1(X3,X2) | ~l1_struct_0(X3) | ~l1_struct_0(X2) | k1_xboole_0 = k3_xboole_0(u1_struct_0(X3),u1_struct_0(X2))) )),
% 0.22/0.49    inference(resolution,[],[f41,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k3_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(resolution,[],[f47,f46])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK3(X0),X0) | k1_xboole_0 = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (? [X1] : r2_hidden(X1,X0) | k1_xboole_0 = X0)),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : ~(! [X1] : ~r2_hidden(X1,X0) & k1_xboole_0 != X0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (~r2_hidden(X2,k3_xboole_0(X0,X1)) | ~r1_xboole_0(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1))) & (? [X3] : r2_hidden(X3,k3_xboole_0(X0,X1)) | r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(ennf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X3] : ~r2_hidden(X3,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    inference(rectify,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : r2_hidden(X2,k3_xboole_0(X0,X1))) & ~(! [X2] : ~r2_hidden(X2,k3_xboole_0(X0,X1)) & ~r1_xboole_0(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0) | ~r1_tsep_1(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    r1_tsep_1(sK2,sK1) | ~spl5_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f53])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    ~spl5_21),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f245])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    $false | ~spl5_21),
% 0.22/0.49    inference(resolution,[],[f183,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ~v2_struct_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f183,plain,(
% 0.22/0.49    v2_struct_0(sK1) | ~spl5_21),
% 0.22/0.49    inference(avatar_component_clause,[],[f182])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    spl5_22),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f196])).
% 0.22/0.49  fof(f196,plain,(
% 0.22/0.49    $false | spl5_22),
% 0.22/0.49    inference(resolution,[],[f186,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    v1_xboole_0(k1_xboole_0)),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.22/0.49  fof(f186,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | spl5_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f185])).
% 0.22/0.49  fof(f187,plain,(
% 0.22/0.49    spl5_21 | ~spl5_5 | ~spl5_22 | ~spl5_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f155,f82,f185,f88,f182])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    spl5_3 <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.22/0.49  fof(f155,plain,(
% 0.22/0.49    ~v1_xboole_0(k1_xboole_0) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl5_3),
% 0.22/0.49    inference(superposition,[],[f45,f145])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    k1_xboole_0 = u1_struct_0(sK1) | ~spl5_3),
% 0.22/0.49    inference(forward_demodulation,[],[f76,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    k1_xboole_0 = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl5_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f82])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    spl5_3 | ~spl5_4 | ~spl5_5 | ~spl5_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f130,f56,f88,f85,f82])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    spl5_2 <=> r1_tsep_1(sK1,sK2)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ~l1_struct_0(sK1) | ~l1_struct_0(sK2) | k1_xboole_0 = k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl5_2),
% 0.22/0.49    inference(resolution,[],[f57,f70])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    r1_tsep_1(sK1,sK2) | ~spl5_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f56])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl5_5),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f109])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    $false | spl5_5),
% 0.22/0.49    inference(resolution,[],[f92,f63])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    l1_pre_topc(sK1)),
% 0.22/0.49    inference(global_subsumption,[],[f62,f60])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ~l1_pre_topc(sK2) | l1_pre_topc(sK1)),
% 0.22/0.49    inference(resolution,[],[f43,f34])).
% 0.22/0.49  fof(f92,plain,(
% 0.22/0.49    ~l1_pre_topc(sK1) | spl5_5),
% 0.22/0.49    inference(resolution,[],[f89,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ~l1_struct_0(sK1) | spl5_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f88])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl5_4),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f93])).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    $false | spl5_4),
% 0.22/0.49    inference(resolution,[],[f91,f62])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    ~l1_pre_topc(sK2) | spl5_4),
% 0.22/0.49    inference(resolution,[],[f86,f42])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ~l1_struct_0(sK2) | spl5_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f85])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    spl5_1 | spl5_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f56,f53])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    r1_tsep_1(sK1,sK2) | r1_tsep_1(sK2,sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (24965)------------------------------
% 0.22/0.49  % (24965)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (24965)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (24965)Memory used [KB]: 10746
% 0.22/0.49  % (24965)Time elapsed: 0.078 s
% 0.22/0.49  % (24965)------------------------------
% 0.22/0.49  % (24965)------------------------------
% 0.22/0.49  % (24952)Success in time 0.131 s
%------------------------------------------------------------------------------
