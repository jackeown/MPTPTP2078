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
% DateTime   : Thu Dec  3 13:12:54 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 273 expanded)
%              Number of leaves         :   16 (  84 expanded)
%              Depth                    :   13
%              Number of atoms          :  239 ( 748 expanded)
%              Number of equality atoms :   45 (  97 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f371,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f38,f89,f92,f144,f146,f249,f259,f264,f266,f273,f364])).

fof(f364,plain,
    ( ~ spl2_7
    | spl2_33
    | ~ spl2_24
    | ~ spl2_32 ),
    inference(avatar_split_clause,[],[f363,f255,f181,f262,f77])).

fof(f77,plain,
    ( spl2_7
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).

fof(f262,plain,
    ( spl2_33
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).

fof(f181,plain,
    ( spl2_24
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).

fof(f255,plain,
    ( spl2_32
  <=> sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).

fof(f363,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_24
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f358,f274])).

fof(f274,plain,
    ( sK1 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ spl2_32 ),
    inference(forward_demodulation,[],[f97,f256])).

fof(f256,plain,
    ( sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_32 ),
    inference(avatar_component_clause,[],[f255])).

fof(f97,plain,(
    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) ),
    inference(global_subsumption,[],[f20,f93])).

fof(f93,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f65,f19])).

fof(f19,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v6_tops_1(X1,X0)
          <~> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
            <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).

fof(f65,plain,(
    ! [X2,X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | k1_tops_1(X2,k2_pre_topc(X2,X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3))))
      | ~ l1_pre_topc(X2) ) ),
    inference(duplicate_literal_removal,[],[f64])).

fof(f64,plain,(
    ! [X2,X3] :
      ( ~ l1_pre_topc(X2)
      | k1_tops_1(X2,k2_pre_topc(X2,X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | ~ l1_pre_topc(X2) ) ),
    inference(resolution,[],[f21,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f20,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f358,plain,
    ( k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_24 ),
    inference(resolution,[],[f84,f182])).

fof(f182,plain,
    ( m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f42,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ l1_pre_topc(X1)
      | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0))) ) ),
    inference(resolution,[],[f28,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f273,plain,
    ( ~ spl2_7
    | ~ spl2_16
    | spl2_24 ),
    inference(avatar_split_clause,[],[f272,f181,f139,f77])).

fof(f139,plain,
    ( spl2_16
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).

fof(f272,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_24 ),
    inference(resolution,[],[f251,f28])).

fof(f251,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_24 ),
    inference(avatar_component_clause,[],[f181])).

fof(f266,plain,
    ( ~ spl2_2
    | ~ spl2_7
    | spl2_33
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f241,f80,f262,f77,f33])).

fof(f33,plain,
    ( spl2_2
  <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f80,plain,
    ( spl2_8
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f241,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f225,f157])).

fof(f157,plain,(
    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(global_subsumption,[],[f20,f156])).

fof(f156,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f150,f39])).

fof(f39,plain,(
    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f27,f19])).

fof(f150,plain,
    ( k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f63,f19])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),X1))))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f21,f26])).

fof(f225,plain,
    ( ~ l1_pre_topc(sK0)
    | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_8 ),
    inference(resolution,[],[f205,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1
      | ~ v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f205,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f264,plain,
    ( spl2_2
    | ~ spl2_8
    | ~ spl2_33 ),
    inference(avatar_split_clause,[],[f260,f262,f80,f33])).

fof(f260,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_subsumption,[],[f20,f208])).

fof(f208,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f24,f157])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f259,plain,
    ( ~ spl2_1
    | spl2_32 ),
    inference(avatar_split_clause,[],[f258,f255,f30])).

fof(f30,plain,
    ( spl2_1
  <=> v6_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f258,plain,
    ( sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ v6_tops_1(sK1,sK0) ),
    inference(global_subsumption,[],[f20,f46])).

fof(f46,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ v6_tops_1(sK1,sK0) ),
    inference(resolution,[],[f23,f19])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f249,plain,
    ( spl2_1
    | ~ spl2_7
    | ~ spl2_16
    | ~ spl2_17 ),
    inference(avatar_split_clause,[],[f248,f142,f139,f77,f30])).

fof(f142,plain,
    ( spl2_17
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).

fof(f248,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v6_tops_1(sK1,sK0)
    | ~ spl2_17 ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v6_tops_1(sK1,sK0)
    | ~ spl2_17 ),
    inference(superposition,[],[f22,f244])).

fof(f244,plain,
    ( sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f243,f39])).

fof(f243,plain,
    ( k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ spl2_17 ),
    inference(forward_demodulation,[],[f97,f207])).

fof(f207,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))
    | ~ spl2_17 ),
    inference(backward_demodulation,[],[f143,f157])).

fof(f143,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ spl2_17 ),
    inference(avatar_component_clause,[],[f142])).

fof(f22,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f146,plain,(
    spl2_16 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl2_16 ),
    inference(resolution,[],[f140,f19])).

fof(f140,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_16 ),
    inference(avatar_component_clause,[],[f139])).

fof(f144,plain,
    ( ~ spl2_16
    | ~ spl2_7
    | spl2_17
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f135,f33,f142,f77,f139])).

fof(f135,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_2 ),
    inference(resolution,[],[f51,f37])).

fof(f37,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(resolution,[],[f25,f26])).

fof(f92,plain,(
    spl2_8 ),
    inference(avatar_contradiction_clause,[],[f91])).

fof(f91,plain,
    ( $false
    | spl2_8 ),
    inference(resolution,[],[f90,f19])).

fof(f90,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(resolution,[],[f81,f26])).

fof(f81,plain,
    ( ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_8 ),
    inference(avatar_component_clause,[],[f80])).

fof(f89,plain,(
    spl2_7 ),
    inference(avatar_contradiction_clause,[],[f88])).

fof(f88,plain,
    ( $false
    | spl2_7 ),
    inference(resolution,[],[f78,f20])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f38,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f17,f33,f30])).

fof(f17,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f18,f33,f30])).

fof(f18,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:48:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (5239)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.50  % (5245)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.50  % (5235)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (5247)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.51  % (5238)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (5233)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (5237)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.51  % (5249)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.51  % (5234)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (5245)Refutation found. Thanks to Tanya!
% 0.22/0.51  % SZS status Theorem for theBenchmark
% 0.22/0.51  % (5241)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.52  % (5243)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.52  % (5253)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.52  % (5256)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.52  % (5248)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.52  % (5251)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (5236)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.52  % (5236)Refutation not found, incomplete strategy% (5236)------------------------------
% 0.22/0.52  % (5236)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5246)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (5244)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (5254)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (5240)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (5256)Refutation not found, incomplete strategy% (5256)------------------------------
% 0.22/0.52  % (5256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (5256)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (5256)Memory used [KB]: 10618
% 0.22/0.52  % (5256)Time elapsed: 0.066 s
% 0.22/0.52  % (5256)------------------------------
% 0.22/0.52  % (5256)------------------------------
% 0.22/0.53  % (5242)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.53  % (5236)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (5236)Memory used [KB]: 10490
% 0.22/0.53  % (5236)Time elapsed: 0.099 s
% 0.22/0.53  % (5236)------------------------------
% 0.22/0.53  % (5236)------------------------------
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f371,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(avatar_sat_refutation,[],[f35,f38,f89,f92,f144,f146,f249,f259,f264,f266,f273,f364])).
% 0.22/0.53  fof(f364,plain,(
% 0.22/0.53    ~spl2_7 | spl2_33 | ~spl2_24 | ~spl2_32),
% 0.22/0.53    inference(avatar_split_clause,[],[f363,f255,f181,f262,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    spl2_7 <=> l1_pre_topc(sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_7])])).
% 0.22/0.53  fof(f262,plain,(
% 0.22/0.53    spl2_33 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_33])])).
% 0.22/0.53  fof(f181,plain,(
% 0.22/0.53    spl2_24 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_24])])).
% 0.22/0.53  fof(f255,plain,(
% 0.22/0.53    spl2_32 <=> sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_32])])).
% 0.22/0.53  fof(f363,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0) | (~spl2_24 | ~spl2_32)),
% 0.22/0.53    inference(forward_demodulation,[],[f358,f274])).
% 0.22/0.53  fof(f274,plain,(
% 0.22/0.53    sK1 = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) | ~spl2_32),
% 0.22/0.53    inference(forward_demodulation,[],[f97,f256])).
% 0.22/0.53  fof(f256,plain,(
% 0.22/0.53    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~spl2_32),
% 0.22/0.53    inference(avatar_component_clause,[],[f255])).
% 0.22/0.53  fof(f97,plain,(
% 0.22/0.53    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))),
% 0.22/0.53    inference(global_subsumption,[],[f20,f93])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)))) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(resolution,[],[f65,f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v6_tops_1(X1,X0) <~> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f8])).
% 0.22/0.53  fof(f8,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.53    inference(negated_conjecture,[],[f7])).
% 0.22/0.53  fof(f7,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | k1_tops_1(X2,k2_pre_topc(X2,X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3)))) | ~l1_pre_topc(X2)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f64])).
% 0.22/0.53  fof(f64,plain,(
% 0.22/0.53    ( ! [X2,X3] : (~l1_pre_topc(X2) | k1_tops_1(X2,k2_pre_topc(X2,X3)) = k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,k3_subset_1(u1_struct_0(X2),k2_pre_topc(X2,X3)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | ~l1_pre_topc(X2)) )),
% 0.22/0.53    inference(resolution,[],[f21,f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f4])).
% 0.22/0.53  fof(f4,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.22/0.53  fof(f20,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f358,plain,(
% 0.22/0.53    k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))))) | ~l1_pre_topc(sK0) | ~spl2_24),
% 0.22/0.53    inference(resolution,[],[f84,f182])).
% 0.22/0.53  fof(f182,plain,(
% 0.22/0.53    m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f181])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)) = k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(resolution,[],[f42,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | k2_pre_topc(X1,X0) = k3_subset_1(u1_struct_0(X1),k3_subset_1(u1_struct_0(X1),k2_pre_topc(X1,X0)))) )),
% 0.22/0.53    inference(resolution,[],[f28,f27])).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k3_subset_1(X0,k3_subset_1(X0,X1)) = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.22/0.53  fof(f273,plain,(
% 0.22/0.53    ~spl2_7 | ~spl2_16 | spl2_24),
% 0.22/0.53    inference(avatar_split_clause,[],[f272,f181,f139,f77])).
% 0.22/0.53  fof(f139,plain,(
% 0.22/0.53    spl2_16 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_16])])).
% 0.22/0.53  fof(f272,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_24),
% 0.22/0.53    inference(resolution,[],[f251,f28])).
% 0.22/0.53  fof(f251,plain,(
% 0.22/0.53    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_24),
% 0.22/0.53    inference(avatar_component_clause,[],[f181])).
% 0.22/0.53  fof(f266,plain,(
% 0.22/0.53    ~spl2_2 | ~spl2_7 | spl2_33 | ~spl2_8),
% 0.22/0.53    inference(avatar_split_clause,[],[f241,f80,f262,f77,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    spl2_2 <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    spl2_8 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.53  fof(f241,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0) | ~v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_8),
% 0.22/0.53    inference(forward_demodulation,[],[f225,f157])).
% 0.22/0.53  fof(f157,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.53    inference(global_subsumption,[],[f20,f156])).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(forward_demodulation,[],[f150,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    sK1 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1))),
% 0.22/0.53    inference(resolution,[],[f27,f19])).
% 0.22/0.53  fof(f150,plain,(
% 0.22/0.53    k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)))) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(resolution,[],[f63,f19])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1)) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),k3_subset_1(u1_struct_0(X0),X1)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(resolution,[],[f21,f26])).
% 0.22/0.53  fof(f225,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_8),
% 0.22/0.53    inference(resolution,[],[f205,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 | ~v5_tops_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f80])).
% 0.22/0.53  fof(f264,plain,(
% 0.22/0.53    spl2_2 | ~spl2_8 | ~spl2_33),
% 0.22/0.53    inference(avatar_split_clause,[],[f260,f262,f80,f33])).
% 0.22/0.53  fof(f260,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.53    inference(global_subsumption,[],[f20,f208])).
% 0.22/0.53  fof(f208,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),sK1) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.22/0.53    inference(superposition,[],[f24,f157])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v5_tops_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f259,plain,(
% 0.22/0.53    ~spl2_1 | spl2_32),
% 0.22/0.53    inference(avatar_split_clause,[],[f258,f255,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    spl2_1 <=> v6_tops_1(sK1,sK0)),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.53  fof(f258,plain,(
% 0.22/0.53    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~v6_tops_1(sK1,sK0)),
% 0.22/0.53    inference(global_subsumption,[],[f20,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~v6_tops_1(sK1,sK0)),
% 0.22/0.53    inference(resolution,[],[f23,f19])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 0.22/0.53  fof(f249,plain,(
% 0.22/0.53    spl2_1 | ~spl2_7 | ~spl2_16 | ~spl2_17),
% 0.22/0.53    inference(avatar_split_clause,[],[f248,f142,f139,f77,f30])).
% 0.22/0.53  fof(f142,plain,(
% 0.22/0.53    spl2_17 <=> k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1)))),
% 0.22/0.53    introduced(avatar_definition,[new_symbols(naming,[spl2_17])])).
% 0.22/0.53  fof(f248,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v6_tops_1(sK1,sK0) | ~spl2_17),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f245])).
% 0.22/0.53  fof(f245,plain,(
% 0.22/0.53    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v6_tops_1(sK1,sK0) | ~spl2_17),
% 0.22/0.53    inference(superposition,[],[f22,f244])).
% 0.22/0.53  fof(f244,plain,(
% 0.22/0.53    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~spl2_17),
% 0.22/0.53    inference(forward_demodulation,[],[f243,f39])).
% 0.22/0.53  fof(f243,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1)) = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~spl2_17),
% 0.22/0.53    inference(forward_demodulation,[],[f97,f207])).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1))) | ~spl2_17),
% 0.22/0.53    inference(backward_demodulation,[],[f143,f157])).
% 0.22/0.53  fof(f143,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~spl2_17),
% 0.22/0.53    inference(avatar_component_clause,[],[f142])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ( ! [X0,X1] : (k1_tops_1(X0,k2_pre_topc(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v6_tops_1(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f146,plain,(
% 0.22/0.53    spl2_16),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f145])).
% 0.22/0.53  fof(f145,plain,(
% 0.22/0.53    $false | spl2_16),
% 0.22/0.53    inference(resolution,[],[f140,f19])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_16),
% 0.22/0.53    inference(avatar_component_clause,[],[f139])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    ~spl2_16 | ~spl2_7 | spl2_17 | ~spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f135,f33,f142,f77,f139])).
% 0.22/0.53  fof(f135,plain,(
% 0.22/0.53    k3_subset_1(u1_struct_0(sK0),sK1) = k2_pre_topc(sK0,k1_tops_1(sK0,k3_subset_1(u1_struct_0(sK0),sK1))) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_2),
% 0.22/0.53    inference(resolution,[],[f51,f37])).
% 0.22/0.53  fof(f37,plain,(
% 0.22/0.53    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl2_2),
% 0.22/0.53    inference(avatar_component_clause,[],[f33])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | k3_subset_1(u1_struct_0(X0),X1) = k2_pre_topc(X0,k1_tops_1(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.53    inference(resolution,[],[f25,f26])).
% 0.22/0.53  fof(f92,plain,(
% 0.22/0.53    spl2_8),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f91])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    $false | spl2_8),
% 0.22/0.53    inference(resolution,[],[f90,f19])).
% 0.22/0.53  fof(f90,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 0.22/0.53    inference(resolution,[],[f81,f26])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_8),
% 0.22/0.53    inference(avatar_component_clause,[],[f80])).
% 0.22/0.53  fof(f89,plain,(
% 0.22/0.53    spl2_7),
% 0.22/0.53    inference(avatar_contradiction_clause,[],[f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    $false | spl2_7),
% 0.22/0.53    inference(resolution,[],[f78,f20])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | spl2_7),
% 0.22/0.53    inference(avatar_component_clause,[],[f77])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    spl2_1 | spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f17,f33,f30])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | v6_tops_1(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ~spl2_1 | ~spl2_2),
% 0.22/0.53    inference(avatar_split_clause,[],[f18,f33,f30])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ~v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v6_tops_1(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f9])).
% 0.22/0.53  % SZS output end Proof for theBenchmark
% 0.22/0.53  % (5245)------------------------------
% 0.22/0.53  % (5245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (5245)Termination reason: Refutation
% 0.22/0.53  
% 0.22/0.53  % (5245)Memory used [KB]: 10746
% 0.22/0.53  % (5245)Time elapsed: 0.100 s
% 0.22/0.53  % (5245)------------------------------
% 0.22/0.53  % (5245)------------------------------
% 0.22/0.53  % (5255)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.53  % (5232)Success in time 0.167 s
%------------------------------------------------------------------------------
