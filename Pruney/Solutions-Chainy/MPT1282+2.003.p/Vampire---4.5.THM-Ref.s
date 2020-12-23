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
% DateTime   : Thu Dec  3 13:13:01 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 176 expanded)
%              Number of leaves         :   13 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  194 ( 603 expanded)
%              Number of equality atoms :   48 ( 188 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f127,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f39,f82,f93,f99,f101,f120,f126])).

fof(f126,plain,
    ( ~ spl2_11
    | ~ spl2_10
    | spl2_2
    | ~ spl2_8 ),
    inference(avatar_split_clause,[],[f124,f77,f37,f88,f91])).

fof(f91,plain,
    ( spl2_11
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f88,plain,
    ( spl2_10
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f37,plain,
    ( spl2_2
  <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f77,plain,
    ( spl2_8
  <=> v5_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f124,plain,
    ( k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(forward_demodulation,[],[f123,f70])).

fof(f70,plain,(
    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) ),
    inference(global_subsumption,[],[f23,f22,f67])).

fof(f67,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | ~ v6_tops_1(sK1,sK0) ),
    inference(resolution,[],[f29,f21])).

fof(f21,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
            | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1)) )
          & v6_tops_1(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v6_tops_1(X1,X0)
             => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
                & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
           => ( k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1)
              & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tops_1)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1
      | ~ v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).

fof(f22,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f23,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f10])).

fof(f123,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl2_8 ),
    inference(resolution,[],[f85,f78])).

fof(f78,plain,
    ( v5_tops_1(k2_pre_topc(sK0,sK1),sK0)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f77])).

fof(f85,plain,(
    ! [X0,X1] :
      ( ~ v5_tops_1(k2_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,k2_pre_topc(X0,X1)) = k2_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v5_tops_1(k2_pre_topc(X0,X1),X0)
      | k2_tops_1(X0,k2_pre_topc(X0,X1)) = k2_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f25,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v5_tops_1(X1,X0)
      | k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))
          | ~ v5_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
           => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tops_1)).

fof(f120,plain,(
    spl2_1 ),
    inference(avatar_contradiction_clause,[],[f119])).

fof(f119,plain,
    ( $false
    | spl2_1 ),
    inference(trivial_inequality_removal,[],[f118])).

fof(f118,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1)
    | spl2_1 ),
    inference(superposition,[],[f35,f108])).

fof(f108,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(backward_demodulation,[],[f97,f106])).

fof(f106,plain,(
    sK1 = k1_tops_1(sK0,sK1) ),
    inference(global_subsumption,[],[f23,f105])).

fof(f105,plain,
    ( sK1 = k1_tops_1(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(forward_demodulation,[],[f102,f70])).

fof(f102,plain,
    ( k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f21])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | k1_tops_1(X0,k2_pre_topc(X0,X1)) = k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f31,f30])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).

fof(f97,plain,(
    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(global_subsumption,[],[f23,f94])).

fof(f94,plain,
    ( ~ l1_pre_topc(sK0)
    | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1)) ),
    inference(resolution,[],[f24,f21])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).

fof(f35,plain,
    ( k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)
    | spl2_1 ),
    inference(avatar_component_clause,[],[f34])).

fof(f34,plain,
    ( spl2_1
  <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f101,plain,(
    spl2_11 ),
    inference(avatar_contradiction_clause,[],[f100])).

fof(f100,plain,
    ( $false
    | spl2_11 ),
    inference(resolution,[],[f92,f21])).

fof(f92,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_11 ),
    inference(avatar_component_clause,[],[f91])).

fof(f99,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f98])).

fof(f98,plain,
    ( $false
    | spl2_10 ),
    inference(resolution,[],[f89,f23])).

fof(f89,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_10 ),
    inference(avatar_component_clause,[],[f88])).

fof(f93,plain,
    ( ~ spl2_10
    | ~ spl2_11
    | spl2_9 ),
    inference(avatar_split_clause,[],[f86,f80,f91,f88])).

fof(f80,plain,
    ( spl2_9
  <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f86,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | spl2_9 ),
    inference(resolution,[],[f81,f30])).

fof(f81,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | spl2_9 ),
    inference(avatar_component_clause,[],[f80])).

fof(f82,plain,
    ( spl2_8
    | ~ spl2_9 ),
    inference(avatar_split_clause,[],[f75,f80,f77])).

fof(f75,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v5_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(global_subsumption,[],[f23,f73])).

fof(f73,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v5_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f72])).

fof(f72,plain,
    ( k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v5_tops_1(k2_pre_topc(sK0,sK1),sK0) ),
    inference(superposition,[],[f26,f70])).

fof(f26,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v5_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v5_tops_1(X1,X0)
          <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).

fof(f39,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f32,f37,f34])).

fof(f32,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(inner_rewriting,[],[f20])).

fof(f20,plain,
    ( k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k2_pre_topc(sK0,sK1))
    | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) ),
    inference(cnf_transformation,[],[f10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 16:55:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.22/0.46  % (8189)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.46  % (8181)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.47  % (8181)Refutation found. Thanks to Tanya!
% 0.22/0.47  % SZS status Theorem for theBenchmark
% 0.22/0.47  % SZS output start Proof for theBenchmark
% 0.22/0.47  fof(f127,plain,(
% 0.22/0.47    $false),
% 0.22/0.47    inference(avatar_sat_refutation,[],[f39,f82,f93,f99,f101,f120,f126])).
% 0.22/0.47  fof(f126,plain,(
% 0.22/0.47    ~spl2_11 | ~spl2_10 | spl2_2 | ~spl2_8),
% 0.22/0.47    inference(avatar_split_clause,[],[f124,f77,f37,f88,f91])).
% 0.22/0.47  fof(f91,plain,(
% 0.22/0.47    spl2_11 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.22/0.47  fof(f88,plain,(
% 0.22/0.47    spl2_10 <=> l1_pre_topc(sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.22/0.47  fof(f37,plain,(
% 0.22/0.47    spl2_2 <=> k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.22/0.47  fof(f77,plain,(
% 0.22/0.47    spl2_8 <=> v5_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.22/0.47  fof(f124,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) = k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_8),
% 0.22/0.47    inference(forward_demodulation,[],[f123,f70])).
% 0.22/0.47  fof(f70,plain,(
% 0.22/0.47    sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1))),
% 0.22/0.47    inference(global_subsumption,[],[f23,f22,f67])).
% 0.22/0.47  fof(f67,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | sK1 = k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) | ~v6_tops_1(sK1,sK0)),
% 0.22/0.47    inference(resolution,[],[f29,f21])).
% 0.22/0.47  fof(f21,plain,(
% 0.22/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f10,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : ((k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1))) & v6_tops_1(X1,X0) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f9])).
% 0.22/0.47  fof(f9,plain,(
% 0.22/0.47    ? [X0] : (? [X1] : (((k2_tops_1(X0,k2_pre_topc(X0,X1)) != k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) | k2_tops_1(X0,X1) != k2_tops_1(X0,k2_pre_topc(X0,X1))) & v6_tops_1(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f8])).
% 0.22/0.47  fof(f8,negated_conjecture,(
% 0.22/0.47    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) => (k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 0.22/0.47    inference(negated_conjecture,[],[f7])).
% 0.22/0.47  fof(f7,conjecture,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) => (k2_tops_1(X0,k2_pre_topc(X0,X1)) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),X1) & k2_tops_1(X0,X1) = k2_tops_1(X0,k2_pre_topc(X0,X1))))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tops_1)).
% 0.22/0.47  fof(f29,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1 | ~v6_tops_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f15])).
% 0.22/0.47  fof(f15,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f3])).
% 0.22/0.47  fof(f3,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> k1_tops_1(X0,k2_pre_topc(X0,X1)) = X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_tops_1)).
% 0.22/0.47  fof(f22,plain,(
% 0.22/0.47    v6_tops_1(sK1,sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f23,plain,(
% 0.22/0.47    l1_pre_topc(sK0)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  fof(f123,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k2_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl2_8),
% 0.22/0.47    inference(resolution,[],[f85,f78])).
% 0.22/0.47  fof(f78,plain,(
% 0.22/0.47    v5_tops_1(k2_pre_topc(sK0,sK1),sK0) | ~spl2_8),
% 0.22/0.47    inference(avatar_component_clause,[],[f77])).
% 0.22/0.47  fof(f85,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~v5_tops_1(k2_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0) | k2_tops_1(X0,k2_pre_topc(X0,X1)) = k2_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f84])).
% 0.22/0.47  fof(f84,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v5_tops_1(k2_pre_topc(X0,X1),X0) | k2_tops_1(X0,k2_pre_topc(X0,X1)) = k2_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(resolution,[],[f25,f30])).
% 0.22/0.47  fof(f30,plain,(
% 0.22/0.47    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f17])).
% 0.22/0.47  fof(f17,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f16])).
% 0.22/0.47  fof(f16,plain,(
% 0.22/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f1])).
% 0.22/0.47  fof(f1,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.22/0.47  fof(f25,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v5_tops_1(X1,X0) | k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f13])).
% 0.22/0.47  fof(f13,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f12])).
% 0.22/0.47  fof(f12,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)) | ~v5_tops_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f6])).
% 0.22/0.47  fof(f6,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) => k2_tops_1(X0,X1) = k2_tops_1(X0,k1_tops_1(X0,X1)))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_tops_1)).
% 0.22/0.47  fof(f120,plain,(
% 0.22/0.47    spl2_1),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f119])).
% 0.22/0.47  fof(f119,plain,(
% 0.22/0.47    $false | spl2_1),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f118])).
% 0.22/0.47  fof(f118,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,sK1) | spl2_1),
% 0.22/0.47    inference(superposition,[],[f35,f108])).
% 0.22/0.47  fof(f108,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.22/0.47    inference(backward_demodulation,[],[f97,f106])).
% 0.22/0.47  fof(f106,plain,(
% 0.22/0.47    sK1 = k1_tops_1(sK0,sK1)),
% 0.22/0.47    inference(global_subsumption,[],[f23,f105])).
% 0.22/0.47  fof(f105,plain,(
% 0.22/0.47    sK1 = k1_tops_1(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.22/0.47    inference(forward_demodulation,[],[f102,f70])).
% 0.22/0.47  fof(f102,plain,(
% 0.22/0.47    k1_tops_1(sK0,k2_pre_topc(sK0,sK1)) = k1_tops_1(sK0,k1_tops_1(sK0,k2_pre_topc(sK0,sK1))) | ~l1_pre_topc(sK0)),
% 0.22/0.47    inference(resolution,[],[f42,f21])).
% 0.22/0.47  fof(f42,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(duplicate_literal_removal,[],[f41])).
% 0.22/0.47  fof(f41,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~l1_pre_topc(X0) | k1_tops_1(X0,k2_pre_topc(X0,X1)) = k1_tops_1(X0,k1_tops_1(X0,k2_pre_topc(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.22/0.47    inference(resolution,[],[f31,f30])).
% 0.22/0.47  fof(f31,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f19])).
% 0.22/0.47  fof(f19,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(flattening,[],[f18])).
% 0.22/0.47  fof(f18,plain,(
% 0.22/0.47    ! [X0,X1] : (k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.22/0.47    inference(ennf_transformation,[],[f5])).
% 0.22/0.47  fof(f5,axiom,(
% 0.22/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => k1_tops_1(X0,X1) = k1_tops_1(X0,k1_tops_1(X0,X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',projectivity_k1_tops_1)).
% 0.22/0.47  fof(f97,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.47    inference(global_subsumption,[],[f23,f94])).
% 0.22/0.47  fof(f94,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),k1_tops_1(sK0,sK1))),
% 0.22/0.47    inference(resolution,[],[f24,f21])).
% 0.22/0.47  fof(f24,plain,(
% 0.22/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))) )),
% 0.22/0.47    inference(cnf_transformation,[],[f11])).
% 0.22/0.47  fof(f11,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : (k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f4])).
% 0.22/0.47  fof(f4,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k2_tops_1(X0,X1) = k7_subset_1(u1_struct_0(X0),k2_pre_topc(X0,X1),k1_tops_1(X0,X1))))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l78_tops_1)).
% 0.22/0.47  fof(f35,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1) | spl2_1),
% 0.22/0.47    inference(avatar_component_clause,[],[f34])).
% 0.22/0.47  fof(f34,plain,(
% 0.22/0.47    spl2_1 <=> k2_tops_1(sK0,sK1) = k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.22/0.47  fof(f101,plain,(
% 0.22/0.47    spl2_11),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f100])).
% 0.22/0.47  fof(f100,plain,(
% 0.22/0.47    $false | spl2_11),
% 0.22/0.47    inference(resolution,[],[f92,f21])).
% 0.22/0.47  fof(f92,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | spl2_11),
% 0.22/0.47    inference(avatar_component_clause,[],[f91])).
% 0.22/0.47  fof(f99,plain,(
% 0.22/0.47    spl2_10),
% 0.22/0.47    inference(avatar_contradiction_clause,[],[f98])).
% 0.22/0.47  fof(f98,plain,(
% 0.22/0.47    $false | spl2_10),
% 0.22/0.47    inference(resolution,[],[f89,f23])).
% 0.22/0.47  fof(f89,plain,(
% 0.22/0.47    ~l1_pre_topc(sK0) | spl2_10),
% 0.22/0.47    inference(avatar_component_clause,[],[f88])).
% 0.22/0.47  fof(f93,plain,(
% 0.22/0.47    ~spl2_10 | ~spl2_11 | spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f86,f80,f91,f88])).
% 0.22/0.47  fof(f80,plain,(
% 0.22/0.47    spl2_9 <=> m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.47    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.22/0.47  fof(f86,plain,(
% 0.22/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | spl2_9),
% 0.22/0.47    inference(resolution,[],[f81,f30])).
% 0.22/0.47  fof(f81,plain,(
% 0.22/0.47    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | spl2_9),
% 0.22/0.47    inference(avatar_component_clause,[],[f80])).
% 0.22/0.47  fof(f82,plain,(
% 0.22/0.47    spl2_8 | ~spl2_9),
% 0.22/0.47    inference(avatar_split_clause,[],[f75,f80,f77])).
% 0.22/0.47  fof(f75,plain,(
% 0.22/0.47    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v5_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 0.22/0.47    inference(global_subsumption,[],[f23,f73])).
% 0.22/0.47  fof(f73,plain,(
% 0.22/0.47    ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v5_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 0.22/0.47    inference(trivial_inequality_removal,[],[f72])).
% 0.22/0.47  fof(f72,plain,(
% 0.22/0.47    k2_pre_topc(sK0,sK1) != k2_pre_topc(sK0,sK1) | ~m1_subset_1(k2_pre_topc(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v5_tops_1(k2_pre_topc(sK0,sK1),sK0)),
% 0.22/0.47    inference(superposition,[],[f26,f70])).
% 0.22/0.47  fof(f26,plain,(
% 0.22/0.47    ( ! [X0,X1] : (k2_pre_topc(X0,k1_tops_1(X0,X1)) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v5_tops_1(X1,X0)) )),
% 0.22/0.47    inference(cnf_transformation,[],[f14])).
% 0.22/0.47  fof(f14,plain,(
% 0.22/0.47    ! [X0] : (! [X1] : ((v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.47    inference(ennf_transformation,[],[f2])).
% 0.22/0.47  fof(f2,axiom,(
% 0.22/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v5_tops_1(X1,X0) <=> k2_pre_topc(X0,k1_tops_1(X0,X1)) = X1)))),
% 0.22/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tops_1)).
% 0.22/0.47  fof(f39,plain,(
% 0.22/0.47    ~spl2_1 | ~spl2_2),
% 0.22/0.47    inference(avatar_split_clause,[],[f32,f37,f34])).
% 0.22/0.47  fof(f32,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) | k2_tops_1(sK0,sK1) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.22/0.47    inference(inner_rewriting,[],[f20])).
% 0.22/0.47  fof(f20,plain,(
% 0.22/0.47    k2_tops_1(sK0,sK1) != k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) | k2_tops_1(sK0,k2_pre_topc(sK0,sK1)) != k7_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,sK1),sK1)),
% 0.22/0.47    inference(cnf_transformation,[],[f10])).
% 0.22/0.47  % SZS output end Proof for theBenchmark
% 0.22/0.47  % (8181)------------------------------
% 0.22/0.47  % (8181)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.47  % (8181)Termination reason: Refutation
% 0.22/0.47  
% 0.22/0.47  % (8181)Memory used [KB]: 10618
% 0.22/0.47  % (8181)Time elapsed: 0.061 s
% 0.22/0.47  % (8181)------------------------------
% 0.22/0.47  % (8181)------------------------------
% 0.22/0.47  % (8168)Success in time 0.111 s
%------------------------------------------------------------------------------
