%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:32 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 260 expanded)
%              Number of leaves         :   21 ( 102 expanded)
%              Depth                    :   12
%              Number of atoms          :  431 ( 927 expanded)
%              Number of equality atoms :   41 ( 104 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f309,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f47,f51,f55,f78,f85,f93,f101,f113,f123,f132,f136,f141,f145,f305,f308])).

fof(f308,plain,
    ( spl4_11
    | ~ spl4_26 ),
    inference(avatar_contradiction_clause,[],[f307])).

fof(f307,plain,
    ( $false
    | spl4_11
    | ~ spl4_26 ),
    inference(subsumption_resolution,[],[f306,f135])).

fof(f135,plain,
    ( k1_xboole_0 != sK2
    | spl4_11 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl4_11
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f306,plain,
    ( k1_xboole_0 = sK2
    | ~ spl4_26 ),
    inference(resolution,[],[f304,f34])).

fof(f34,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f304,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_26 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl4_26
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).

fof(f305,plain,
    ( spl4_26
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f299,f143,f130,f95,f83,f53,f49,f45,f303])).

fof(f45,plain,
    ( spl4_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f49,plain,
    ( spl4_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f53,plain,
    ( spl4_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f83,plain,
    ( spl4_6
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f95,plain,
    ( spl4_8
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f130,plain,
    ( spl4_10
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f143,plain,
    ( spl4_12
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f299,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f298,f260])).

fof(f260,plain,
    ( sK2 = k1_tops_1(sK0,sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_10
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f259,f131])).

fof(f131,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f259,plain,
    ( ~ v3_pre_topc(sK2,sK0)
    | sK2 = k1_tops_1(sK0,sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f246,f50])).

fof(f50,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f49])).

fof(f246,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_pre_topc(sK2,sK0)
    | sK2 = k1_tops_1(sK0,sK2)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(resolution,[],[f65,f144])).

fof(f144,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f143])).

fof(f65,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v3_pre_topc(X1,X0)
        | k1_tops_1(X0,X1) = X1 )
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f64,f46])).

fof(f46,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f45])).

fof(f64,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | k1_tops_1(X0,X1) = X1 )
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f56,f50])).

fof(f56,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ v3_pre_topc(X1,X0)
        | k1_tops_1(X0,X1) = X1 )
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f33])).

fof(f33,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | k1_tops_1(X1,X3) = X3 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( v3_pre_topc(X2,X0)
                      | k1_tops_1(X0,X2) != X2 )
                    & ( k1_tops_1(X1,X3) = X3
                      | ~ v3_pre_topc(X3,X1) ) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( ( k1_tops_1(X0,X2) = X2
                     => v3_pre_topc(X2,X0) )
                    & ( v3_pre_topc(X3,X1)
                     => k1_tops_1(X1,X3) = X3 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).

fof(f54,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f53])).

fof(f298,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_xboole_0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_8
    | ~ spl4_12 ),
    inference(forward_demodulation,[],[f297,f124])).

fof(f124,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f297,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_6
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f285,f84])).

fof(f84,plain,
    ( r1_tarski(sK2,sK1)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f83])).

fof(f285,plain,
    ( ~ r1_tarski(sK2,sK1)
    | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_12 ),
    inference(resolution,[],[f157,f54])).

fof(f157,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X0)
        | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) )
    | ~ spl4_2
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f149,f50])).

fof(f149,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK2,X0)
        | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0)) )
    | ~ spl4_12 ),
    inference(resolution,[],[f144,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X1,X2)
      | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f145,plain,
    ( spl4_12
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f126,f95,f53,f49,f143])).

fof(f126,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f24,f125])).

fof(f125,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f66,f124])).

fof(f66,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f57,f50])).

fof(f57,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).

fof(f24,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_1(X1,X0)
          <~> ! [X2] :
                ( k1_xboole_0 = X2
                | ~ v3_pre_topc(X2,X0)
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v2_tops_1(X1,X0)
            <=> ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v3_pre_topc(X2,X0)
                      & r1_tarski(X2,X1) )
                   => k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v3_pre_topc(X2,X0)
                    & r1_tarski(X2,X1) )
                 => k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).

fof(f141,plain,
    ( spl4_5
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f125,f95,f53,f49,f80])).

fof(f80,plain,
    ( spl4_5
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f136,plain,
    ( ~ spl4_11
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f128,f95,f53,f49,f134])).

fof(f128,plain,
    ( k1_xboole_0 != sK2
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f27,f125])).

fof(f27,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f132,plain,
    ( spl4_10
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f127,f95,f53,f49,f130])).

fof(f127,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | ~ spl4_8 ),
    inference(subsumption_resolution,[],[f26,f125])).

fof(f26,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f123,plain,
    ( ~ spl4_5
    | ~ spl4_2
    | ~ spl4_3
    | spl4_8 ),
    inference(avatar_split_clause,[],[f121,f95,f53,f49,f80])).

fof(f121,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3
    | spl4_8 ),
    inference(subsumption_resolution,[],[f67,f96])).

fof(f96,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f95])).

fof(f67,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f58,f50])).

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ v2_tops_1(sK1,sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f113,plain,
    ( ~ spl4_4
    | spl4_5
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9 ),
    inference(avatar_contradiction_clause,[],[f112])).

fof(f112,plain,
    ( $false
    | ~ spl4_4
    | spl4_5
    | ~ spl4_7
    | spl4_8
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f111,f96])).

fof(f111,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl4_4
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f110,f77])).

fof(f77,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl4_4
  <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f110,plain,
    ( ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | spl4_5
    | ~ spl4_7
    | ~ spl4_9 ),
    inference(subsumption_resolution,[],[f102,f92])).

fof(f92,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f91,plain,
    ( spl4_7
  <=> r1_tarski(k1_tops_1(sK0,sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f102,plain,
    ( ~ r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | k1_xboole_0 = k1_tops_1(sK0,sK1)
    | spl4_5
    | ~ spl4_9 ),
    inference(resolution,[],[f100,f87])).

fof(f87,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(X2,sK1)
        | ~ v3_pre_topc(X2,sK0)
        | k1_xboole_0 = X2 )
    | spl4_5 ),
    inference(subsumption_resolution,[],[f28,f81])).

fof(f81,plain,
    ( ~ v2_tops_1(sK1,sK0)
    | spl4_5 ),
    inference(avatar_component_clause,[],[f80])).

fof(f28,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f100,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_9
  <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f101,plain,
    ( spl4_9
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f72,f53,f49,f99])).

fof(f72,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f62,f50])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f93,plain,
    ( spl4_7
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f71,f53,f49,f91])).

fof(f71,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f61,f50])).

fof(f61,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(k1_tops_1(sK0,sK1),sK1)
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(k1_tops_1(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f85,plain,
    ( ~ spl4_5
    | spl4_6 ),
    inference(avatar_split_clause,[],[f25,f83,f80])).

fof(f25,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f78,plain,
    ( spl4_4
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f69,f53,f49,f45,f76])).

fof(f69,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f68,f46])).

fof(f68,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_2
    | ~ spl4_3 ),
    inference(subsumption_resolution,[],[f59,f50])).

fof(f59,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k1_tops_1(sK0,sK1),sK0)
    | ~ spl4_3 ),
    inference(resolution,[],[f54,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f55,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f29,f53])).

fof(f29,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f51,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f31,f49])).

fof(f31,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f47,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f30,f45])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n003.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:01:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (20183)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (20183)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (20192)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f47,f51,f55,f78,f85,f93,f101,f113,f123,f132,f136,f141,f145,f305,f308])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    spl4_11 | ~spl4_26),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f307])).
% 0.21/0.48  fof(f307,plain,(
% 0.21/0.48    $false | (spl4_11 | ~spl4_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f306,f135])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | spl4_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl4_11 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl4_26),
% 0.21/0.48    inference(resolution,[],[f304,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.21/0.48  fof(f304,plain,(
% 0.21/0.48    r1_tarski(sK2,k1_xboole_0) | ~spl4_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f303])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    spl4_26 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_26])])).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    spl4_26 | ~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f299,f143,f130,f95,f83,f53,f49,f45,f303])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    spl4_1 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    spl4_2 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl4_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl4_6 <=> r1_tarski(sK2,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl4_8 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    spl4_10 <=> v3_pre_topc(sK2,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl4_12 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    r1_tarski(sK2,k1_xboole_0) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_10 | ~spl4_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f298,f260])).
% 0.21/0.48  fof(f260,plain,(
% 0.21/0.48    sK2 = k1_tops_1(sK0,sK2) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_10 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f259,f131])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    v3_pre_topc(sK2,sK0) | ~spl4_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f130])).
% 0.21/0.48  fof(f259,plain,(
% 0.21/0.48    ~v3_pre_topc(sK2,sK0) | sK2 = k1_tops_1(sK0,sK2) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f246,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl4_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f49])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v3_pre_topc(sK2,sK0) | sK2 = k1_tops_1(sK0,sK2) | (~spl4_1 | ~spl4_2 | ~spl4_3 | ~spl4_12)),
% 0.21/0.48    inference(resolution,[],[f65,f144])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f143])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | k1_tops_1(X0,X1) = X1) ) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f64,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    v2_pre_topc(sK0) | ~spl4_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f45])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k1_tops_1(X0,X1) = X1) ) | (~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f56,f50])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~l1_pre_topc(X0) | ~v2_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | k1_tops_1(X0,X1) = X1) ) | ~spl4_3),
% 0.21/0.48    inference(resolution,[],[f54,f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | k1_tops_1(X1,X3) = X3) )),
% 0.21/0.48    inference(cnf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f13])).
% 0.21/0.48  fof(f13,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v3_pre_topc(X2,X0) | k1_tops_1(X0,X2) != X2) & (k1_tops_1(X1,X3) = X3 | ~v3_pre_topc(X3,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X1)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => ((k1_tops_1(X0,X2) = X2 => v3_pre_topc(X2,X0)) & (v3_pre_topc(X3,X1) => k1_tops_1(X1,X3) = X3))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_1)).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f53])).
% 0.21/0.48  fof(f298,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK2),k1_xboole_0) | (~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_8 | ~spl4_12)),
% 0.21/0.48    inference(forward_demodulation,[],[f297,f124])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_6 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f285,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    r1_tarski(sK2,sK1) | ~spl4_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    ~r1_tarski(sK2,sK1) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK1)) | (~spl4_2 | ~spl4_3 | ~spl4_12)),
% 0.21/0.48    inference(resolution,[],[f157,f54])).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))) ) | (~spl4_2 | ~spl4_12)),
% 0.21/0.48    inference(subsumption_resolution,[],[f149,f50])).
% 0.21/0.48  fof(f149,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK2,X0) | r1_tarski(k1_tops_1(sK0,sK2),k1_tops_1(sK0,X0))) ) | ~spl4_12),
% 0.21/0.48    inference(resolution,[],[f144,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X1,X2) | r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.21/0.48  fof(f145,plain,(
% 0.21/0.48    spl4_12 | ~spl4_2 | ~spl4_3 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f126,f95,f53,f49,f143])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_3 | ~spl4_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f24,f125])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    v2_tops_1(sK1,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f66,f124])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | (~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f57,f50])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~spl4_3),
% 0.21/0.48    inference(resolution,[],[f54,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tops_1)).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f11])).
% 0.21/0.48  fof(f11,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f9])).
% 0.21/0.48  fof(f9,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tops_1)).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl4_5 | ~spl4_2 | ~spl4_3 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f125,f95,f53,f49,f80])).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    spl4_5 <=> v2_tops_1(sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.48  fof(f136,plain,(
% 0.21/0.48    ~spl4_11 | ~spl4_2 | ~spl4_3 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f128,f95,f53,f49,f134])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | (~spl4_2 | ~spl4_3 | ~spl4_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f27,f125])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl4_10 | ~spl4_2 | ~spl4_3 | ~spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f127,f95,f53,f49,f130])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    v3_pre_topc(sK2,sK0) | (~spl4_2 | ~spl4_3 | ~spl4_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f26,f125])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~spl4_5 | ~spl4_2 | ~spl4_3 | spl4_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f121,f95,f53,f49,f80])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~v2_tops_1(sK1,sK0) | (~spl4_2 | ~spl4_3 | spl4_8)),
% 0.21/0.48    inference(subsumption_resolution,[],[f67,f96])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl4_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0) | (~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f58,f50])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | ~v2_tops_1(sK1,sK0) | ~spl4_3),
% 0.21/0.48    inference(resolution,[],[f54,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f113,plain,(
% 0.21/0.48    ~spl4_4 | spl4_5 | ~spl4_7 | spl4_8 | ~spl4_9),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f112])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    $false | (~spl4_4 | spl4_5 | ~spl4_7 | spl4_8 | ~spl4_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f111,f96])).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    k1_xboole_0 = k1_tops_1(sK0,sK1) | (~spl4_4 | spl4_5 | ~spl4_7 | ~spl4_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f110,f77])).
% 0.21/0.48  fof(f77,plain,(
% 0.21/0.48    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl4_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f76])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl4_4 <=> v3_pre_topc(k1_tops_1(sK0,sK1),sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.48  fof(f110,plain,(
% 0.21/0.48    ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (spl4_5 | ~spl4_7 | ~spl4_9)),
% 0.21/0.48    inference(subsumption_resolution,[],[f102,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl4_7 <=> r1_tarski(k1_tops_1(sK0,sK1),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    ~r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | k1_xboole_0 = k1_tops_1(sK0,sK1) | (spl4_5 | ~spl4_9)),
% 0.21/0.48    inference(resolution,[],[f100,f87])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2) ) | spl4_5),
% 0.21/0.48    inference(subsumption_resolution,[],[f28,f81])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    ~v2_tops_1(sK1,sK0) | spl4_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f80])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl4_9 <=> m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl4_9 | ~spl4_2 | ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f72,f53,f49,f99])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f62,f50])).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | m1_subset_1(k1_tops_1(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_3),
% 0.21/0.48    inference(resolution,[],[f54,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl4_7 | ~spl4_2 | ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f71,f53,f49,f91])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    r1_tarski(k1_tops_1(sK0,sK1),sK1) | (~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f61,f50])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | r1_tarski(k1_tops_1(sK0,sK1),sK1) | ~spl4_3),
% 0.21/0.48    inference(resolution,[],[f54,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(k1_tops_1(X0,X1),X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~spl4_5 | spl4_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f25,f83,f80])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl4_4 | ~spl4_1 | ~spl4_2 | ~spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f69,f53,f49,f45,f76])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl4_1 | ~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f68,f46])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | (~spl4_2 | ~spl4_3)),
% 0.21/0.48    inference(subsumption_resolution,[],[f59,f50])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v3_pre_topc(k1_tops_1(sK0,sK1),sK0) | ~spl4_3),
% 0.21/0.48    inference(resolution,[],[f54,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl4_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f53])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    spl4_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f49])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    spl4_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f45])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f12])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (20183)------------------------------
% 0.21/0.48  % (20183)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (20183)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (20183)Memory used [KB]: 6268
% 0.21/0.48  % (20183)Time elapsed: 0.068 s
% 0.21/0.48  % (20183)------------------------------
% 0.21/0.48  % (20183)------------------------------
% 0.21/0.49  % (20200)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (20176)Success in time 0.124 s
%------------------------------------------------------------------------------
