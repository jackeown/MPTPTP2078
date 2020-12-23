%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1110+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:16 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 136 expanded)
%              Number of leaves         :   19 (  56 expanded)
%              Depth                    :    7
%              Number of atoms          :  197 ( 332 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f150,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f40,f45,f49,f59,f63,f68,f73,f84,f88,f93,f99,f145,f149])).

fof(f149,plain,
    ( spl6_8
    | ~ spl6_18 ),
    inference(avatar_contradiction_clause,[],[f148])).

fof(f148,plain,
    ( $false
    | spl6_8
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f147,f83])).

fof(f83,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | spl6_8 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl6_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_18 ),
    inference(resolution,[],[f144,f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f144,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f143,plain,
    ( spl6_18
  <=> r1_tarski(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f145,plain,
    ( spl6_18
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f141,f97,f91,f143])).

fof(f91,plain,
    ( spl6_10
  <=> r1_tarski(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f97,plain,
    ( spl6_11
  <=> r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f141,plain,
    ( r1_tarski(sK2,k2_struct_0(sK0))
    | ~ spl6_10
    | ~ spl6_11 ),
    inference(resolution,[],[f94,f98])).

fof(f98,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f97])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k2_struct_0(sK1),X0)
        | r1_tarski(sK2,X0) )
    | ~ spl6_10 ),
    inference(resolution,[],[f92,f25])).

fof(f25,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X2)
      | r1_tarski(X0,X2) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f92,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1))
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f99,plain,
    ( spl6_11
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f55,f47,f38,f97])).

fof(f38,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f47,plain,
    ( spl6_3
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f55,plain,
    ( r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f53,f54])).

fof(f54,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f52,f39])).

fof(f39,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f38])).

fof(f52,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK1)
    | ~ spl6_3 ),
    inference(resolution,[],[f48,f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f48,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f47])).

fof(f53,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(subsumption_resolution,[],[f51,f39])).

fof(f51,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(k2_struct_0(sK1),k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(resolution,[],[f48,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X1)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( r2_hidden(X2,u1_pre_topc(X1))
                  <=> ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) )
              & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f93,plain,
    ( spl6_10
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f89,f86,f71,f91])).

fof(f71,plain,
    ( spl6_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f86,plain,
    ( spl6_9
  <=> r1_tarski(sK2,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f89,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1))
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f87,f80])).

fof(f80,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl6_7 ),
    inference(resolution,[],[f72,f22])).

fof(f22,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f72,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f87,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1))
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f86])).

fof(f88,plain,
    ( spl6_9
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f77,f61,f86])).

fof(f61,plain,
    ( spl6_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f77,plain,
    ( r1_tarski(sK2,u1_struct_0(sK1))
    | ~ spl6_5 ),
    inference(resolution,[],[f62,f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f62,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f84,plain,
    ( ~ spl6_8
    | ~ spl6_2
    | spl6_6 ),
    inference(avatar_split_clause,[],[f69,f66,f43,f82])).

fof(f43,plain,
    ( spl6_2
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f66,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f69,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ spl6_2
    | spl6_6 ),
    inference(forward_demodulation,[],[f67,f50])).

fof(f50,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl6_2 ),
    inference(resolution,[],[f44,f22])).

fof(f44,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f43])).

fof(f67,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl6_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f73,plain,
    ( spl6_7
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f64,f57,f71])).

fof(f57,plain,
    ( spl6_4
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f64,plain,
    ( l1_struct_0(sK1)
    | ~ spl6_4 ),
    inference(resolution,[],[f58,f24])).

fof(f24,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f58,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f57])).

fof(f68,plain,(
    ~ spl6_6 ),
    inference(avatar_split_clause,[],[f17,f66])).

fof(f17,plain,(
    ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
               => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f63,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f16,f61])).

fof(f16,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f9])).

fof(f59,plain,
    ( spl6_4
    | ~ spl6_1
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f54,f47,f38,f57])).

fof(f49,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f18,f47])).

fof(f18,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f45,plain,
    ( spl6_2
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f41,f38,f43])).

fof(f41,plain,
    ( l1_struct_0(sK0)
    | ~ spl6_1 ),
    inference(resolution,[],[f39,f24])).

fof(f40,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f19,f38])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

%------------------------------------------------------------------------------
