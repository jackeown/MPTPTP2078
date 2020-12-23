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
% DateTime   : Thu Dec  3 13:14:52 EST 2020

% Result     : Theorem 0.23s
% Output     : Refutation 0.23s
% Verified   : 
% Statistics : Number of formulae       :  135 (1427 expanded)
%              Number of leaves         :   25 ( 513 expanded)
%              Depth                    :   21
%              Number of atoms          :  625 (10923 expanded)
%              Number of equality atoms :   70 (1401 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f629,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f77,f187,f277,f440,f457,f549,f580,f591,f612,f624])).

fof(f624,plain,
    ( spl8_2
    | ~ spl8_49 ),
    inference(avatar_contradiction_clause,[],[f623])).

fof(f623,plain,
    ( $false
    | spl8_2
    | ~ spl8_49 ),
    inference(subsumption_resolution,[],[f584,f592])).

fof(f592,plain,
    ( ~ v2_compts_1(sK2,sK1)
    | spl8_2 ),
    inference(forward_demodulation,[],[f75,f44])).

fof(f44,plain,(
    sK2 = sK3 ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,
    ( ( ~ v2_compts_1(sK3,sK1)
      | ~ v2_compts_1(sK2,sK0) )
    & ( v2_compts_1(sK3,sK1)
      | v2_compts_1(sK2,sK0) )
    & sK2 = sK3
    & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_pre_topc(sK1,sK0)
    & l1_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27,f26,f25,f24])).

fof(f24,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ~ v2_compts_1(X3,X1)
                      | ~ v2_compts_1(X2,X0) )
                    & ( v2_compts_1(X3,X1)
                      | v2_compts_1(X2,X0) )
                    & X2 = X3
                    & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_pre_topc(X1,X0) )
        & l1_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,sK0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,sK0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_pre_topc(X1,sK0) )
      & l1_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ~ v2_compts_1(X3,X1)
                  | ~ v2_compts_1(X2,sK0) )
                & ( v2_compts_1(X3,X1)
                  | v2_compts_1(X2,sK0) )
                & X2 = X3
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_pre_topc(X1,sK0) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ~ v2_compts_1(X3,sK1)
                | ~ v2_compts_1(X2,sK0) )
              & ( v2_compts_1(X3,sK1)
                | v2_compts_1(X2,sK0) )
              & X2 = X3
              & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_pre_topc(sK1,sK0) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ~ v2_compts_1(X3,sK1)
              | ~ v2_compts_1(X2,sK0) )
            & ( v2_compts_1(X3,sK1)
              | v2_compts_1(X2,sK0) )
            & X2 = X3
            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X3] :
          ( ( ~ v2_compts_1(X3,sK1)
            | ~ v2_compts_1(sK2,sK0) )
          & ( v2_compts_1(X3,sK1)
            | v2_compts_1(sK2,sK0) )
          & sK2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X3] :
        ( ( ~ v2_compts_1(X3,sK1)
          | ~ v2_compts_1(sK2,sK0) )
        & ( v2_compts_1(X3,sK1)
          | v2_compts_1(sK2,sK0) )
        & sK2 = X3
        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1))) )
   => ( ( ~ v2_compts_1(sK3,sK1)
        | ~ v2_compts_1(sK2,sK0) )
      & ( v2_compts_1(sK3,sK1)
        | v2_compts_1(sK2,sK0) )
      & sK2 = sK3
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ~ v2_compts_1(X3,X1)
                    | ~ v2_compts_1(X2,X0) )
                  & ( v2_compts_1(X3,X1)
                    | v2_compts_1(X2,X0) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( v2_compts_1(X2,X0)
                  <~> v2_compts_1(X3,X1) )
                  & X2 = X3
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_pre_topc(X1,X0) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_pre_topc(X1,X0)
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                   => ( X2 = X3
                     => ( v2_compts_1(X2,X0)
                      <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                 => ( X2 = X3
                   => ( v2_compts_1(X2,X0)
                    <=> v2_compts_1(X3,X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).

fof(f75,plain,
    ( ~ v2_compts_1(sK3,sK1)
    | spl8_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f73,plain,
    ( spl8_2
  <=> v2_compts_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f584,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ spl8_49 ),
    inference(avatar_component_clause,[],[f583])).

fof(f583,plain,
    ( spl8_49
  <=> v2_compts_1(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).

fof(f612,plain,
    ( ~ spl8_1
    | ~ spl8_50 ),
    inference(avatar_contradiction_clause,[],[f611])).

fof(f611,plain,
    ( $false
    | ~ spl8_1
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f610,f70])).

fof(f70,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f69,plain,
    ( spl8_1
  <=> v2_compts_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f610,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f609,f41])).

fof(f41,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f609,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | ~ v2_compts_1(sK2,sK0)
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f608,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f608,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_compts_1(sK2,sK0)
    | ~ spl8_50 ),
    inference(subsumption_resolution,[],[f602,f222])).

fof(f222,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(superposition,[],[f42,f94])).

fof(f94,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f80,f47])).

% (25329)Refutation not found, incomplete strategy% (25329)------------------------------
% (25329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25329)Termination reason: Refutation not found, incomplete strategy

% (25329)Memory used [KB]: 6140
% (25329)Time elapsed: 0.086 s
% (25329)------------------------------
% (25329)------------------------------
fof(f47,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f80,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f48,f40])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f28])).

fof(f602,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ v2_compts_1(sK2,sK0)
    | ~ spl8_50 ),
    inference(superposition,[],[f590,f94])).

fof(f590,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ v2_compts_1(sK2,X1) )
    | ~ spl8_50 ),
    inference(avatar_component_clause,[],[f589])).

fof(f589,plain,
    ( spl8_50
  <=> ! [X1] :
        ( ~ v2_compts_1(sK2,X1)
        | ~ l1_pre_topc(X1)
        | ~ m1_pre_topc(sK1,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f591,plain,
    ( spl8_50
    | spl8_49
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f587,f181,f583,f589])).

fof(f181,plain,
    ( spl8_15
  <=> r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f587,plain,
    ( ! [X1] :
        ( v2_compts_1(sK2,sK1)
        | ~ v2_compts_1(sK2,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl8_15 ),
    inference(subsumption_resolution,[],[f119,f534])).

fof(f534,plain,
    ( r1_tarski(sK2,k2_struct_0(sK1))
    | ~ spl8_15 ),
    inference(superposition,[],[f183,f281])).

fof(f281,plain,(
    sK2 = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(forward_demodulation,[],[f280,f93])).

fof(f93,plain,(
    sK2 = u1_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f91,f82])).

fof(f82,plain,(
    l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f81,f40])).

fof(f81,plain,
    ( l1_pre_topc(sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f59,f41])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f91,plain,
    ( sK2 = u1_struct_0(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f64,f78])).

fof(f78,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(forward_demodulation,[],[f43,f44])).

fof(f43,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(cnf_transformation,[],[f28])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(k1_pre_topc(X0,X1)) = X1
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( u1_struct_0(k1_pre_topc(X0,X1)) = X1
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => u1_struct_0(k1_pre_topc(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).

fof(f280,plain,(
    u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(resolution,[],[f221,f47])).

% (25346)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
fof(f221,plain,(
    l1_struct_0(k1_pre_topc(sK1,sK2)) ),
    inference(resolution,[],[f185,f48])).

fof(f185,plain,(
    l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f174,f82])).

fof(f174,plain,
    ( l1_pre_topc(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f89,f59])).

fof(f89,plain,(
    m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) ),
    inference(subsumption_resolution,[],[f87,f82])).

fof(f87,plain,
    ( m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f65,f78])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_pre_topc(k1_pre_topc(X0,X1),X0) ) ),
    inference(pure_predicate_removal,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => ( m1_pre_topc(k1_pre_topc(X0,X1),X0)
        & v1_pre_topc(k1_pre_topc(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).

fof(f183,plain,
    ( r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1))
    | ~ spl8_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f119,plain,(
    ! [X1] :
      ( v2_compts_1(sK2,sK1)
      | ~ v2_compts_1(sK2,X1)
      | ~ r1_tarski(sK2,k2_struct_0(sK1))
      | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ m1_pre_topc(sK1,X1)
      | ~ l1_pre_topc(X1) ) ),
    inference(resolution,[],[f67,f78])).

fof(f67,plain,(
    ! [X4,X0,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | v2_compts_1(X4,X1)
      | ~ v2_compts_1(X4,X0)
      | ~ r1_tarski(X4,k2_struct_0(X1))
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X4,X2,X0,X1] :
      ( v2_compts_1(X4,X1)
      | X2 != X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ( ~ v2_compts_1(sK7(X1,X2),X1)
                    & sK7(X1,X2) = X2
                    & m1_subset_1(sK7(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).

fof(f38,plain,(
    ! [X2,X1] :
      ( ? [X3] :
          ( ~ v2_compts_1(X3,X1)
          & X2 = X3
          & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ~ v2_compts_1(sK7(X1,X2),X1)
        & sK7(X1,X2) = X2
        & m1_subset_1(sK7(X1,X2),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X4] :
                      ( v2_compts_1(X4,X1)
                      | X2 != X4
                      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( v2_compts_1(X2,X0)
                  | ? [X3] :
                      ( ~ v2_compts_1(X3,X1)
                      & X2 = X3
                      & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
                & ( ! [X3] :
                      ( v2_compts_1(X3,X1)
                      | X2 != X3
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  | ~ v2_compts_1(X2,X0) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_compts_1(X2,X0)
              <=> ! [X3] :
                    ( v2_compts_1(X3,X1)
                    | X2 != X3
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ~ r1_tarski(X2,k2_struct_0(X1))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X2,k2_struct_0(X1))
               => ( v2_compts_1(X2,X0)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( X2 = X3
                       => v2_compts_1(X3,X1) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).

fof(f580,plain,
    ( spl8_1
    | ~ spl8_46 ),
    inference(avatar_contradiction_clause,[],[f579])).

fof(f579,plain,
    ( $false
    | spl8_1
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f578,f71])).

fof(f71,plain,
    ( ~ v2_compts_1(sK2,sK0)
    | spl8_1 ),
    inference(avatar_component_clause,[],[f69])).

fof(f578,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f577,f41])).

fof(f577,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_compts_1(sK2,sK0)
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f576,f40])).

fof(f576,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_compts_1(sK2,sK0)
    | ~ spl8_46 ),
    inference(subsumption_resolution,[],[f570,f222])).

fof(f570,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_compts_1(sK2,sK0)
    | ~ spl8_46 ),
    inference(superposition,[],[f456,f94])).

fof(f456,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_compts_1(sK2,X0) )
    | ~ spl8_46 ),
    inference(avatar_component_clause,[],[f455])).

fof(f455,plain,
    ( spl8_46
  <=> ! [X0] :
        ( v2_compts_1(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).

fof(f549,plain,
    ( ~ spl8_15
    | spl8_45 ),
    inference(avatar_contradiction_clause,[],[f548])).

fof(f548,plain,
    ( $false
    | ~ spl8_15
    | spl8_45 ),
    inference(subsumption_resolution,[],[f534,f453])).

fof(f453,plain,
    ( ~ r1_tarski(sK2,k2_struct_0(sK1))
    | spl8_45 ),
    inference(avatar_component_clause,[],[f451])).

fof(f451,plain,
    ( spl8_45
  <=> r1_tarski(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).

fof(f457,plain,
    ( ~ spl8_45
    | spl8_46
    | ~ spl8_2
    | ~ spl8_21 ),
    inference(avatar_split_clause,[],[f449,f274,f73,f455,f451])).

fof(f274,plain,
    ( spl8_21
  <=> k2_struct_0(k1_pre_topc(sK1,sK2)) = sK7(sK1,k2_struct_0(k1_pre_topc(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f449,plain,
    ( ! [X0] :
        ( v2_compts_1(sK2,X0)
        | ~ r1_tarski(sK2,k2_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_2
    | ~ spl8_21 ),
    inference(subsumption_resolution,[],[f448,f79])).

fof(f79,plain,
    ( v2_compts_1(sK2,sK1)
    | ~ spl8_2 ),
    inference(forward_demodulation,[],[f74,f44])).

fof(f74,plain,
    ( v2_compts_1(sK3,sK1)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f448,plain,
    ( ! [X0] :
        ( ~ v2_compts_1(sK2,sK1)
        | v2_compts_1(sK2,X0)
        | ~ r1_tarski(sK2,k2_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl8_21 ),
    inference(superposition,[],[f63,f445])).

fof(f445,plain,
    ( sK2 = sK7(sK1,sK2)
    | ~ spl8_21 ),
    inference(forward_demodulation,[],[f276,f281])).

fof(f276,plain,
    ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK7(sK1,k2_struct_0(k1_pre_topc(sK1,sK2)))
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f274])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_compts_1(sK7(X1,X2),X1)
      | v2_compts_1(X2,X0)
      | ~ r1_tarski(X2,k2_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f440,plain,
    ( spl8_1
    | ~ spl8_19 ),
    inference(avatar_contradiction_clause,[],[f439])).

fof(f439,plain,
    ( $false
    | spl8_1
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f438,f71])).

fof(f438,plain,
    ( v2_compts_1(sK2,sK0)
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f437,f281])).

fof(f437,plain,
    ( v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f436,f222])).

fof(f436,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0)
    | ~ spl8_19 ),
    inference(forward_demodulation,[],[f435,f281])).

fof(f435,plain,
    ( ~ m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f434,f41])).

fof(f434,plain,
    ( ~ m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_pre_topc(sK1,sK0)
    | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0)
    | ~ spl8_19 ),
    inference(subsumption_resolution,[],[f432,f40])).

fof(f432,plain,
    ( ~ m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0)
    | ~ spl8_19 ),
    inference(superposition,[],[f267,f94])).

fof(f267,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),X0) )
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f266])).

fof(f266,plain,
    ( spl8_19
  <=> ! [X0] :
        ( v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

% (25338)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f277,plain,
    ( spl8_19
    | spl8_21
    | ~ spl8_15 ),
    inference(avatar_split_clause,[],[f263,f181,f274,f266])).

fof(f263,plain,
    ( ! [X1] :
        ( k2_struct_0(k1_pre_topc(sK1,sK2)) = sK7(sK1,k2_struct_0(k1_pre_topc(sK1,sK2)))
        | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),X1)
        | ~ m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X1)))
        | ~ m1_pre_topc(sK1,X1)
        | ~ l1_pre_topc(X1) )
    | ~ spl8_15 ),
    inference(resolution,[],[f183,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(X2,k2_struct_0(X1))
      | sK7(X1,X2) = X2
      | v2_compts_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f187,plain,(
    spl8_15 ),
    inference(avatar_contradiction_clause,[],[f186])).

fof(f186,plain,
    ( $false
    | spl8_15 ),
    inference(global_subsumption,[],[f175,f185,f182])).

fof(f182,plain,
    ( ~ r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1))
    | spl8_15 ),
    inference(avatar_component_clause,[],[f181])).

fof(f175,plain,
    ( r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2)) ),
    inference(subsumption_resolution,[],[f173,f82])).

fof(f173,plain,
    ( r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1))
    | ~ l1_pre_topc(k1_pre_topc(sK1,sK2))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f89,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | r1_tarski(k2_struct_0(X1),k2_struct_0(X0))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ( ( ! [X3] :
                      ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
                      | ~ r2_hidden(X3,u1_pre_topc(X0))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & ( ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
                    & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
                    & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) )
                  | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
                & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
                          & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
                          & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                | ~ r2_hidden(X3,u1_pre_topc(X0))
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X2,u1_pre_topc(X1)) )
          & ( ? [X4] :
                ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                & r2_hidden(X4,u1_pre_topc(X0))
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X2,u1_pre_topc(X1)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
     => ( ( ! [X3] :
              ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1)
              | ~ r2_hidden(X3,u1_pre_topc(X0))
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & ( ? [X4] :
              ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
              & r2_hidden(X4,u1_pre_topc(X0))
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
          | r2_hidden(sK4(X0,X1),u1_pre_topc(X1)) )
        & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1))) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X4] :
          ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1)
          & r2_hidden(X4,u1_pre_topc(X0))
          & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1))
        & r2_hidden(sK5(X0,X1),u1_pre_topc(X0))
        & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X5,X1,X0] :
      ( ? [X7] :
          ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
          & r2_hidden(X7,u1_pre_topc(X0))
          & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
     => ( k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5
        & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0))
        & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X4] :
                        ( k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2
                        & r2_hidden(X4,u1_pre_topc(X0))
                        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X5] :
                    ( ( ( r2_hidden(X5,u1_pre_topc(X1))
                        | ! [X6] :
                            ( k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5
                            | ~ r2_hidden(X6,u1_pre_topc(X0))
                            | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X7] :
                            ( k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5
                            & r2_hidden(X7,u1_pre_topc(X0))
                            & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X5,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              | ? [X2] :
                  ( ( ! [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                        | ~ r2_hidden(X3,u1_pre_topc(X0))
                        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | ~ r2_hidden(X2,u1_pre_topc(X1)) )
                  & ( ? [X3] :
                        ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                        & r2_hidden(X3,u1_pre_topc(X0))
                        & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                    | r2_hidden(X2,u1_pre_topc(X1)) )
                  & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
              | ~ r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
            & ( ( ! [X2] :
                    ( ( ( r2_hidden(X2,u1_pre_topc(X1))
                        | ! [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2
                            | ~ r2_hidden(X3,u1_pre_topc(X0))
                            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
                      & ( ? [X3] :
                            ( k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2
                            & r2_hidden(X3,u1_pre_topc(X0))
                            & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                        | ~ r2_hidden(X2,u1_pre_topc(X1)) ) )
                    | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
                & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) )
              | ~ m1_pre_topc(X1,X0) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).

fof(f77,plain,
    ( spl8_1
    | spl8_2 ),
    inference(avatar_split_clause,[],[f45,f73,f69])).

fof(f45,plain,
    ( v2_compts_1(sK3,sK1)
    | v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).

fof(f76,plain,
    ( ~ spl8_1
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f46,f73,f69])).

fof(f46,plain,
    ( ~ v2_compts_1(sK3,sK1)
    | ~ v2_compts_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:57:37 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.23/0.47  % (25334)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.23/0.49  % (25344)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.23/0.50  % (25329)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.23/0.50  % (25334)Refutation found. Thanks to Tanya!
% 0.23/0.50  % SZS status Theorem for theBenchmark
% 0.23/0.50  % SZS output start Proof for theBenchmark
% 0.23/0.50  fof(f629,plain,(
% 0.23/0.50    $false),
% 0.23/0.50    inference(avatar_sat_refutation,[],[f76,f77,f187,f277,f440,f457,f549,f580,f591,f612,f624])).
% 0.23/0.50  fof(f624,plain,(
% 0.23/0.50    spl8_2 | ~spl8_49),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f623])).
% 0.23/0.50  fof(f623,plain,(
% 0.23/0.50    $false | (spl8_2 | ~spl8_49)),
% 0.23/0.50    inference(subsumption_resolution,[],[f584,f592])).
% 0.23/0.50  fof(f592,plain,(
% 0.23/0.50    ~v2_compts_1(sK2,sK1) | spl8_2),
% 0.23/0.50    inference(forward_demodulation,[],[f75,f44])).
% 0.23/0.50  fof(f44,plain,(
% 0.23/0.50    sK2 = sK3),
% 0.23/0.50    inference(cnf_transformation,[],[f28])).
% 0.23/0.50  fof(f28,plain,(
% 0.23/0.50    ((((~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0)) & l1_pre_topc(sK0)),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f23,f27,f26,f25,f24])).
% 0.23/0.50  fof(f24,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0)) => (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) & l1_pre_topc(sK0))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f25,plain,(
% 0.23/0.50    ? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(X1,sK0)) => (? [X2] : (? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_pre_topc(sK1,sK0))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f26,plain,(
% 0.23/0.50    ? [X2] : (? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(X2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(X2,sK0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f27,plain,(
% 0.23/0.50    ? [X3] : ((~v2_compts_1(X3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(X3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK1)))) => ((~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)) & (v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)) & sK2 = sK3 & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f23,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f22])).
% 0.23/0.50  fof(f22,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~v2_compts_1(X3,X1) | ~v2_compts_1(X2,X0)) & (v2_compts_1(X3,X1) | v2_compts_1(X2,X0))) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.23/0.50    inference(nnf_transformation,[],[f12])).
% 0.23/0.50  fof(f12,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f11])).
% 0.23/0.50  fof(f11,plain,(
% 0.23/0.50    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((v2_compts_1(X2,X0) <~> v2_compts_1(X3,X1)) & X2 = X3) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_pre_topc(X1,X0)) & l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f9])).
% 0.23/0.50  fof(f9,negated_conjecture,(
% 0.23/0.50    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 0.23/0.50    inference(negated_conjecture,[],[f8])).
% 0.23/0.50  fof(f8,conjecture,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => (v2_compts_1(X2,X0) <=> v2_compts_1(X3,X1)))))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_compts_1)).
% 0.23/0.50  fof(f75,plain,(
% 0.23/0.50    ~v2_compts_1(sK3,sK1) | spl8_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f73])).
% 0.23/0.50  fof(f73,plain,(
% 0.23/0.50    spl8_2 <=> v2_compts_1(sK3,sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.23/0.50  fof(f584,plain,(
% 0.23/0.50    v2_compts_1(sK2,sK1) | ~spl8_49),
% 0.23/0.50    inference(avatar_component_clause,[],[f583])).
% 0.23/0.50  fof(f583,plain,(
% 0.23/0.50    spl8_49 <=> v2_compts_1(sK2,sK1)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_49])])).
% 0.23/0.50  fof(f612,plain,(
% 0.23/0.50    ~spl8_1 | ~spl8_50),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f611])).
% 0.23/0.50  fof(f611,plain,(
% 0.23/0.50    $false | (~spl8_1 | ~spl8_50)),
% 0.23/0.50    inference(subsumption_resolution,[],[f610,f70])).
% 0.23/0.50  fof(f70,plain,(
% 0.23/0.50    v2_compts_1(sK2,sK0) | ~spl8_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f69])).
% 0.23/0.50  fof(f69,plain,(
% 0.23/0.50    spl8_1 <=> v2_compts_1(sK2,sK0)),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.23/0.50  fof(f610,plain,(
% 0.23/0.50    ~v2_compts_1(sK2,sK0) | ~spl8_50),
% 0.23/0.50    inference(subsumption_resolution,[],[f609,f41])).
% 0.23/0.50  fof(f41,plain,(
% 0.23/0.50    m1_pre_topc(sK1,sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f28])).
% 0.23/0.50  fof(f609,plain,(
% 0.23/0.50    ~m1_pre_topc(sK1,sK0) | ~v2_compts_1(sK2,sK0) | ~spl8_50),
% 0.23/0.50    inference(subsumption_resolution,[],[f608,f40])).
% 0.23/0.50  fof(f40,plain,(
% 0.23/0.50    l1_pre_topc(sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f28])).
% 0.23/0.50  fof(f608,plain,(
% 0.23/0.50    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v2_compts_1(sK2,sK0) | ~spl8_50),
% 0.23/0.50    inference(subsumption_resolution,[],[f602,f222])).
% 0.23/0.50  fof(f222,plain,(
% 0.23/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.23/0.50    inference(superposition,[],[f42,f94])).
% 0.23/0.50  fof(f94,plain,(
% 0.23/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.23/0.50    inference(resolution,[],[f80,f47])).
% 0.23/0.50  % (25329)Refutation not found, incomplete strategy% (25329)------------------------------
% 0.23/0.50  % (25329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (25329)Termination reason: Refutation not found, incomplete strategy
% 0.23/0.50  
% 0.23/0.50  % (25329)Memory used [KB]: 6140
% 0.23/0.50  % (25329)Time elapsed: 0.086 s
% 0.23/0.50  % (25329)------------------------------
% 0.23/0.50  % (25329)------------------------------
% 0.23/0.50  fof(f47,plain,(
% 0.23/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f13])).
% 0.23/0.50  fof(f13,plain,(
% 0.23/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f1])).
% 0.23/0.50  fof(f1,axiom,(
% 0.23/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.23/0.50  fof(f80,plain,(
% 0.23/0.50    l1_struct_0(sK0)),
% 0.23/0.50    inference(resolution,[],[f48,f40])).
% 0.23/0.50  fof(f48,plain,(
% 0.23/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f14])).
% 0.23/0.50  fof(f14,plain,(
% 0.23/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f4])).
% 0.23/0.50  fof(f4,axiom,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.23/0.50  fof(f42,plain,(
% 0.23/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.23/0.50    inference(cnf_transformation,[],[f28])).
% 0.23/0.50  fof(f602,plain,(
% 0.23/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | ~v2_compts_1(sK2,sK0) | ~spl8_50),
% 0.23/0.50    inference(superposition,[],[f590,f94])).
% 0.23/0.50  fof(f590,plain,(
% 0.23/0.50    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1))) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | ~v2_compts_1(sK2,X1)) ) | ~spl8_50),
% 0.23/0.50    inference(avatar_component_clause,[],[f589])).
% 0.23/0.50  fof(f589,plain,(
% 0.23/0.50    spl8_50 <=> ! [X1] : (~v2_compts_1(sK2,X1) | ~l1_pre_topc(X1) | ~m1_pre_topc(sK1,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1))))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.23/0.50  fof(f591,plain,(
% 0.23/0.50    spl8_50 | spl8_49 | ~spl8_15),
% 0.23/0.50    inference(avatar_split_clause,[],[f587,f181,f583,f589])).
% 0.23/0.50  fof(f181,plain,(
% 0.23/0.50    spl8_15 <=> r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.23/0.50  fof(f587,plain,(
% 0.23/0.50    ( ! [X1] : (v2_compts_1(sK2,sK1) | ~v2_compts_1(sK2,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) ) | ~spl8_15),
% 0.23/0.50    inference(subsumption_resolution,[],[f119,f534])).
% 0.23/0.50  fof(f534,plain,(
% 0.23/0.50    r1_tarski(sK2,k2_struct_0(sK1)) | ~spl8_15),
% 0.23/0.50    inference(superposition,[],[f183,f281])).
% 0.23/0.50  fof(f281,plain,(
% 0.23/0.50    sK2 = k2_struct_0(k1_pre_topc(sK1,sK2))),
% 0.23/0.50    inference(forward_demodulation,[],[f280,f93])).
% 0.23/0.50  fof(f93,plain,(
% 0.23/0.50    sK2 = u1_struct_0(k1_pre_topc(sK1,sK2))),
% 0.23/0.50    inference(subsumption_resolution,[],[f91,f82])).
% 0.23/0.50  fof(f82,plain,(
% 0.23/0.50    l1_pre_topc(sK1)),
% 0.23/0.50    inference(subsumption_resolution,[],[f81,f40])).
% 0.23/0.50  fof(f81,plain,(
% 0.23/0.50    l1_pre_topc(sK1) | ~l1_pre_topc(sK0)),
% 0.23/0.50    inference(resolution,[],[f59,f41])).
% 0.23/0.50  fof(f59,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f16])).
% 0.23/0.50  fof(f16,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f5])).
% 0.23/0.50  fof(f5,axiom,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.23/0.50  fof(f91,plain,(
% 0.23/0.50    sK2 = u1_struct_0(k1_pre_topc(sK1,sK2)) | ~l1_pre_topc(sK1)),
% 0.23/0.50    inference(resolution,[],[f64,f78])).
% 0.23/0.50  fof(f78,plain,(
% 0.23/0.50    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.23/0.50    inference(forward_demodulation,[],[f43,f44])).
% 0.23/0.50  fof(f43,plain,(
% 0.23/0.50    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.23/0.50    inference(cnf_transformation,[],[f28])).
% 0.23/0.50  fof(f64,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f19])).
% 0.23/0.50  fof(f19,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (u1_struct_0(k1_pre_topc(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f6])).
% 0.23/0.50  fof(f6,axiom,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => u1_struct_0(k1_pre_topc(X0,X1)) = X1))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_pre_topc)).
% 0.23/0.50  fof(f280,plain,(
% 0.23/0.50    u1_struct_0(k1_pre_topc(sK1,sK2)) = k2_struct_0(k1_pre_topc(sK1,sK2))),
% 0.23/0.50    inference(resolution,[],[f221,f47])).
% 0.23/0.50  % (25346)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.23/0.50  fof(f221,plain,(
% 0.23/0.50    l1_struct_0(k1_pre_topc(sK1,sK2))),
% 0.23/0.50    inference(resolution,[],[f185,f48])).
% 0.23/0.50  fof(f185,plain,(
% 0.23/0.50    l1_pre_topc(k1_pre_topc(sK1,sK2))),
% 0.23/0.50    inference(subsumption_resolution,[],[f174,f82])).
% 0.23/0.50  fof(f174,plain,(
% 0.23/0.50    l1_pre_topc(k1_pre_topc(sK1,sK2)) | ~l1_pre_topc(sK1)),
% 0.23/0.50    inference(resolution,[],[f89,f59])).
% 0.23/0.50  fof(f89,plain,(
% 0.23/0.50    m1_pre_topc(k1_pre_topc(sK1,sK2),sK1)),
% 0.23/0.50    inference(subsumption_resolution,[],[f87,f82])).
% 0.23/0.50  fof(f87,plain,(
% 0.23/0.50    m1_pre_topc(k1_pre_topc(sK1,sK2),sK1) | ~l1_pre_topc(sK1)),
% 0.23/0.50    inference(resolution,[],[f65,f78])).
% 0.23/0.50  fof(f65,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f21])).
% 0.23/0.50  fof(f21,plain,(
% 0.23/0.50    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f20])).
% 0.23/0.50  fof(f20,plain,(
% 0.23/0.50    ! [X0,X1] : (m1_pre_topc(k1_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.23/0.50    inference(ennf_transformation,[],[f10])).
% 0.23/0.50  fof(f10,plain,(
% 0.23/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_pre_topc(k1_pre_topc(X0,X1),X0))),
% 0.23/0.50    inference(pure_predicate_removal,[],[f3])).
% 0.23/0.50  fof(f3,axiom,(
% 0.23/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => (m1_pre_topc(k1_pre_topc(X0,X1),X0) & v1_pre_topc(k1_pre_topc(X0,X1))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_pre_topc)).
% 0.23/0.50  fof(f183,plain,(
% 0.23/0.50    r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1)) | ~spl8_15),
% 0.23/0.50    inference(avatar_component_clause,[],[f181])).
% 0.23/0.50  fof(f119,plain,(
% 0.23/0.50    ( ! [X1] : (v2_compts_1(sK2,sK1) | ~v2_compts_1(sK2,X1) | ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) )),
% 0.23/0.50    inference(resolution,[],[f67,f78])).
% 0.23/0.50  fof(f67,plain,(
% 0.23/0.50    ( ! [X4,X0,X1] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | v2_compts_1(X4,X1) | ~v2_compts_1(X4,X0) | ~r1_tarski(X4,k2_struct_0(X1)) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(equality_resolution,[],[f60])).
% 0.23/0.50  fof(f60,plain,(
% 0.23/0.50    ( ! [X4,X2,X0,X1] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1))) | ~v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f39])).
% 0.23/0.50  fof(f39,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | (~v2_compts_1(sK7(X1,X2),X1) & sK7(X1,X2) = X2 & m1_subset_1(sK7(X1,X2),k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f37,f38])).
% 0.23/0.50  fof(f38,plain,(
% 0.23/0.50    ! [X2,X1] : (? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) => (~v2_compts_1(sK7(X1,X2),X1) & sK7(X1,X2) = X2 & m1_subset_1(sK7(X1,X2),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f37,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X4] : (v2_compts_1(X4,X1) | X2 != X4 | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(rectify,[],[f36])).
% 0.23/0.50  fof(f36,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) | ? [X3] : (~v2_compts_1(X3,X1) & X2 = X3 & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) & (! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) | ~v2_compts_1(X2,X0))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(nnf_transformation,[],[f18])).
% 0.23/0.50  fof(f18,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_compts_1(X2,X0) <=> ! [X3] : (v2_compts_1(X3,X1) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f17])).
% 0.23/0.50  fof(f17,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (! [X2] : (((v2_compts_1(X2,X0) <=> ! [X3] : ((v2_compts_1(X3,X1) | X2 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | ~r1_tarski(X2,k2_struct_0(X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f7])).
% 0.23/0.50  fof(f7,axiom,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,k2_struct_0(X1)) => (v2_compts_1(X2,X0) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (X2 = X3 => v2_compts_1(X3,X1))))))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_compts_1)).
% 0.23/0.50  fof(f580,plain,(
% 0.23/0.50    spl8_1 | ~spl8_46),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f579])).
% 0.23/0.50  fof(f579,plain,(
% 0.23/0.50    $false | (spl8_1 | ~spl8_46)),
% 0.23/0.50    inference(subsumption_resolution,[],[f578,f71])).
% 0.23/0.50  fof(f71,plain,(
% 0.23/0.50    ~v2_compts_1(sK2,sK0) | spl8_1),
% 0.23/0.50    inference(avatar_component_clause,[],[f69])).
% 0.23/0.50  fof(f578,plain,(
% 0.23/0.50    v2_compts_1(sK2,sK0) | ~spl8_46),
% 0.23/0.50    inference(subsumption_resolution,[],[f577,f41])).
% 0.23/0.50  fof(f577,plain,(
% 0.23/0.50    ~m1_pre_topc(sK1,sK0) | v2_compts_1(sK2,sK0) | ~spl8_46),
% 0.23/0.50    inference(subsumption_resolution,[],[f576,f40])).
% 0.23/0.50  fof(f576,plain,(
% 0.23/0.50    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_compts_1(sK2,sK0) | ~spl8_46),
% 0.23/0.50    inference(subsumption_resolution,[],[f570,f222])).
% 0.23/0.50  fof(f570,plain,(
% 0.23/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_compts_1(sK2,sK0) | ~spl8_46),
% 0.23/0.50    inference(superposition,[],[f456,f94])).
% 0.23/0.50  fof(f456,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_compts_1(sK2,X0)) ) | ~spl8_46),
% 0.23/0.50    inference(avatar_component_clause,[],[f455])).
% 0.23/0.50  fof(f455,plain,(
% 0.23/0.50    spl8_46 <=> ! [X0] : (v2_compts_1(sK2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_46])])).
% 0.23/0.50  fof(f549,plain,(
% 0.23/0.50    ~spl8_15 | spl8_45),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f548])).
% 0.23/0.50  fof(f548,plain,(
% 0.23/0.50    $false | (~spl8_15 | spl8_45)),
% 0.23/0.50    inference(subsumption_resolution,[],[f534,f453])).
% 0.23/0.50  fof(f453,plain,(
% 0.23/0.50    ~r1_tarski(sK2,k2_struct_0(sK1)) | spl8_45),
% 0.23/0.50    inference(avatar_component_clause,[],[f451])).
% 0.23/0.50  fof(f451,plain,(
% 0.23/0.50    spl8_45 <=> r1_tarski(sK2,k2_struct_0(sK1))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_45])])).
% 0.23/0.50  fof(f457,plain,(
% 0.23/0.50    ~spl8_45 | spl8_46 | ~spl8_2 | ~spl8_21),
% 0.23/0.50    inference(avatar_split_clause,[],[f449,f274,f73,f455,f451])).
% 0.23/0.50  fof(f274,plain,(
% 0.23/0.50    spl8_21 <=> k2_struct_0(k1_pre_topc(sK1,sK2)) = sK7(sK1,k2_struct_0(k1_pre_topc(sK1,sK2)))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.23/0.50  fof(f449,plain,(
% 0.23/0.50    ( ! [X0] : (v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | (~spl8_2 | ~spl8_21)),
% 0.23/0.50    inference(subsumption_resolution,[],[f448,f79])).
% 0.23/0.50  fof(f79,plain,(
% 0.23/0.50    v2_compts_1(sK2,sK1) | ~spl8_2),
% 0.23/0.50    inference(forward_demodulation,[],[f74,f44])).
% 0.23/0.50  fof(f74,plain,(
% 0.23/0.50    v2_compts_1(sK3,sK1) | ~spl8_2),
% 0.23/0.50    inference(avatar_component_clause,[],[f73])).
% 0.23/0.50  fof(f448,plain,(
% 0.23/0.50    ( ! [X0] : (~v2_compts_1(sK2,sK1) | v2_compts_1(sK2,X0) | ~r1_tarski(sK2,k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0)) ) | ~spl8_21),
% 0.23/0.50    inference(superposition,[],[f63,f445])).
% 0.23/0.50  fof(f445,plain,(
% 0.23/0.50    sK2 = sK7(sK1,sK2) | ~spl8_21),
% 0.23/0.50    inference(forward_demodulation,[],[f276,f281])).
% 0.23/0.50  fof(f276,plain,(
% 0.23/0.50    k2_struct_0(k1_pre_topc(sK1,sK2)) = sK7(sK1,k2_struct_0(k1_pre_topc(sK1,sK2))) | ~spl8_21),
% 0.23/0.50    inference(avatar_component_clause,[],[f274])).
% 0.23/0.50  fof(f63,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~v2_compts_1(sK7(X1,X2),X1) | v2_compts_1(X2,X0) | ~r1_tarski(X2,k2_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f39])).
% 0.23/0.50  fof(f440,plain,(
% 0.23/0.50    spl8_1 | ~spl8_19),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f439])).
% 0.23/0.50  fof(f439,plain,(
% 0.23/0.50    $false | (spl8_1 | ~spl8_19)),
% 0.23/0.50    inference(subsumption_resolution,[],[f438,f71])).
% 0.23/0.50  fof(f438,plain,(
% 0.23/0.50    v2_compts_1(sK2,sK0) | ~spl8_19),
% 0.23/0.50    inference(forward_demodulation,[],[f437,f281])).
% 0.23/0.50  fof(f437,plain,(
% 0.23/0.50    v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0) | ~spl8_19),
% 0.23/0.50    inference(subsumption_resolution,[],[f436,f222])).
% 0.23/0.50  fof(f436,plain,(
% 0.23/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0) | ~spl8_19),
% 0.23/0.50    inference(forward_demodulation,[],[f435,f281])).
% 0.23/0.50  fof(f435,plain,(
% 0.23/0.50    ~m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0) | ~spl8_19),
% 0.23/0.50    inference(subsumption_resolution,[],[f434,f41])).
% 0.23/0.50  fof(f434,plain,(
% 0.23/0.50    ~m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_pre_topc(sK1,sK0) | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0) | ~spl8_19),
% 0.23/0.50    inference(subsumption_resolution,[],[f432,f40])).
% 0.23/0.50  fof(f432,plain,(
% 0.23/0.50    ~m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),sK0) | ~spl8_19),
% 0.23/0.50    inference(superposition,[],[f267,f94])).
% 0.23/0.50  fof(f267,plain,(
% 0.23/0.50    ( ! [X0] : (~m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),X0)) ) | ~spl8_19),
% 0.23/0.50    inference(avatar_component_clause,[],[f266])).
% 0.23/0.50  fof(f266,plain,(
% 0.23/0.50    spl8_19 <=> ! [X0] : (v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0) | ~m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.23/0.50    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.23/0.50  % (25338)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.23/0.50  fof(f277,plain,(
% 0.23/0.50    spl8_19 | spl8_21 | ~spl8_15),
% 0.23/0.50    inference(avatar_split_clause,[],[f263,f181,f274,f266])).
% 0.23/0.50  fof(f263,plain,(
% 0.23/0.50    ( ! [X1] : (k2_struct_0(k1_pre_topc(sK1,sK2)) = sK7(sK1,k2_struct_0(k1_pre_topc(sK1,sK2))) | v2_compts_1(k2_struct_0(k1_pre_topc(sK1,sK2)),X1) | ~m1_subset_1(k2_struct_0(k1_pre_topc(sK1,sK2)),k1_zfmisc_1(u1_struct_0(X1))) | ~m1_pre_topc(sK1,X1) | ~l1_pre_topc(X1)) ) | ~spl8_15),
% 0.23/0.50    inference(resolution,[],[f183,f62])).
% 0.23/0.50  fof(f62,plain,(
% 0.23/0.50    ( ! [X2,X0,X1] : (~r1_tarski(X2,k2_struct_0(X1)) | sK7(X1,X2) = X2 | v2_compts_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f39])).
% 0.23/0.50  fof(f187,plain,(
% 0.23/0.50    spl8_15),
% 0.23/0.50    inference(avatar_contradiction_clause,[],[f186])).
% 0.23/0.50  fof(f186,plain,(
% 0.23/0.50    $false | spl8_15),
% 0.23/0.50    inference(global_subsumption,[],[f175,f185,f182])).
% 0.23/0.50  fof(f182,plain,(
% 0.23/0.50    ~r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1)) | spl8_15),
% 0.23/0.50    inference(avatar_component_clause,[],[f181])).
% 0.23/0.50  fof(f175,plain,(
% 0.23/0.50    r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1)) | ~l1_pre_topc(k1_pre_topc(sK1,sK2))),
% 0.23/0.50    inference(subsumption_resolution,[],[f173,f82])).
% 0.23/0.50  fof(f173,plain,(
% 0.23/0.50    r1_tarski(k2_struct_0(k1_pre_topc(sK1,sK2)),k2_struct_0(sK1)) | ~l1_pre_topc(k1_pre_topc(sK1,sK2)) | ~l1_pre_topc(sK1)),
% 0.23/0.50    inference(resolution,[],[f89,f49])).
% 0.23/0.50  fof(f49,plain,(
% 0.23/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | r1_tarski(k2_struct_0(X1),k2_struct_0(X0)) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.23/0.50    inference(cnf_transformation,[],[f35])).
% 0.23/0.50  fof(f35,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & ((sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) & r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & ((k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6])],[f31,f34,f33,f32])).
% 0.23/0.50  fof(f32,plain,(
% 0.23/0.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) => ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != sK4(X0,X1) | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(sK4(X0,X1),u1_pre_topc(X1))) & m1_subset_1(sK4(X0,X1),k1_zfmisc_1(u1_struct_0(X1)))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f33,plain,(
% 0.23/0.50    ! [X1,X0] : (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = sK4(X0,X1) & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) => (sK4(X0,X1) = k9_subset_1(u1_struct_0(X1),sK5(X0,X1),k2_struct_0(X1)) & r2_hidden(sK5(X0,X1),u1_pre_topc(X0)) & m1_subset_1(sK5(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f34,plain,(
% 0.23/0.50    ! [X5,X1,X0] : (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) => (k9_subset_1(u1_struct_0(X1),sK6(X0,X1,X5),k2_struct_0(X1)) = X5 & r2_hidden(sK6(X0,X1,X5),u1_pre_topc(X0)) & m1_subset_1(sK6(X0,X1,X5),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.23/0.50    introduced(choice_axiom,[])).
% 0.23/0.50  fof(f31,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X4] : (k9_subset_1(u1_struct_0(X1),X4,k2_struct_0(X1)) = X2 & r2_hidden(X4,u1_pre_topc(X0)) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X5] : (((r2_hidden(X5,u1_pre_topc(X1)) | ! [X6] : (k9_subset_1(u1_struct_0(X1),X6,k2_struct_0(X1)) != X5 | ~r2_hidden(X6,u1_pre_topc(X0)) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X7] : (k9_subset_1(u1_struct_0(X1),X7,k2_struct_0(X1)) = X5 & r2_hidden(X7,u1_pre_topc(X0)) & m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X5,u1_pre_topc(X1)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(rectify,[],[f30])).
% 0.23/0.50  fof(f30,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | ? [X2] : ((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(flattening,[],[f29])).
% 0.23/0.50  fof(f29,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : (((m1_pre_topc(X1,X0) | (? [X2] : (((! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X2,u1_pre_topc(X1)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) & ((! [X2] : (((r2_hidden(X2,u1_pre_topc(X1)) | ! [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) != X2 | ~r2_hidden(X3,u1_pre_topc(X0)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & (? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X2,u1_pre_topc(X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))) | ~m1_pre_topc(X1,X0))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(nnf_transformation,[],[f15])).
% 0.23/0.50  fof(f15,plain,(
% 0.23/0.50    ! [X0] : (! [X1] : ((m1_pre_topc(X1,X0) <=> (! [X2] : ((r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.23/0.50    inference(ennf_transformation,[],[f2])).
% 0.23/0.50  fof(f2,axiom,(
% 0.23/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => (r2_hidden(X2,u1_pre_topc(X1)) <=> ? [X3] : (k9_subset_1(u1_struct_0(X1),X3,k2_struct_0(X1)) = X2 & r2_hidden(X3,u1_pre_topc(X0)) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))) & r1_tarski(k2_struct_0(X1),k2_struct_0(X0))))))),
% 0.23/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_pre_topc)).
% 0.23/0.50  fof(f77,plain,(
% 0.23/0.50    spl8_1 | spl8_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f45,f73,f69])).
% 0.23/0.50  fof(f45,plain,(
% 0.23/0.50    v2_compts_1(sK3,sK1) | v2_compts_1(sK2,sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f28])).
% 0.23/0.50  fof(f76,plain,(
% 0.23/0.50    ~spl8_1 | ~spl8_2),
% 0.23/0.50    inference(avatar_split_clause,[],[f46,f73,f69])).
% 0.23/0.50  fof(f46,plain,(
% 0.23/0.50    ~v2_compts_1(sK3,sK1) | ~v2_compts_1(sK2,sK0)),
% 0.23/0.50    inference(cnf_transformation,[],[f28])).
% 0.23/0.50  % SZS output end Proof for theBenchmark
% 0.23/0.50  % (25334)------------------------------
% 0.23/0.50  % (25334)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.23/0.50  % (25334)Termination reason: Refutation
% 0.23/0.50  
% 0.23/0.50  % (25334)Memory used [KB]: 11001
% 0.23/0.50  % (25334)Time elapsed: 0.070 s
% 0.23/0.50  % (25334)------------------------------
% 0.23/0.50  % (25334)------------------------------
% 0.23/0.51  % (25323)Success in time 0.136 s
%------------------------------------------------------------------------------
