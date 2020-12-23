%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:42 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 191 expanded)
%              Number of leaves         :   17 (  66 expanded)
%              Depth                    :    8
%              Number of atoms          :  220 ( 518 expanded)
%              Number of equality atoms :    6 (  22 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f223,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f35,f38,f81,f93,f103,f122,f137,f159,f206,f208,f210,f214,f222])).

fof(f222,plain,
    ( ~ spl2_15
    | ~ spl2_9
    | ~ spl2_22
    | spl2_23 ),
    inference(avatar_split_clause,[],[f220,f212,f202,f88,f144])).

fof(f144,plain,
    ( spl2_15
  <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).

fof(f88,plain,
    ( spl2_9
  <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).

fof(f202,plain,
    ( spl2_22
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).

fof(f212,plain,
    ( spl2_23
  <=> r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).

fof(f220,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_23 ),
    inference(resolution,[],[f213,f58])).

fof(f58,plain,(
    ! [X2,X1] :
      ( r1_tarski(k7_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | ~ v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    inference(resolution,[],[f22,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,u1_pre_topc(X0))
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> r1_tarski(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).

fof(f213,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | spl2_23 ),
    inference(avatar_component_clause,[],[f212])).

fof(f214,plain,
    ( ~ spl2_6
    | spl2_2
    | ~ spl2_23
    | ~ spl2_11 ),
    inference(avatar_split_clause,[],[f141,f101,f212,f33,f72])).

fof(f72,plain,
    ( spl2_6
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f33,plain,
    ( spl2_2
  <=> r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f101,plain,
    ( spl2_11
  <=> ! [X0] :
        ( r1_tarski(sK1,X0)
        | ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).

fof(f141,plain,
    ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))
    | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ spl2_11 ),
    inference(superposition,[],[f102,f43])).

fof(f43,plain,(
    u1_pre_topc(sK0) = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(resolution,[],[f40,f19])).

fof(f19,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tops_2(X1,X0)
          <~> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
           => ( v2_tops_2(X1,X0)
            <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    inference(negated_conjecture,[],[f7])).

fof(f7,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v2_tops_2(X1,X0)
          <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).

fof(f40,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_pre_topc(X0) = k7_setfam_1(u1_struct_0(X0),k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) ) ),
    inference(resolution,[],[f25,f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

fof(f102,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),X0))
        | r1_tarski(sK1,X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) )
    | ~ spl2_11 ),
    inference(avatar_component_clause,[],[f101])).

fof(f210,plain,
    ( spl2_9
    | ~ spl2_10
    | ~ spl2_1 ),
    inference(avatar_split_clause,[],[f209,f30,f91,f88])).

fof(f91,plain,
    ( spl2_10
  <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f30,plain,
    ( spl2_1
  <=> v2_tops_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).

fof(f209,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_subsumption,[],[f19,f64])).

fof(f64,plain,
    ( ~ v2_tops_2(sK1,sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f23,f39])).

fof(f39,plain,(
    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1)) ),
    inference(resolution,[],[f25,f18])).

fof(f18,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(cnf_transformation,[],[f9])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
         => ( v1_tops_2(X1,X0)
          <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tops_2)).

fof(f208,plain,(
    spl2_22 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | spl2_22 ),
    inference(resolution,[],[f203,f19])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_22 ),
    inference(avatar_component_clause,[],[f202])).

fof(f206,plain,
    ( ~ spl2_22
    | ~ spl2_8
    | ~ spl2_15
    | spl2_9
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f198,f33,f88,f144,f79,f202])).

fof(f79,plain,
    ( spl2_8
  <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f198,plain,
    ( v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ spl2_2 ),
    inference(resolution,[],[f130,f37])).

fof(f37,plain,
    ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f33])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(duplicate_literal_removal,[],[f127])).

fof(f127,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(resolution,[],[f46,f27])).

fof(f27,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k7_setfam_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | ~ r1_tarski(X1,k7_setfam_1(X0,X2))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))
         => ( r1_tarski(k7_setfam_1(X0,X1),X2)
          <=> r1_tarski(X1,k7_setfam_1(X0,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).

fof(f46,plain,(
    ! [X2,X1] :
      ( ~ r1_tarski(k7_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1))
      | ~ l1_pre_topc(X1)
      | v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1)))) ) ),
    inference(resolution,[],[f21,f26])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,u1_pre_topc(X0))
      | v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f159,plain,(
    spl2_15 ),
    inference(avatar_contradiction_clause,[],[f158])).

fof(f158,plain,
    ( $false
    | spl2_15 ),
    inference(resolution,[],[f145,f18])).

fof(f145,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f137,plain,(
    spl2_6 ),
    inference(avatar_contradiction_clause,[],[f136])).

fof(f136,plain,
    ( $false
    | spl2_6 ),
    inference(resolution,[],[f131,f19])).

fof(f131,plain,
    ( ~ l1_pre_topc(sK0)
    | spl2_6 ),
    inference(resolution,[],[f126,f20])).

fof(f126,plain,
    ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_6 ),
    inference(resolution,[],[f73,f26])).

fof(f73,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_6 ),
    inference(avatar_component_clause,[],[f72])).

fof(f122,plain,(
    spl2_10 ),
    inference(avatar_contradiction_clause,[],[f121])).

fof(f121,plain,
    ( $false
    | spl2_10 ),
    inference(resolution,[],[f118,f18])).

fof(f118,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_10 ),
    inference(resolution,[],[f92,f26])).

fof(f92,plain,
    ( ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | spl2_10 ),
    inference(avatar_component_clause,[],[f91])).

fof(f103,plain,
    ( ~ spl2_10
    | spl2_11 ),
    inference(avatar_split_clause,[],[f98,f101,f91])).

fof(f98,plain,(
    ! [X0] :
      ( r1_tarski(sK1,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | ~ r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),X0))
      | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ) ),
    inference(superposition,[],[f27,f39])).

fof(f93,plain,
    ( ~ spl2_9
    | ~ spl2_10
    | spl2_1 ),
    inference(avatar_split_clause,[],[f86,f30,f91,f88])).

fof(f86,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(global_subsumption,[],[f19,f83])).

fof(f83,plain,
    ( v2_tops_2(sK1,sK0)
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK0)
    | ~ v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(superposition,[],[f24,f39])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0)
      | ~ v1_tops_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f81,plain,
    ( ~ spl2_6
    | spl2_8 ),
    inference(avatar_split_clause,[],[f66,f79,f72])).

fof(f66,plain,
    ( m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(superposition,[],[f26,f43])).

fof(f38,plain,
    ( spl2_1
    | spl2_2 ),
    inference(avatar_split_clause,[],[f16,f33,f30])).

fof(f16,plain,
    ( r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f35,plain,
    ( ~ spl2_1
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f17,f33,f30])).

fof(f17,plain,
    ( ~ r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ v2_tops_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f9])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:01:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (32396)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.20/0.47  % (32396)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.48  % (32404)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.20/0.48  % (32397)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.20/0.48  % (32389)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.20/0.49  % (32386)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.20/0.49  % (32395)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f223,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(avatar_sat_refutation,[],[f35,f38,f81,f93,f103,f122,f137,f159,f206,f208,f210,f214,f222])).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    ~spl2_15 | ~spl2_9 | ~spl2_22 | spl2_23),
% 0.20/0.49    inference(avatar_split_clause,[],[f220,f212,f202,f88,f144])).
% 0.20/0.49  fof(f144,plain,(
% 0.20/0.49    spl2_15 <=> m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_15])])).
% 0.20/0.49  fof(f88,plain,(
% 0.20/0.49    spl2_9 <=> v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_9])])).
% 0.20/0.49  fof(f202,plain,(
% 0.20/0.49    spl2_22 <=> l1_pre_topc(sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_22])])).
% 0.20/0.49  fof(f212,plain,(
% 0.20/0.49    spl2_23 <=> r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_23])])).
% 0.20/0.49  fof(f220,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_23),
% 0.20/0.49    inference(resolution,[],[f213,f58])).
% 0.20/0.49  fof(f58,plain,(
% 0.20/0.49    ( ! [X2,X1] : (r1_tarski(k7_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) | ~l1_pre_topc(X1) | ~v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) )),
% 0.20/0.49    inference(resolution,[],[f22,f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,plain,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => m1_subset_1(k7_setfam_1(X0,X1),k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | r1_tarski(X1,u1_pre_topc(X0)) | ~v1_tops_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> r1_tarski(X1,u1_pre_topc(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_tops_2)).
% 0.20/0.49  fof(f213,plain,(
% 0.20/0.49    ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | spl2_23),
% 0.20/0.49    inference(avatar_component_clause,[],[f212])).
% 0.20/0.49  fof(f214,plain,(
% 0.20/0.49    ~spl2_6 | spl2_2 | ~spl2_23 | ~spl2_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f141,f101,f212,f33,f72])).
% 0.20/0.49  fof(f72,plain,(
% 0.20/0.49    spl2_6 <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    spl2_2 <=> r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).
% 0.20/0.49  fof(f101,plain,(
% 0.20/0.49    spl2_11 <=> ! [X0] : (r1_tarski(sK1,X0) | ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_11])])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),u1_pre_topc(sK0)) | r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~spl2_11),
% 0.20/0.49    inference(superposition,[],[f102,f43])).
% 0.20/0.49  fof(f43,plain,(
% 0.20/0.49    u1_pre_topc(sK0) = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.49    inference(resolution,[],[f40,f19])).
% 0.20/0.49  fof(f19,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f9,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v2_tops_2(X1,X0) <~> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))) & m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) & l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f8])).
% 0.20/0.49  fof(f8,negated_conjecture,(
% 0.20/0.49    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.49    inference(negated_conjecture,[],[f7])).
% 0.20/0.49  fof(f7,conjecture,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v2_tops_2(X1,X0) <=> r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_tops_2)).
% 0.20/0.49  fof(f40,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(X0) | u1_pre_topc(X0) = k7_setfam_1(u1_struct_0(X0),k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0)))) )),
% 0.20/0.49    inference(resolution,[],[f25,f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f10])).
% 0.20/0.49  fof(f10,plain,(
% 0.20/0.49    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f4])).
% 0.20/0.49  fof(f4,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,plain,(
% 0.20/0.49    ! [X0,X1] : (k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => k7_setfam_1(X0,k7_setfam_1(X0,X1)) = X1)),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).
% 0.20/0.49  fof(f102,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),X0)) | r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) ) | ~spl2_11),
% 0.20/0.49    inference(avatar_component_clause,[],[f101])).
% 0.20/0.49  fof(f210,plain,(
% 0.20/0.49    spl2_9 | ~spl2_10 | ~spl2_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f209,f30,f91,f88])).
% 0.20/0.49  fof(f91,plain,(
% 0.20/0.49    spl2_10 <=> m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).
% 0.20/0.49  fof(f30,plain,(
% 0.20/0.49    spl2_1 <=> v2_tops_2(sK1,sK0)),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_1])])).
% 0.20/0.49  fof(f209,plain,(
% 0.20/0.49    ~v2_tops_2(sK1,sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    inference(global_subsumption,[],[f19,f64])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ~v2_tops_2(sK1,sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    inference(superposition,[],[f23,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    sK1 = k7_setfam_1(u1_struct_0(sK0),k7_setfam_1(u1_struct_0(sK0),sK1))),
% 0.20/0.49    inference(resolution,[],[f25,f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | v1_tops_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) => (v1_tops_2(X1,X0) <=> v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_tops_2)).
% 0.20/0.49  fof(f208,plain,(
% 0.20/0.49    spl2_22),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f207])).
% 0.20/0.49  fof(f207,plain,(
% 0.20/0.49    $false | spl2_22),
% 0.20/0.49    inference(resolution,[],[f203,f19])).
% 0.20/0.49  fof(f203,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | spl2_22),
% 0.20/0.49    inference(avatar_component_clause,[],[f202])).
% 0.20/0.49  fof(f206,plain,(
% 0.20/0.49    ~spl2_22 | ~spl2_8 | ~spl2_15 | spl2_9 | ~spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f198,f33,f88,f144,f79,f202])).
% 0.20/0.49  fof(f79,plain,(
% 0.20/0.49    spl2_8 <=> m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).
% 0.20/0.49  fof(f198,plain,(
% 0.20/0.49    v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~spl2_2),
% 0.20/0.49    inference(resolution,[],[f130,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~spl2_2),
% 0.20/0.49    inference(avatar_component_clause,[],[f33])).
% 0.20/0.49  fof(f130,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.20/0.49    inference(duplicate_literal_removal,[],[f127])).
% 0.20/0.49  fof(f127,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | v1_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~r1_tarski(X1,k7_setfam_1(u1_struct_0(X0),u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.20/0.49    inference(resolution,[],[f46,f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ( ! [X2,X0,X1] : (r1_tarski(k7_setfam_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) | ~r1_tarski(X1,k7_setfam_1(X0,X2)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))) )),
% 0.20/0.49    inference(cnf_transformation,[],[f15])).
% 0.20/0.49  fof(f15,plain,(
% 0.20/0.49    ! [X0,X1] : (! [X2] : ((r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.20/0.49    inference(ennf_transformation,[],[f3])).
% 0.20/0.49  fof(f3,axiom,(
% 0.20/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(X0))) => (r1_tarski(k7_setfam_1(X0,X1),X2) <=> r1_tarski(X1,k7_setfam_1(X0,X2)))))),
% 0.20/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_setfam_1)).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X2,X1] : (~r1_tarski(k7_setfam_1(u1_struct_0(X1),X2),u1_pre_topc(X1)) | ~l1_pre_topc(X1) | v1_tops_2(k7_setfam_1(u1_struct_0(X1),X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X1))))) )),
% 0.20/0.49    inference(resolution,[],[f21,f26])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,u1_pre_topc(X0)) | v1_tops_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f11])).
% 0.20/0.49  fof(f159,plain,(
% 0.20/0.49    spl2_15),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f158])).
% 0.20/0.49  fof(f158,plain,(
% 0.20/0.49    $false | spl2_15),
% 0.20/0.49    inference(resolution,[],[f145,f18])).
% 0.20/0.49  fof(f145,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_15),
% 0.20/0.49    inference(avatar_component_clause,[],[f144])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    spl2_6),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f136])).
% 0.20/0.49  fof(f136,plain,(
% 0.20/0.49    $false | spl2_6),
% 0.20/0.49    inference(resolution,[],[f131,f19])).
% 0.20/0.49  fof(f131,plain,(
% 0.20/0.49    ~l1_pre_topc(sK0) | spl2_6),
% 0.20/0.49    inference(resolution,[],[f126,f20])).
% 0.20/0.49  fof(f126,plain,(
% 0.20/0.49    ~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_6),
% 0.20/0.49    inference(resolution,[],[f73,f26])).
% 0.20/0.49  fof(f73,plain,(
% 0.20/0.49    ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_6),
% 0.20/0.49    inference(avatar_component_clause,[],[f72])).
% 0.20/0.49  fof(f122,plain,(
% 0.20/0.49    spl2_10),
% 0.20/0.49    inference(avatar_contradiction_clause,[],[f121])).
% 0.20/0.49  fof(f121,plain,(
% 0.20/0.49    $false | spl2_10),
% 0.20/0.49    inference(resolution,[],[f118,f18])).
% 0.20/0.49  fof(f118,plain,(
% 0.20/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_10),
% 0.20/0.49    inference(resolution,[],[f92,f26])).
% 0.20/0.49  fof(f92,plain,(
% 0.20/0.49    ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | spl2_10),
% 0.20/0.49    inference(avatar_component_clause,[],[f91])).
% 0.20/0.49  fof(f103,plain,(
% 0.20/0.49    ~spl2_10 | spl2_11),
% 0.20/0.49    inference(avatar_split_clause,[],[f98,f101,f91])).
% 0.20/0.49  fof(f98,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(sK1,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~r1_tarski(k7_setfam_1(u1_struct_0(sK0),sK1),k7_setfam_1(u1_struct_0(sK0),X0)) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))) )),
% 0.20/0.49    inference(superposition,[],[f27,f39])).
% 0.20/0.49  fof(f93,plain,(
% 0.20/0.49    ~spl2_9 | ~spl2_10 | spl2_1),
% 0.20/0.49    inference(avatar_split_clause,[],[f86,f30,f91,f88])).
% 0.20/0.49  fof(f86,plain,(
% 0.20/0.49    v2_tops_2(sK1,sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    inference(global_subsumption,[],[f19,f83])).
% 0.20/0.49  fof(f83,plain,(
% 0.20/0.49    v2_tops_2(sK1,sK0) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(sK0) | ~v1_tops_2(k7_setfam_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.49    inference(superposition,[],[f24,f39])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_tops_2(k7_setfam_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tops_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f12])).
% 0.20/0.49  fof(f81,plain,(
% 0.20/0.49    ~spl2_6 | spl2_8),
% 0.20/0.49    inference(avatar_split_clause,[],[f66,f79,f72])).
% 0.20/0.49  fof(f66,plain,(
% 0.20/0.49    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~m1_subset_1(k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.49    inference(superposition,[],[f26,f43])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    spl2_1 | spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f16,f33,f30])).
% 0.20/0.49  fof(f16,plain,(
% 0.20/0.49    r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | v2_tops_2(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~spl2_1 | ~spl2_2),
% 0.20/0.49    inference(avatar_split_clause,[],[f17,f33,f30])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ~r1_tarski(sK1,k7_setfam_1(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~v2_tops_2(sK1,sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f9])).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (32396)------------------------------
% 0.20/0.49  % (32396)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (32396)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (32396)Memory used [KB]: 10746
% 0.20/0.49  % (32396)Time elapsed: 0.055 s
% 0.20/0.49  % (32396)------------------------------
% 0.20/0.49  % (32396)------------------------------
% 0.20/0.49  % (32383)Success in time 0.135 s
%------------------------------------------------------------------------------
