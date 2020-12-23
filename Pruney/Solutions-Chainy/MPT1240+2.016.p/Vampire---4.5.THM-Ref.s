%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:18 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 279 expanded)
%              Number of leaves         :   37 ( 125 expanded)
%              Depth                    :   10
%              Number of atoms          :  476 (1610 expanded)
%              Number of equality atoms :   22 (  22 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f308,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f104,f110,f117,f148,f161,f170,f185,f208,f236,f259,f269,f274,f298,f299,f304])).

fof(f304,plain,
    ( ~ spl4_22
    | spl4_10
    | ~ spl4_11 ),
    inference(avatar_split_clause,[],[f283,f114,f107,f199])).

fof(f199,plain,
    ( spl4_22
  <=> r1_tarski(sK3,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f107,plain,
    ( spl4_10
  <=> r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f114,plain,
    ( spl4_11
  <=> r1_tarski(k1_tarski(sK1),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f283,plain,
    ( ~ r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | spl4_10
    | ~ spl4_11 ),
    inference(unit_resulting_resolution,[],[f116,f109,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( r1_tarski(X1,X2)
        & r1_tarski(X0,X1) )
     => r1_tarski(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f109,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | spl4_10 ),
    inference(avatar_component_clause,[],[f107])).

fof(f116,plain,
    ( r1_tarski(k1_tarski(sK1),sK3)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f299,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))
    | k1_tops_1(sK0,sK3) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | sK3 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | r1_tarski(sK3,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f298,plain,
    ( ~ spl4_8
    | ~ spl4_14
    | spl4_34
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f293,f266,f295,f145,f96])).

fof(f96,plain,
    ( spl4_8
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f145,plain,
    ( spl4_14
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f295,plain,
    ( spl4_34
  <=> k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f266,plain,
    ( spl4_30
  <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f293,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl4_30 ),
    inference(resolution,[],[f268,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f268,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f266])).

fof(f274,plain,
    ( spl4_31
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f247,f96,f91,f86,f76,f271])).

fof(f271,plain,
    ( spl4_31
  <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).

fof(f76,plain,
    ( spl4_4
  <=> r1_tarski(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f86,plain,
    ( spl4_6
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f91,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f247,plain,
    ( r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f98,f78,f93,f88,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
      | ~ r1_tarski(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))
              | ~ r1_tarski(X1,X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( r1_tarski(X1,X2)
               => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).

fof(f88,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f93,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f91])).

fof(f78,plain,
    ( r1_tarski(sK3,sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f76])).

fof(f98,plain,
    ( l1_pre_topc(sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f269,plain,
    ( spl4_30
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f250,f96,f86,f81,f266])).

fof(f81,plain,
    ( spl4_5
  <=> v3_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f250,plain,
    ( v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f98,f83,f88,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v3_pre_topc(X1,X0)
              | ~ v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v3_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).

fof(f83,plain,
    ( v3_pre_topc(sK3,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f81])).

fof(f259,plain,
    ( spl4_28
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f252,f96,f86,f256])).

fof(f256,plain,
    ( spl4_28
  <=> k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f252,plain,
    ( k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))
    | ~ spl4_6
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f98,f88,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f236,plain,
    ( ~ spl4_17
    | ~ spl4_1
    | ~ spl4_23
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f234,f182,f67,f205,f63,f167])).

fof(f167,plain,
    ( spl4_17
  <=> r1_tarski(k1_tops_1(sK0,sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).

fof(f63,plain,
    ( spl4_1
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f205,plain,
    ( spl4_23
  <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f67,plain,
    ( spl4_2
  <=> ! [X3] :
        ( ~ r2_hidden(sK1,X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v3_pre_topc(X3,sK0)
        | ~ r1_tarski(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f182,plain,
    ( spl4_19
  <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f234,plain,
    ( ~ m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_2
    | ~ spl4_19 ),
    inference(resolution,[],[f184,f68])).

fof(f68,plain,
    ( ! [X3] :
        ( ~ v3_pre_topc(X3,sK0)
        | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(sK1,X3)
        | ~ r1_tarski(X3,sK2) )
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f184,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f208,plain,
    ( spl4_23
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f203,f96,f91,f205])).

fof(f203,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f98,f93,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f185,plain,
    ( spl4_19
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f179,f101,f96,f91,f182])).

fof(f101,plain,
    ( spl4_9
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f179,plain,
    ( v3_pre_topc(k1_tops_1(sK0,sK2),sK0)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9 ),
    inference(unit_resulting_resolution,[],[f103,f98,f93,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k1_tops_1(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k1_tops_1(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).

fof(f103,plain,
    ( v2_pre_topc(sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f101])).

fof(f170,plain,
    ( spl4_17
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f165,f96,f91,f167])).

fof(f165,plain,
    ( r1_tarski(k1_tops_1(sK0,sK2),sK2)
    | ~ spl4_7
    | ~ spl4_8 ),
    inference(unit_resulting_resolution,[],[f98,f93,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tops_1(X0,X1),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_tops_1(X0,X1),X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => r1_tarski(k1_tops_1(X0,X1),X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).

fof(f161,plain,
    ( spl4_16
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f149,f86,f158])).

fof(f158,plain,
    ( spl4_16
  <=> sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).

fof(f149,plain,
    ( sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f88,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f148,plain,
    ( spl4_14
    | ~ spl4_6 ),
    inference(avatar_split_clause,[],[f137,f86,f145])).

fof(f137,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl4_6 ),
    inference(unit_resulting_resolution,[],[f88,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f117,plain,
    ( spl4_11
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f111,f71,f114])).

fof(f71,plain,
    ( spl4_3
  <=> r2_hidden(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f111,plain,
    ( r1_tarski(k1_tarski(sK1),sK3)
    | ~ spl4_3 ),
    inference(unit_resulting_resolution,[],[f73,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
      & ( r2_hidden(X0,X1)
        | ~ r1_tarski(k1_tarski(X0),X1) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f73,plain,
    ( r2_hidden(sK1,sK3)
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f110,plain,
    ( ~ spl4_10
    | spl4_1 ),
    inference(avatar_split_clause,[],[f105,f63,f107])).

fof(f105,plain,
    ( ~ r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))
    | spl4_1 ),
    inference(unit_resulting_resolution,[],[f65,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_tarski(X0),X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f65,plain,
    ( ~ r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f104,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f40,f101])).

fof(f40,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,
    ( ( ! [X3] :
          ( ~ r2_hidden(sK1,X3)
          | ~ r1_tarski(X3,sK2)
          | ~ v3_pre_topc(X3,sK0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & ( ( r2_hidden(sK1,sK3)
        & r1_tarski(sK3,sK2)
        & v3_pre_topc(sK3,sK0)
        & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) )
      | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1,X2] :
            ( ( ! [X3] :
                  ( ~ r2_hidden(X1,X3)
                  | ~ r1_tarski(X3,X2)
                  | ~ v3_pre_topc(X3,X0)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
            & ( ? [X4] :
                  ( r2_hidden(X1,X4)
                  & r1_tarski(X4,X2)
                  & v3_pre_topc(X4,X0)
                  & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
              | r2_hidden(X1,k1_tops_1(X0,X2)) )
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X2,X1] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,sK0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
            | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,sK0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
            | r2_hidden(X1,k1_tops_1(sK0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X2,X1] :
        ( ( ! [X3] :
              ( ~ r2_hidden(X1,X3)
              | ~ r1_tarski(X3,X2)
              | ~ v3_pre_topc(X3,sK0)
              | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
          | ~ r2_hidden(X1,k1_tops_1(sK0,X2)) )
        & ( ? [X4] :
              ( r2_hidden(X1,X4)
              & r1_tarski(X4,X2)
              & v3_pre_topc(X4,sK0)
              & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
          | r2_hidden(X1,k1_tops_1(sK0,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ( ! [X3] :
            ( ~ r2_hidden(sK1,X3)
            | ~ r1_tarski(X3,sK2)
            | ~ v3_pre_topc(X3,sK0)
            | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) )
        | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
      & ( ? [X4] :
            ( r2_hidden(sK1,X4)
            & r1_tarski(X4,sK2)
            & v3_pre_topc(X4,sK0)
            & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
        | r2_hidden(sK1,k1_tops_1(sK0,sK2)) )
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X4] :
        ( r2_hidden(sK1,X4)
        & r1_tarski(X4,sK2)
        & v3_pre_topc(X4,sK0)
        & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( r2_hidden(sK1,sK3)
      & r1_tarski(sK3,sK2)
      & v3_pre_topc(sK3,sK0)
      & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X4] :
                ( r2_hidden(X1,X4)
                & r1_tarski(X4,X2)
                & v3_pre_topc(X4,X0)
                & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( ! [X3] :
                ( ~ r2_hidden(X1,X3)
                | ~ r1_tarski(X3,X2)
                | ~ v3_pre_topc(X3,X0)
                | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | ~ r2_hidden(X1,k1_tops_1(X0,X2)) )
          & ( ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
            | r2_hidden(X1,k1_tops_1(X0,X2)) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <~> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1,X2] :
            ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,k1_tops_1(X0,X2))
            <=> ? [X3] :
                  ( r2_hidden(X1,X3)
                  & r1_tarski(X3,X2)
                  & v3_pre_topc(X3,X0)
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1,X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).

fof(f99,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f41,f96])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f37])).

fof(f94,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f42,f91])).

fof(f42,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f89,plain,
    ( spl4_1
    | spl4_6 ),
    inference(avatar_split_clause,[],[f43,f86,f63])).

fof(f43,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f84,plain,
    ( spl4_1
    | spl4_5 ),
    inference(avatar_split_clause,[],[f44,f81,f63])).

fof(f44,plain,
    ( v3_pre_topc(sK3,sK0)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f79,plain,
    ( spl4_1
    | spl4_4 ),
    inference(avatar_split_clause,[],[f45,f76,f63])).

fof(f45,plain,
    ( r1_tarski(sK3,sK2)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f74,plain,
    ( spl4_1
    | spl4_3 ),
    inference(avatar_split_clause,[],[f46,f71,f63])).

fof(f46,plain,
    ( r2_hidden(sK1,sK3)
    | r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,
    ( ~ spl4_1
    | spl4_2 ),
    inference(avatar_split_clause,[],[f47,f67,f63])).

fof(f47,plain,(
    ! [X3] :
      ( ~ r2_hidden(sK1,X3)
      | ~ r1_tarski(X3,sK2)
      | ~ v3_pre_topc(X3,sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r2_hidden(sK1,k1_tops_1(sK0,sK2)) ) ),
    inference(cnf_transformation,[],[f37])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n010.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 15:15:29 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.49  % (7325)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.21/0.50  % (7324)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.21/0.50  % (7319)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.21/0.50  % (7317)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.21/0.50  % (7328)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.21/0.50  % (7320)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.21/0.50  % (7337)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.21/0.50  % (7316)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.21/0.50  % (7329)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.21/0.51  % (7320)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % (7315)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.21/0.51  % (7321)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.51  % (7332)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.21/0.51  % (7324)Refutation not found, incomplete strategy% (7324)------------------------------
% 0.21/0.51  % (7324)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (7324)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (7324)Memory used [KB]: 10618
% 0.21/0.51  % (7324)Time elapsed: 0.095 s
% 0.21/0.51  % (7324)------------------------------
% 0.21/0.51  % (7324)------------------------------
% 0.21/0.51  % (7327)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.51  % (7336)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.21/0.52  % (7331)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.21/0.52  % (7335)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.21/0.52  % (7318)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f308,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f104,f110,f117,f148,f161,f170,f185,f208,f236,f259,f269,f274,f298,f299,f304])).
% 0.21/0.52  fof(f304,plain,(
% 0.21/0.52    ~spl4_22 | spl4_10 | ~spl4_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f283,f114,f107,f199])).
% 0.21/0.52  fof(f199,plain,(
% 0.21/0.52    spl4_22 <=> r1_tarski(sK3,k1_tops_1(sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.21/0.52  fof(f107,plain,(
% 0.21/0.52    spl4_10 <=> r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl4_11 <=> r1_tarski(k1_tarski(sK1),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    ~r1_tarski(sK3,k1_tops_1(sK0,sK2)) | (spl4_10 | ~spl4_11)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f116,f109,f48])).
% 0.21/0.52  fof(f48,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f17])).
% 0.21/0.52  fof(f17,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.21/0.52    inference(flattening,[],[f16])).
% 0.21/0.52  fof(f16,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.21/0.52  fof(f109,plain,(
% 0.21/0.52    ~r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | spl4_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f107])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    r1_tarski(k1_tarski(sK1),sK3) | ~spl4_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f114])).
% 0.21/0.52  fof(f299,plain,(
% 0.21/0.52    k3_subset_1(u1_struct_0(sK0),sK3) != k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) | k1_tops_1(sK0,sK3) != k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) | sK3 != k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) | r1_tarski(sK3,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f298,plain,(
% 0.21/0.52    ~spl4_8 | ~spl4_14 | spl4_34 | ~spl4_30),
% 0.21/0.52    inference(avatar_split_clause,[],[f293,f266,f295,f145,f96])).
% 0.21/0.52  fof(f96,plain,(
% 0.21/0.52    spl4_8 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl4_14 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.21/0.52  fof(f295,plain,(
% 0.21/0.52    spl4_34 <=> k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    spl4_30 <=> v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.21/0.52  fof(f293,plain,(
% 0.21/0.52    k3_subset_1(u1_struct_0(sK0),sK3) = k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)) | ~m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl4_30),
% 0.21/0.52    inference(resolution,[],[f268,f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f5])).
% 0.21/0.52  fof(f5,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.52  fof(f268,plain,(
% 0.21/0.52    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | ~spl4_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f266])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    spl4_31 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f247,f96,f91,f86,f76,f271])).
% 0.21/0.52  fof(f271,plain,(
% 0.21/0.52    spl4_31 <=> r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_31])])).
% 0.21/0.52  fof(f76,plain,(
% 0.21/0.52    spl4_4 <=> r1_tarski(sK3,sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.21/0.52  fof(f86,plain,(
% 0.21/0.52    spl4_6 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    spl4_7 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f98,f78,f93,f88,f51])).
% 0.21/0.52  fof(f51,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : (r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f18])).
% 0.21/0.52  fof(f18,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2)) | ~r1_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X1,X2) => r1_tarski(k1_tops_1(X0,X1),k1_tops_1(X0,X2))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tops_1)).
% 0.21/0.52  fof(f88,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f86])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_7),
% 0.21/0.52    inference(avatar_component_clause,[],[f91])).
% 0.21/0.52  fof(f78,plain,(
% 0.21/0.52    r1_tarski(sK3,sK2) | ~spl4_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f76])).
% 0.21/0.52  fof(f98,plain,(
% 0.21/0.52    l1_pre_topc(sK0) | ~spl4_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f96])).
% 0.21/0.52  fof(f269,plain,(
% 0.21/0.52    spl4_30 | ~spl4_5 | ~spl4_6 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f250,f96,f86,f81,f266])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    spl4_5 <=> v3_pre_topc(sK3,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.21/0.52  fof(f250,plain,(
% 0.21/0.52    v4_pre_topc(k3_subset_1(u1_struct_0(sK0),sK3),sK0) | (~spl4_5 | ~spl4_6 | ~spl4_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f98,f83,f88,f54])).
% 0.21/0.52  fof(f54,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (((v3_pre_topc(X1,X0) | ~v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> v4_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_tops_1)).
% 0.21/0.52  fof(f83,plain,(
% 0.21/0.52    v3_pre_topc(sK3,sK0) | ~spl4_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f81])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    spl4_28 | ~spl4_6 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f252,f96,f86,f256])).
% 0.21/0.52  fof(f256,plain,(
% 0.21/0.52    spl4_28 <=> k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.21/0.52  fof(f252,plain,(
% 0.21/0.52    k1_tops_1(sK0,sK3) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),sK3))) | (~spl4_6 | ~spl4_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f98,f88,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.52  fof(f236,plain,(
% 0.21/0.52    ~spl4_17 | ~spl4_1 | ~spl4_23 | ~spl4_2 | ~spl4_19),
% 0.21/0.52    inference(avatar_split_clause,[],[f234,f182,f67,f205,f63,f167])).
% 0.21/0.52  fof(f167,plain,(
% 0.21/0.52    spl4_17 <=> r1_tarski(k1_tops_1(sK0,sK2),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_17])])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    spl4_1 <=> r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    spl4_23 <=> m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    spl4_2 <=> ! [X3] : (~r2_hidden(sK1,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X3,sK0) | ~r1_tarski(X3,sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    spl4_19 <=> v3_pre_topc(k1_tops_1(sK0,sK2),sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    ~m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | ~r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl4_2 | ~spl4_19)),
% 0.21/0.52    inference(resolution,[],[f184,f68])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    ( ! [X3] : (~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2)) ) | ~spl4_2),
% 0.21/0.52    inference(avatar_component_clause,[],[f67])).
% 0.21/0.52  fof(f184,plain,(
% 0.21/0.52    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | ~spl4_19),
% 0.21/0.52    inference(avatar_component_clause,[],[f182])).
% 0.21/0.52  fof(f208,plain,(
% 0.21/0.52    spl4_23 | ~spl4_7 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f203,f96,f91,f205])).
% 0.21/0.52  fof(f203,plain,(
% 0.21/0.52    m1_subset_1(k1_tops_1(sK0,sK2),k1_zfmisc_1(u1_struct_0(sK0))) | (~spl4_7 | ~spl4_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f98,f93,f56])).
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f25])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f7])).
% 0.21/0.52  fof(f7,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).
% 0.21/0.52  fof(f185,plain,(
% 0.21/0.52    spl4_19 | ~spl4_7 | ~spl4_8 | ~spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f179,f101,f96,f91,f182])).
% 0.21/0.52  fof(f101,plain,(
% 0.21/0.52    spl4_9 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.21/0.52  fof(f179,plain,(
% 0.21/0.52    v3_pre_topc(k1_tops_1(sK0,sK2),sK0) | (~spl4_7 | ~spl4_8 | ~spl4_9)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f103,f98,f93,f53])).
% 0.21/0.52  fof(f53,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(k1_tops_1(X0,X1),X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,plain,(
% 0.21/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f21])).
% 0.21/0.52  fof(f21,plain,(
% 0.21/0.52    ! [X0,X1] : (v3_pre_topc(k1_tops_1(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k1_tops_1(X0,X1),X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_tops_1)).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    v2_pre_topc(sK0) | ~spl4_9),
% 0.21/0.52    inference(avatar_component_clause,[],[f101])).
% 0.21/0.52  fof(f170,plain,(
% 0.21/0.52    spl4_17 | ~spl4_7 | ~spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f165,f96,f91,f167])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    r1_tarski(k1_tops_1(sK0,sK2),sK2) | (~spl4_7 | ~spl4_8)),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f98,f93,f52])).
% 0.21/0.52  fof(f52,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f20])).
% 0.21/0.52  fof(f20,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (r1_tarski(k1_tops_1(X0,X1),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k1_tops_1(X0,X1),X1)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tops_1)).
% 0.21/0.52  fof(f161,plain,(
% 0.21/0.52    spl4_16 | ~spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f149,f86,f158])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    spl4_16 <=> sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_16])])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    sK3 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK3)) | ~spl4_6),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f88,f58])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f27])).
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.52  fof(f148,plain,(
% 0.21/0.52    spl4_14 | ~spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f137,f86,f145])).
% 0.21/0.52  fof(f137,plain,(
% 0.21/0.52    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK3),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl4_6),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f88,f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.21/0.52  fof(f117,plain,(
% 0.21/0.52    spl4_11 | ~spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f111,f71,f114])).
% 0.21/0.52  fof(f71,plain,(
% 0.21/0.52    spl4_3 <=> r2_hidden(sK1,sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.21/0.52  fof(f111,plain,(
% 0.21/0.52    r1_tarski(k1_tarski(sK1),sK3) | ~spl4_3),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f73,f50])).
% 0.21/0.52  fof(f50,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f38,plain,(
% 0.21/0.52    ! [X0,X1] : ((r1_tarski(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) & (r2_hidden(X0,X1) | ~r1_tarski(k1_tarski(X0),X1)))),
% 0.21/0.52    inference(nnf_transformation,[],[f2])).
% 0.21/0.52  fof(f2,axiom,(
% 0.21/0.52    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.21/0.52  fof(f73,plain,(
% 0.21/0.52    r2_hidden(sK1,sK3) | ~spl4_3),
% 0.21/0.52    inference(avatar_component_clause,[],[f71])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    ~spl4_10 | spl4_1),
% 0.21/0.52    inference(avatar_split_clause,[],[f105,f63,f107])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    ~r1_tarski(k1_tarski(sK1),k1_tops_1(sK0,sK2)) | spl4_1),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f65,f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~r1_tarski(k1_tarski(X0),X1) | r2_hidden(X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f38])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    ~r2_hidden(sK1,k1_tops_1(sK0,sK2)) | spl4_1),
% 0.21/0.52    inference(avatar_component_clause,[],[f63])).
% 0.21/0.52  fof(f104,plain,(
% 0.21/0.52    spl4_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f40,f101])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    v2_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f37,plain,(
% 0.21/0.52    ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & ((r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f33,f36,f35,f34])).
% 0.21/0.52  fof(f34,plain,(
% 0.21/0.52    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ? [X2,X1] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(X1,k1_tops_1(sK0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(X1,k1_tops_1(sK0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => ((! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) & (? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ? [X4] : (r2_hidden(sK1,X4) & r1_tarski(X4,sK2) & v3_pre_topc(X4,sK0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))) => (r2_hidden(sK1,sK3) & r1_tarski(sK3,sK2) & v3_pre_topc(sK3,sK0) & m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f33,plain,(
% 0.21/0.52    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X4] : (r2_hidden(X1,X4) & r1_tarski(X4,X2) & v3_pre_topc(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(rectify,[],[f32])).
% 0.21/0.52  fof(f32,plain,(
% 0.21/0.52    ? [X0] : (? [X1,X2] : ((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f31])).
% 0.21/0.52  fof(f31,plain,(
% 0.21/0.52    ? [X0] : (? [X1,X2] : (((! [X3] : (~r2_hidden(X1,X3) | ~r1_tarski(X3,X2) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~r2_hidden(X1,k1_tops_1(X0,X2))) & (? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | r2_hidden(X1,k1_tops_1(X0,X2)))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(nnf_transformation,[],[f15])).
% 0.21/0.52  fof(f15,plain,(
% 0.21/0.52    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f14])).
% 0.21/0.52  fof(f14,plain,(
% 0.21/0.52    ? [X0] : (? [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <~> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f13])).
% 0.21/0.52  fof(f13,negated_conjecture,(
% 0.21/0.52    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f12])).
% 0.21/0.52  fof(f12,conjecture,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t54_tops_1)).
% 0.21/0.52  fof(f99,plain,(
% 0.21/0.52    spl4_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f41,f96])).
% 0.21/0.52  fof(f41,plain,(
% 0.21/0.52    l1_pre_topc(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f94,plain,(
% 0.21/0.52    spl4_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f42,f91])).
% 0.21/0.52  fof(f42,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    spl4_1 | spl4_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f43,f86,f63])).
% 0.21/0.52  fof(f43,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    spl4_1 | spl4_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f44,f81,f63])).
% 0.21/0.52  fof(f44,plain,(
% 0.21/0.52    v3_pre_topc(sK3,sK0) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f79,plain,(
% 0.21/0.52    spl4_1 | spl4_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f45,f76,f63])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    r1_tarski(sK3,sK2) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f74,plain,(
% 0.21/0.52    spl4_1 | spl4_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f46,f71,f63])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    r2_hidden(sK1,sK3) | r2_hidden(sK1,k1_tops_1(sK0,sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ~spl4_1 | spl4_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f47,f67,f63])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ( ! [X3] : (~r2_hidden(sK1,X3) | ~r1_tarski(X3,sK2) | ~v3_pre_topc(X3,sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(sK1,k1_tops_1(sK0,sK2))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f37])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (7320)------------------------------
% 0.21/0.52  % (7320)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (7320)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (7320)Memory used [KB]: 10874
% 0.21/0.52  % (7320)Time elapsed: 0.091 s
% 0.21/0.52  % (7320)------------------------------
% 0.21/0.52  % (7320)------------------------------
% 0.21/0.52  % (7313)Success in time 0.161 s
%------------------------------------------------------------------------------
