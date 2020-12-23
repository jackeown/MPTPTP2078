%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:12:32 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  115 ( 220 expanded)
%              Number of leaves         :   25 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  403 ( 869 expanded)
%              Number of equality atoms :   32 (  77 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f525,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f105,f131,f146,f163,f206,f208,f213,f238,f243,f269,f363,f377,f420,f484,f512,f520,f524])).

fof(f524,plain,
    ( spl9_22
    | ~ spl9_26 ),
    inference(avatar_contradiction_clause,[],[f522])).

fof(f522,plain,
    ( $false
    | spl9_22
    | ~ spl9_26 ),
    inference(unit_resulting_resolution,[],[f237,f302,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,k1_xboole_0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

fof(f302,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl9_26 ),
    inference(avatar_component_clause,[],[f301])).

fof(f301,plain,
    ( spl9_26
  <=> r1_tarski(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).

fof(f237,plain,
    ( k1_xboole_0 != sK2
    | spl9_22 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl9_22
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).

fof(f520,plain,
    ( spl9_26
    | ~ spl9_39 ),
    inference(avatar_split_clause,[],[f519,f510,f301])).

fof(f510,plain,
    ( spl9_39
  <=> ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).

fof(f519,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | ~ spl9_39 ),
    inference(duplicate_literal_removal,[],[f517])).

fof(f517,plain,
    ( r1_tarski(sK2,k1_xboole_0)
    | r1_tarski(sK2,k1_xboole_0)
    | ~ spl9_39 ),
    inference(resolution,[],[f513,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK4(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f513,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK4(X0,k1_xboole_0),sK2)
        | r1_tarski(X0,k1_xboole_0) )
    | ~ spl9_39 ),
    inference(resolution,[],[f511,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1),X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f511,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,sK2) )
    | ~ spl9_39 ),
    inference(avatar_component_clause,[],[f510])).

fof(f512,plain,
    ( ~ spl9_5
    | spl9_39
    | ~ spl9_3
    | ~ spl9_11
    | ~ spl9_37 ),
    inference(avatar_split_clause,[],[f507,f482,f143,f93,f510,f102])).

fof(f102,plain,
    ( spl9_5
  <=> r1_tarski(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).

fof(f93,plain,
    ( spl9_3
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).

fof(f143,plain,
    ( spl9_11
  <=> k1_xboole_0 = k1_tops_1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).

fof(f482,plain,
    ( spl9_37
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).

fof(f507,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,sK2)
        | ~ r1_tarski(sK2,sK1) )
    | ~ spl9_3
    | ~ spl9_11
    | ~ spl9_37 ),
    inference(forward_demodulation,[],[f502,f144])).

fof(f144,plain,
    ( k1_xboole_0 = k1_tops_1(sK0,sK1)
    | ~ spl9_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f502,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,sK2)
        | r2_hidden(X3,k1_tops_1(sK0,sK1))
        | ~ r1_tarski(sK2,sK1) )
    | ~ spl9_3
    | ~ spl9_37 ),
    inference(resolution,[],[f483,f95])).

fof(f95,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f483,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,k1_tops_1(sK0,X0))
        | ~ r1_tarski(sK2,X0) )
    | ~ spl9_37 ),
    inference(avatar_component_clause,[],[f482])).

fof(f484,plain,
    ( ~ spl9_20
    | ~ spl9_1
    | spl9_37
    | ~ spl9_2
    | ~ spl9_23 ),
    inference(avatar_split_clause,[],[f432,f240,f88,f482,f83,f210])).

fof(f210,plain,
    ( spl9_20
  <=> v3_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).

fof(f83,plain,
    ( spl9_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).

fof(f88,plain,
    ( spl9_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).

fof(f240,plain,
    ( spl9_23
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).

fof(f432,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ v3_pre_topc(sK2,sK0)
        | ~ r1_tarski(sK2,X0)
        | ~ r2_hidden(X1,sK2)
        | r2_hidden(X1,k1_tops_1(sK0,X0)) )
    | ~ spl9_23 ),
    inference(resolution,[],[f242,f59])).

fof(f59,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ r1_tarski(X3,X2)
      | ~ r2_hidden(X1,X3)
      | r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( r2_hidden(X1,k1_tops_1(X0,X2))
          <=> ? [X3] :
                ( r2_hidden(X1,X3)
                & r1_tarski(X3,X2)
                & v3_pre_topc(X3,X0)
                & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).

fof(f242,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl9_23 ),
    inference(avatar_component_clause,[],[f240])).

fof(f420,plain,
    ( spl9_11
    | ~ spl9_28 ),
    inference(avatar_contradiction_clause,[],[f418])).

fof(f418,plain,
    ( $false
    | spl9_11
    | ~ spl9_28 ),
    inference(unit_resulting_resolution,[],[f145,f376,f52])).

fof(f376,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl9_28 ),
    inference(avatar_component_clause,[],[f374])).

fof(f374,plain,
    ( spl9_28
  <=> r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).

fof(f145,plain,
    ( k1_xboole_0 != k1_tops_1(sK0,sK1)
    | spl9_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f377,plain,
    ( spl9_28
    | ~ spl9_27 ),
    inference(avatar_split_clause,[],[f372,f361,f374])).

fof(f361,plain,
    ( spl9_27
  <=> ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).

fof(f372,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl9_27 ),
    inference(duplicate_literal_removal,[],[f370])).

fof(f370,plain,
    ( r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)
    | ~ spl9_27 ),
    inference(resolution,[],[f365,f65])).

fof(f365,plain,
    ( ! [X2] :
        ( r2_hidden(sK4(k1_tops_1(sK0,sK1),X2),k1_xboole_0)
        | r1_tarski(k1_tops_1(sK0,sK1),X2) )
    | ~ spl9_27 ),
    inference(resolution,[],[f362,f64])).

fof(f362,plain,
    ( ! [X3] :
        ( ~ r2_hidden(X3,k1_tops_1(sK0,sK1))
        | r2_hidden(X3,k1_xboole_0) )
    | ~ spl9_27 ),
    inference(avatar_component_clause,[],[f361])).

fof(f363,plain,
    ( ~ spl9_1
    | ~ spl9_3
    | ~ spl9_2
    | spl9_27
    | ~ spl9_24 ),
    inference(avatar_split_clause,[],[f321,f267,f361,f88,f93,f83])).

fof(f267,plain,
    ( spl9_24
  <=> ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
        | k1_xboole_0 = sK3(sK0,X0,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).

fof(f321,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK1)) )
    | ~ spl9_24 ),
    inference(duplicate_literal_removal,[],[f320])).

fof(f320,plain,
    ( ! [X3] :
        ( r2_hidden(X3,k1_xboole_0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK1))
        | ~ r2_hidden(X3,k1_tops_1(sK0,sK1)) )
    | ~ spl9_24 ),
    inference(superposition,[],[f58,f268])).

fof(f268,plain,
    ( ! [X0] :
        ( k1_xboole_0 = sK3(sK0,X0,sK1)
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl9_24 ),
    inference(avatar_component_clause,[],[f267])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,sK3(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f269,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | ~ spl9_3
    | spl9_24
    | ~ spl9_19 ),
    inference(avatar_split_clause,[],[f265,f204,f267,f93,f88,f83])).

fof(f204,plain,
    ( spl9_19
  <=> ! [X1,X0] :
        ( k1_xboole_0 = sK3(sK0,X0,X1)
        | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ r1_tarski(sK3(sK0,X0,X1),sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).

fof(f265,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3(sK0,X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl9_19 ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k1_tops_1(sK0,sK1))
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3(sK0,X0,sK1)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ r2_hidden(X0,k1_tops_1(sK0,sK1)) )
    | ~ spl9_19 ),
    inference(resolution,[],[f205,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(sK3(X0,X1,X2),X2)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f205,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(sK3(sK0,X0,X1),sK1)
        | ~ r2_hidden(X0,k1_tops_1(sK0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = sK3(sK0,X0,X1) )
    | ~ spl9_19 ),
    inference(avatar_component_clause,[],[f204])).

fof(f243,plain,
    ( ~ spl9_4
    | spl9_23 ),
    inference(avatar_split_clause,[],[f38,f240,f98])).

fof(f98,plain,
    ( spl9_4
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).

fof(f38,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).

fof(f238,plain,
    ( ~ spl9_4
    | ~ spl9_22 ),
    inference(avatar_split_clause,[],[f41,f235,f98])).

fof(f41,plain,
    ( k1_xboole_0 != sK2
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f213,plain,
    ( ~ spl9_4
    | spl9_20 ),
    inference(avatar_split_clause,[],[f40,f210,f98])).

fof(f40,plain,
    ( v3_pre_topc(sK2,sK0)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f208,plain,
    ( ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_11 ),
    inference(avatar_contradiction_clause,[],[f207])).

fof(f207,plain,
    ( $false
    | ~ spl9_2
    | ~ spl9_3
    | ~ spl9_4
    | spl9_11 ),
    inference(unit_resulting_resolution,[],[f90,f95,f145,f99,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 = k1_tops_1(X0,X1)
      | ~ v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> k1_xboole_0 = k1_tops_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).

fof(f99,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl9_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f90,plain,
    ( l1_pre_topc(sK0)
    | ~ spl9_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f206,plain,
    ( ~ spl9_1
    | ~ spl9_2
    | spl9_19
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(avatar_split_clause,[],[f198,f161,f128,f204,f88,f83])).

fof(f128,plain,
    ( spl9_8
  <=> r1_tarski(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).

fof(f161,plain,
    ( spl9_15
  <=> ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).

fof(f198,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = sK3(sK0,X0,X1)
        | ~ r1_tarski(sK3(sK0,X0,X1),sK1)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ v2_pre_topc(sK0)
        | ~ r2_hidden(X0,k1_tops_1(sK0,X1)) )
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(resolution,[],[f197,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(sK3(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ r2_hidden(X1,k1_tops_1(X0,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f197,plain,
    ( ! [X7] :
        ( ~ v3_pre_topc(X7,sK0)
        | k1_xboole_0 = X7
        | ~ r1_tarski(X7,sK1) )
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(duplicate_literal_removal,[],[f195])).

fof(f195,plain,
    ( ! [X7] :
        ( ~ r1_tarski(X7,sK1)
        | k1_xboole_0 = X7
        | ~ v3_pre_topc(X7,sK0)
        | ~ r1_tarski(X7,sK1) )
    | ~ spl9_8
    | ~ spl9_15 ),
    inference(resolution,[],[f170,f130])).

fof(f130,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl9_8 ),
    inference(avatar_component_clause,[],[f128])).

fof(f170,plain,
    ( ! [X0,X1] :
        ( ~ r1_tarski(X1,u1_struct_0(sK0))
        | ~ r1_tarski(X0,sK1)
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_tarski(X0,X1) )
    | ~ spl9_15 ),
    inference(resolution,[],[f169,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( r1_tarski(X0,X2)
      | ~ r1_tarski(X1,X2)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

fof(f169,plain,
    ( ! [X2] :
        ( ~ r1_tarski(X2,u1_struct_0(sK0))
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1)
        | k1_xboole_0 = X2 )
    | ~ spl9_15 ),
    inference(resolution,[],[f162,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f162,plain,
    ( ! [X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X2
        | ~ v3_pre_topc(X2,sK0)
        | ~ r1_tarski(X2,sK1) )
    | ~ spl9_15 ),
    inference(avatar_component_clause,[],[f161])).

fof(f163,plain,
    ( spl9_4
    | spl9_15 ),
    inference(avatar_split_clause,[],[f42,f161,f98])).

fof(f42,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X2,sK1)
      | ~ v3_pre_topc(X2,sK0)
      | k1_xboole_0 = X2
      | v2_tops_1(sK1,sK0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f146,plain,
    ( spl9_4
    | ~ spl9_11
    | ~ spl9_2
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f107,f93,f88,f143,f98])).

fof(f107,plain,
    ( ~ l1_pre_topc(sK0)
    | k1_xboole_0 != k1_tops_1(sK0,sK1)
    | v2_tops_1(sK1,sK0)
    | ~ spl9_3 ),
    inference(resolution,[],[f95,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k1_xboole_0 != k1_tops_1(X0,X1)
      | v2_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f131,plain,
    ( spl9_8
    | ~ spl9_3 ),
    inference(avatar_split_clause,[],[f115,f93,f128])).

fof(f115,plain,
    ( r1_tarski(sK1,u1_struct_0(sK0))
    | ~ spl9_3 ),
    inference(resolution,[],[f95,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f10])).

fof(f105,plain,
    ( ~ spl9_4
    | spl9_5 ),
    inference(avatar_split_clause,[],[f39,f102,f98])).

fof(f39,plain,
    ( r1_tarski(sK2,sK1)
    | ~ v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f96,plain,(
    spl9_3 ),
    inference(avatar_split_clause,[],[f43,f93])).

fof(f43,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f91,plain,(
    spl9_2 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f86,plain,(
    spl9_1 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:31:09 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.54  % (30178)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.54  % (30194)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.55  % (30186)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.55  % (30195)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (30199)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.56  % (30179)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.56  % (30183)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.57  % (30187)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.58  % (30191)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.58  % (30176)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.60  % (30189)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.60  % (30197)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.60  % (30181)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.60  % (30174)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.60  % (30173)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.60  % (30194)Refutation found. Thanks to Tanya!
% 0.20/0.60  % SZS status Theorem for theBenchmark
% 0.20/0.60  % SZS output start Proof for theBenchmark
% 0.20/0.60  fof(f525,plain,(
% 0.20/0.60    $false),
% 0.20/0.60    inference(avatar_sat_refutation,[],[f86,f91,f96,f105,f131,f146,f163,f206,f208,f213,f238,f243,f269,f363,f377,f420,f484,f512,f520,f524])).
% 0.20/0.60  fof(f524,plain,(
% 0.20/0.60    spl9_22 | ~spl9_26),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f522])).
% 0.20/0.60  fof(f522,plain,(
% 0.20/0.60    $false | (spl9_22 | ~spl9_26)),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f237,f302,f52])).
% 0.20/0.60  fof(f52,plain,(
% 0.20/0.60    ( ! [X0] : (~r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0) )),
% 0.20/0.60    inference(cnf_transformation,[],[f24])).
% 0.20/0.60  fof(f24,plain,(
% 0.20/0.60    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 0.20/0.60    inference(ennf_transformation,[],[f6])).
% 0.20/0.60  fof(f6,axiom,(
% 0.20/0.60    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).
% 0.20/0.60  fof(f302,plain,(
% 0.20/0.60    r1_tarski(sK2,k1_xboole_0) | ~spl9_26),
% 0.20/0.60    inference(avatar_component_clause,[],[f301])).
% 0.20/0.60  fof(f301,plain,(
% 0.20/0.60    spl9_26 <=> r1_tarski(sK2,k1_xboole_0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_26])])).
% 0.20/0.60  fof(f237,plain,(
% 0.20/0.60    k1_xboole_0 != sK2 | spl9_22),
% 0.20/0.60    inference(avatar_component_clause,[],[f235])).
% 0.20/0.60  fof(f235,plain,(
% 0.20/0.60    spl9_22 <=> k1_xboole_0 = sK2),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_22])])).
% 0.20/0.60  fof(f520,plain,(
% 0.20/0.60    spl9_26 | ~spl9_39),
% 0.20/0.60    inference(avatar_split_clause,[],[f519,f510,f301])).
% 0.20/0.60  fof(f510,plain,(
% 0.20/0.60    spl9_39 <=> ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,sK2))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_39])])).
% 0.20/0.60  fof(f519,plain,(
% 0.20/0.60    r1_tarski(sK2,k1_xboole_0) | ~spl9_39),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f517])).
% 0.20/0.60  fof(f517,plain,(
% 0.20/0.60    r1_tarski(sK2,k1_xboole_0) | r1_tarski(sK2,k1_xboole_0) | ~spl9_39),
% 0.20/0.60    inference(resolution,[],[f513,f64])).
% 0.20/0.60  fof(f64,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r2_hidden(sK4(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f31])).
% 0.20/0.60  fof(f31,plain,(
% 0.20/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.60    inference(ennf_transformation,[],[f1])).
% 0.20/0.60  fof(f1,axiom,(
% 0.20/0.60    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.60  fof(f513,plain,(
% 0.20/0.60    ( ! [X0] : (~r2_hidden(sK4(X0,k1_xboole_0),sK2) | r1_tarski(X0,k1_xboole_0)) ) | ~spl9_39),
% 0.20/0.60    inference(resolution,[],[f511,f65])).
% 0.20/0.60  fof(f65,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r2_hidden(sK4(X0,X1),X1) | r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f31])).
% 0.20/0.60  fof(f511,plain,(
% 0.20/0.60    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,sK2)) ) | ~spl9_39),
% 0.20/0.60    inference(avatar_component_clause,[],[f510])).
% 0.20/0.60  fof(f512,plain,(
% 0.20/0.60    ~spl9_5 | spl9_39 | ~spl9_3 | ~spl9_11 | ~spl9_37),
% 0.20/0.60    inference(avatar_split_clause,[],[f507,f482,f143,f93,f510,f102])).
% 0.20/0.60  fof(f102,plain,(
% 0.20/0.60    spl9_5 <=> r1_tarski(sK2,sK1)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_5])])).
% 0.20/0.60  fof(f93,plain,(
% 0.20/0.60    spl9_3 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_3])])).
% 0.20/0.60  fof(f143,plain,(
% 0.20/0.60    spl9_11 <=> k1_xboole_0 = k1_tops_1(sK0,sK1)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_11])])).
% 0.20/0.60  fof(f482,plain,(
% 0.20/0.60    spl9_37 <=> ! [X1,X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK2,X0))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_37])])).
% 0.20/0.60  fof(f507,plain,(
% 0.20/0.60    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,sK2) | ~r1_tarski(sK2,sK1)) ) | (~spl9_3 | ~spl9_11 | ~spl9_37)),
% 0.20/0.60    inference(forward_demodulation,[],[f502,f144])).
% 0.20/0.60  fof(f144,plain,(
% 0.20/0.60    k1_xboole_0 = k1_tops_1(sK0,sK1) | ~spl9_11),
% 0.20/0.60    inference(avatar_component_clause,[],[f143])).
% 0.20/0.60  fof(f502,plain,(
% 0.20/0.60    ( ! [X3] : (~r2_hidden(X3,sK2) | r2_hidden(X3,k1_tops_1(sK0,sK1)) | ~r1_tarski(sK2,sK1)) ) | (~spl9_3 | ~spl9_37)),
% 0.20/0.60    inference(resolution,[],[f483,f95])).
% 0.20/0.60  fof(f95,plain,(
% 0.20/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_3),
% 0.20/0.60    inference(avatar_component_clause,[],[f93])).
% 0.20/0.60  fof(f483,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0)) | ~r1_tarski(sK2,X0)) ) | ~spl9_37),
% 0.20/0.60    inference(avatar_component_clause,[],[f482])).
% 0.20/0.60  fof(f484,plain,(
% 0.20/0.60    ~spl9_20 | ~spl9_1 | spl9_37 | ~spl9_2 | ~spl9_23),
% 0.20/0.60    inference(avatar_split_clause,[],[f432,f240,f88,f482,f83,f210])).
% 0.20/0.60  fof(f210,plain,(
% 0.20/0.60    spl9_20 <=> v3_pre_topc(sK2,sK0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_20])])).
% 0.20/0.60  fof(f83,plain,(
% 0.20/0.60    spl9_1 <=> v2_pre_topc(sK0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_1])])).
% 0.20/0.60  fof(f88,plain,(
% 0.20/0.60    spl9_2 <=> l1_pre_topc(sK0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_2])])).
% 0.20/0.60  fof(f240,plain,(
% 0.20/0.60    spl9_23 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_23])])).
% 0.20/0.60  fof(f432,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_pre_topc(sK2,sK0) | ~r1_tarski(sK2,X0) | ~r2_hidden(X1,sK2) | r2_hidden(X1,k1_tops_1(sK0,X0))) ) | ~spl9_23),
% 0.20/0.60    inference(resolution,[],[f242,f59])).
% 0.20/0.60  fof(f59,plain,(
% 0.20/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v3_pre_topc(X3,X0) | ~r1_tarski(X3,X2) | ~r2_hidden(X1,X3) | r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f28])).
% 0.20/0.60  fof(f28,plain,(
% 0.20/0.60    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.60    inference(flattening,[],[f27])).
% 0.20/0.60  fof(f27,plain,(
% 0.20/0.60    ! [X0] : (! [X1,X2] : ((r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.60    inference(ennf_transformation,[],[f15])).
% 0.20/0.60  fof(f15,axiom,(
% 0.20/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,k1_tops_1(X0,X2)) <=> ? [X3] : (r2_hidden(X1,X3) & r1_tarski(X3,X2) & v3_pre_topc(X3,X0) & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))))))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_tops_1)).
% 0.20/0.60  fof(f242,plain,(
% 0.20/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl9_23),
% 0.20/0.60    inference(avatar_component_clause,[],[f240])).
% 0.20/0.60  fof(f420,plain,(
% 0.20/0.60    spl9_11 | ~spl9_28),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f418])).
% 0.20/0.60  fof(f418,plain,(
% 0.20/0.60    $false | (spl9_11 | ~spl9_28)),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f145,f376,f52])).
% 0.20/0.60  fof(f376,plain,(
% 0.20/0.60    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | ~spl9_28),
% 0.20/0.60    inference(avatar_component_clause,[],[f374])).
% 0.20/0.60  fof(f374,plain,(
% 0.20/0.60    spl9_28 <=> r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_28])])).
% 0.20/0.60  fof(f145,plain,(
% 0.20/0.60    k1_xboole_0 != k1_tops_1(sK0,sK1) | spl9_11),
% 0.20/0.60    inference(avatar_component_clause,[],[f143])).
% 0.20/0.60  fof(f377,plain,(
% 0.20/0.60    spl9_28 | ~spl9_27),
% 0.20/0.60    inference(avatar_split_clause,[],[f372,f361,f374])).
% 0.20/0.60  fof(f361,plain,(
% 0.20/0.60    spl9_27 <=> ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~r2_hidden(X3,k1_tops_1(sK0,sK1)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_27])])).
% 0.20/0.60  fof(f372,plain,(
% 0.20/0.60    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | ~spl9_27),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f370])).
% 0.20/0.60  fof(f370,plain,(
% 0.20/0.60    r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | r1_tarski(k1_tops_1(sK0,sK1),k1_xboole_0) | ~spl9_27),
% 0.20/0.60    inference(resolution,[],[f365,f65])).
% 0.20/0.60  fof(f365,plain,(
% 0.20/0.60    ( ! [X2] : (r2_hidden(sK4(k1_tops_1(sK0,sK1),X2),k1_xboole_0) | r1_tarski(k1_tops_1(sK0,sK1),X2)) ) | ~spl9_27),
% 0.20/0.60    inference(resolution,[],[f362,f64])).
% 0.20/0.60  fof(f362,plain,(
% 0.20/0.60    ( ! [X3] : (~r2_hidden(X3,k1_tops_1(sK0,sK1)) | r2_hidden(X3,k1_xboole_0)) ) | ~spl9_27),
% 0.20/0.60    inference(avatar_component_clause,[],[f361])).
% 0.20/0.60  fof(f363,plain,(
% 0.20/0.60    ~spl9_1 | ~spl9_3 | ~spl9_2 | spl9_27 | ~spl9_24),
% 0.20/0.60    inference(avatar_split_clause,[],[f321,f267,f361,f88,f93,f83])).
% 0.20/0.60  fof(f267,plain,(
% 0.20/0.60    spl9_24 <=> ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK1)) | k1_xboole_0 = sK3(sK0,X0,sK1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_24])])).
% 0.20/0.60  fof(f321,plain,(
% 0.20/0.60    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r2_hidden(X3,k1_tops_1(sK0,sK1))) ) | ~spl9_24),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f320])).
% 0.20/0.60  fof(f320,plain,(
% 0.20/0.60    ( ! [X3] : (r2_hidden(X3,k1_xboole_0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r2_hidden(X3,k1_tops_1(sK0,sK1)) | ~r2_hidden(X3,k1_tops_1(sK0,sK1))) ) | ~spl9_24),
% 0.20/0.60    inference(superposition,[],[f58,f268])).
% 0.20/0.60  fof(f268,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = sK3(sK0,X0,sK1) | ~r2_hidden(X0,k1_tops_1(sK0,sK1))) ) | ~spl9_24),
% 0.20/0.60    inference(avatar_component_clause,[],[f267])).
% 0.20/0.60  fof(f58,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r2_hidden(X1,sK3(X0,X1,X2)) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f28])).
% 0.20/0.60  fof(f269,plain,(
% 0.20/0.60    ~spl9_1 | ~spl9_2 | ~spl9_3 | spl9_24 | ~spl9_19),
% 0.20/0.60    inference(avatar_split_clause,[],[f265,f204,f267,f93,f88,f83])).
% 0.20/0.60  fof(f204,plain,(
% 0.20/0.60    spl9_19 <=> ! [X1,X0] : (k1_xboole_0 = sK3(sK0,X0,X1) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(sK3(sK0,X0,X1),sK1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_19])])).
% 0.20/0.60  fof(f265,plain,(
% 0.20/0.60    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3(sK0,X0,sK1) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0)) ) | ~spl9_19),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f263])).
% 0.20/0.60  fof(f263,plain,(
% 0.20/0.60    ( ! [X0] : (~r2_hidden(X0,k1_tops_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3(sK0,X0,sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,sK1))) ) | ~spl9_19),
% 0.20/0.60    inference(resolution,[],[f205,f57])).
% 0.20/0.60  fof(f57,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r1_tarski(sK3(X0,X1,X2),X2) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f28])).
% 0.20/0.60  fof(f205,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r1_tarski(sK3(sK0,X0,X1),sK1) | ~r2_hidden(X0,k1_tops_1(sK0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = sK3(sK0,X0,X1)) ) | ~spl9_19),
% 0.20/0.60    inference(avatar_component_clause,[],[f204])).
% 0.20/0.60  fof(f243,plain,(
% 0.20/0.60    ~spl9_4 | spl9_23),
% 0.20/0.60    inference(avatar_split_clause,[],[f38,f240,f98])).
% 0.20/0.60  fof(f98,plain,(
% 0.20/0.60    spl9_4 <=> v2_tops_1(sK1,sK0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_4])])).
% 0.20/0.60  fof(f38,plain,(
% 0.20/0.60    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.60    inference(cnf_transformation,[],[f21])).
% 0.20/0.60  fof(f21,plain,(
% 0.20/0.60    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : (k1_xboole_0 = X2 | ~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.60    inference(flattening,[],[f20])).
% 0.20/0.60  fof(f20,plain,(
% 0.20/0.60    ? [X0] : (? [X1] : ((v2_tops_1(X1,X0) <~> ! [X2] : ((k1_xboole_0 = X2 | (~v3_pre_topc(X2,X0) | ~r1_tarski(X2,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.60    inference(ennf_transformation,[],[f19])).
% 0.20/0.60  fof(f19,negated_conjecture,(
% 0.20/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.60    inference(negated_conjecture,[],[f18])).
% 0.20/0.60  fof(f18,conjecture,(
% 0.20/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_pre_topc(X2,X0) & r1_tarski(X2,X1)) => k1_xboole_0 = X2)))))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tops_1)).
% 0.20/0.60  fof(f238,plain,(
% 0.20/0.60    ~spl9_4 | ~spl9_22),
% 0.20/0.60    inference(avatar_split_clause,[],[f41,f235,f98])).
% 0.20/0.60  fof(f41,plain,(
% 0.20/0.60    k1_xboole_0 != sK2 | ~v2_tops_1(sK1,sK0)),
% 0.20/0.60    inference(cnf_transformation,[],[f21])).
% 0.20/0.60  fof(f213,plain,(
% 0.20/0.60    ~spl9_4 | spl9_20),
% 0.20/0.60    inference(avatar_split_clause,[],[f40,f210,f98])).
% 0.20/0.60  fof(f40,plain,(
% 0.20/0.60    v3_pre_topc(sK2,sK0) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.60    inference(cnf_transformation,[],[f21])).
% 0.20/0.60  fof(f208,plain,(
% 0.20/0.60    ~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_11),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f207])).
% 0.20/0.60  fof(f207,plain,(
% 0.20/0.60    $false | (~spl9_2 | ~spl9_3 | ~spl9_4 | spl9_11)),
% 0.20/0.60    inference(unit_resulting_resolution,[],[f90,f95,f145,f99,f51])).
% 0.20/0.60  fof(f51,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 = k1_tops_1(X0,X1) | ~v2_tops_1(X1,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f23])).
% 0.20/0.60  fof(f23,plain,(
% 0.20/0.60    ! [X0] : (! [X1] : ((v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.60    inference(ennf_transformation,[],[f17])).
% 0.20/0.60  fof(f17,axiom,(
% 0.20/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tops_1(X1,X0) <=> k1_xboole_0 = k1_tops_1(X0,X1))))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tops_1)).
% 0.20/0.60  fof(f99,plain,(
% 0.20/0.60    v2_tops_1(sK1,sK0) | ~spl9_4),
% 0.20/0.60    inference(avatar_component_clause,[],[f98])).
% 0.20/0.60  fof(f90,plain,(
% 0.20/0.60    l1_pre_topc(sK0) | ~spl9_2),
% 0.20/0.60    inference(avatar_component_clause,[],[f88])).
% 0.20/0.60  fof(f206,plain,(
% 0.20/0.60    ~spl9_1 | ~spl9_2 | spl9_19 | ~spl9_8 | ~spl9_15),
% 0.20/0.60    inference(avatar_split_clause,[],[f198,f161,f128,f204,f88,f83])).
% 0.20/0.60  fof(f128,plain,(
% 0.20/0.60    spl9_8 <=> r1_tarski(sK1,u1_struct_0(sK0))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_8])])).
% 0.20/0.60  fof(f161,plain,(
% 0.20/0.60    spl9_15 <=> ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl9_15])])).
% 0.20/0.60  fof(f198,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k1_xboole_0 = sK3(sK0,X0,X1) | ~r1_tarski(sK3(sK0,X0,X1),sK1) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~r2_hidden(X0,k1_tops_1(sK0,X1))) ) | (~spl9_8 | ~spl9_15)),
% 0.20/0.60    inference(resolution,[],[f197,f56])).
% 0.20/0.60  fof(f56,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (v3_pre_topc(sK3(X0,X1,X2),X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~r2_hidden(X1,k1_tops_1(X0,X2))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f28])).
% 0.20/0.60  fof(f197,plain,(
% 0.20/0.60    ( ! [X7] : (~v3_pre_topc(X7,sK0) | k1_xboole_0 = X7 | ~r1_tarski(X7,sK1)) ) | (~spl9_8 | ~spl9_15)),
% 0.20/0.60    inference(duplicate_literal_removal,[],[f195])).
% 0.20/0.60  fof(f195,plain,(
% 0.20/0.60    ( ! [X7] : (~r1_tarski(X7,sK1) | k1_xboole_0 = X7 | ~v3_pre_topc(X7,sK0) | ~r1_tarski(X7,sK1)) ) | (~spl9_8 | ~spl9_15)),
% 0.20/0.60    inference(resolution,[],[f170,f130])).
% 0.20/0.60  fof(f130,plain,(
% 0.20/0.60    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl9_8),
% 0.20/0.60    inference(avatar_component_clause,[],[f128])).
% 0.20/0.60  fof(f170,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r1_tarski(X1,u1_struct_0(sK0)) | ~r1_tarski(X0,sK1) | k1_xboole_0 = X0 | ~v3_pre_topc(X0,sK0) | ~r1_tarski(X0,X1)) ) | ~spl9_15),
% 0.20/0.60    inference(resolution,[],[f169,f71])).
% 0.20/0.60  fof(f71,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f37])).
% 0.20/0.60  fof(f37,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | ~r1_tarski(X1,X2) | ~r1_tarski(X0,X1))),
% 0.20/0.60    inference(flattening,[],[f36])).
% 0.20/0.60  fof(f36,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (r1_tarski(X0,X2) | (~r1_tarski(X1,X2) | ~r1_tarski(X0,X1)))),
% 0.20/0.60    inference(ennf_transformation,[],[f4])).
% 0.20/0.60  fof(f4,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : ((r1_tarski(X1,X2) & r1_tarski(X0,X1)) => r1_tarski(X0,X2))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).
% 0.20/0.60  fof(f169,plain,(
% 0.20/0.60    ( ! [X2] : (~r1_tarski(X2,u1_struct_0(sK0)) | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1) | k1_xboole_0 = X2) ) | ~spl9_15),
% 0.20/0.60    inference(resolution,[],[f162,f66])).
% 0.20/0.60  fof(f66,plain,(
% 0.20/0.60    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f10])).
% 0.20/0.60  fof(f10,axiom,(
% 0.20/0.60    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.60  fof(f162,plain,(
% 0.20/0.60    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = X2 | ~v3_pre_topc(X2,sK0) | ~r1_tarski(X2,sK1)) ) | ~spl9_15),
% 0.20/0.60    inference(avatar_component_clause,[],[f161])).
% 0.20/0.60  fof(f163,plain,(
% 0.20/0.60    spl9_4 | spl9_15),
% 0.20/0.60    inference(avatar_split_clause,[],[f42,f161,f98])).
% 0.20/0.60  fof(f42,plain,(
% 0.20/0.60    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X2,sK1) | ~v3_pre_topc(X2,sK0) | k1_xboole_0 = X2 | v2_tops_1(sK1,sK0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f21])).
% 0.20/0.60  fof(f146,plain,(
% 0.20/0.60    spl9_4 | ~spl9_11 | ~spl9_2 | ~spl9_3),
% 0.20/0.60    inference(avatar_split_clause,[],[f107,f93,f88,f143,f98])).
% 0.20/0.60  fof(f107,plain,(
% 0.20/0.60    ~l1_pre_topc(sK0) | k1_xboole_0 != k1_tops_1(sK0,sK1) | v2_tops_1(sK1,sK0) | ~spl9_3),
% 0.20/0.60    inference(resolution,[],[f95,f50])).
% 0.20/0.60  fof(f50,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k1_xboole_0 != k1_tops_1(X0,X1) | v2_tops_1(X1,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f23])).
% 0.20/0.60  fof(f131,plain,(
% 0.20/0.60    spl9_8 | ~spl9_3),
% 0.20/0.60    inference(avatar_split_clause,[],[f115,f93,f128])).
% 0.20/0.60  fof(f115,plain,(
% 0.20/0.60    r1_tarski(sK1,u1_struct_0(sK0)) | ~spl9_3),
% 0.20/0.60    inference(resolution,[],[f95,f67])).
% 0.20/0.60  fof(f67,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f10])).
% 0.20/0.60  fof(f105,plain,(
% 0.20/0.60    ~spl9_4 | spl9_5),
% 0.20/0.60    inference(avatar_split_clause,[],[f39,f102,f98])).
% 0.20/0.60  fof(f39,plain,(
% 0.20/0.60    r1_tarski(sK2,sK1) | ~v2_tops_1(sK1,sK0)),
% 0.20/0.60    inference(cnf_transformation,[],[f21])).
% 0.20/0.60  fof(f96,plain,(
% 0.20/0.60    spl9_3),
% 0.20/0.60    inference(avatar_split_clause,[],[f43,f93])).
% 0.20/0.60  fof(f43,plain,(
% 0.20/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.60    inference(cnf_transformation,[],[f21])).
% 0.20/0.60  fof(f91,plain,(
% 0.20/0.60    spl9_2),
% 0.20/0.60    inference(avatar_split_clause,[],[f45,f88])).
% 0.20/0.60  fof(f45,plain,(
% 0.20/0.60    l1_pre_topc(sK0)),
% 0.20/0.60    inference(cnf_transformation,[],[f21])).
% 0.20/0.60  fof(f86,plain,(
% 0.20/0.60    spl9_1),
% 0.20/0.60    inference(avatar_split_clause,[],[f44,f83])).
% 0.20/0.60  fof(f44,plain,(
% 0.20/0.60    v2_pre_topc(sK0)),
% 0.20/0.60    inference(cnf_transformation,[],[f21])).
% 0.20/0.60  % SZS output end Proof for theBenchmark
% 0.20/0.60  % (30194)------------------------------
% 0.20/0.60  % (30194)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (30194)Termination reason: Refutation
% 0.20/0.60  
% 0.20/0.60  % (30194)Memory used [KB]: 11001
% 0.20/0.60  % (30194)Time elapsed: 0.154 s
% 0.20/0.60  % (30194)------------------------------
% 0.20/0.60  % (30194)------------------------------
% 0.20/0.60  % (30201)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.60  % (30200)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.60  % (30177)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.61  % (30192)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.89/0.61  % (30185)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.89/0.61  % (30180)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.89/0.62  % (30193)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 1.89/0.62  % (30172)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.89/0.62  % (30184)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.89/0.62  % (30188)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.89/0.62  % (30175)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.89/0.63  % (30171)Success in time 0.259 s
%------------------------------------------------------------------------------
